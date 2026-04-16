// ── WebGL renderer for Q3 BSP face geometry with lightmaps ───────
//
// Consumes the parsed BSP data from bsp.js and draws polygon (type 1),
// bezier patch (type 2), and mesh (type 3) faces with lightmap-
// modulated vertex colors.  Patches are tessellated at load time by
// patches.js and merged into the same vertex/index buffers.
//
// Usage:
//   import { createRenderer } from './renderer.js';
//   const renderer = createRenderer(canvas, bsp);
//   renderer.render(viewMatrix, projMatrix);
//   renderer.destroy();
//
// Coordinate system: Q3 is right-handed Z-up. We pass vertices
// through unmodified — the view matrix handles the conversion.

import { FACE_POLYGON, FACE_MESH, isVisibleTexture } from './bsp.js';
import { tessellatePatches } from './patches.js';

// ── shader sources ───────────────────────────────────────────────────

const VERT_SRC = `
  attribute vec3 a_position;
  attribute vec2 a_lmCoord;
  attribute vec2 a_texCoord;
  attribute vec4 a_color;

  uniform mat4 u_view;
  uniform mat4 u_proj;

  varying vec2 v_lmCoord;
  varying vec4 v_color;

  void main() {
    v_lmCoord = a_lmCoord;
    v_color   = a_color;
    gl_Position = u_proj * u_view * vec4(a_position, 1.0);
  }
`;

const FRAG_SRC = `
  precision mediump float;

  uniform sampler2D u_lightmap;

  varying vec2 v_lmCoord;
  varying vec4 v_color;

  void main() {
    vec3 lm = texture2D(u_lightmap, v_lmCoord).rgb;
    // Lightmap modulates vertex color; gamma-correct the lightmap
    // from sRGB storage to linear, apply, then back to sRGB would be
    // ideal — but Q3 shipped without gamma correction, so we match
    // that look for now.  Brighten slightly (×2) because Q3 lightmaps
    // are authored for the engine's built-in over-brightening.
    vec3 color = v_color.rgb * lm * 2.0;
    gl_FragColor = vec4(color, v_color.a);
  }
`;

// ── GL helpers ───────────────────────────────────────────────────────

function compileShader(gl, type, src) {
  const s = gl.createShader(type);
  gl.shaderSource(s, src);
  gl.compileShader(s);
  if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) {
    const log = gl.getShaderInfoLog(s);
    gl.deleteShader(s);
    throw new Error(`Shader compile failed: ${log}`);
  }
  return s;
}

function linkProgram(gl, vs, fs) {
  const p = gl.createProgram();
  gl.attachShader(p, vs);
  gl.attachShader(p, fs);
  gl.linkProgram(p);
  if (!gl.getProgramParameter(p, gl.LINK_STATUS)) {
    const log = gl.getProgramInfoLog(p);
    gl.deleteProgram(p);
    throw new Error(`Program link failed: ${log}`);
  }
  return p;
}

// ── surface filtering ────────────────────────────────────────────────

function shouldDrawFace(face, textures) {
  if (face.type !== FACE_POLYGON && face.type !== FACE_MESH) return false;
  if (face.nMeshverts === 0) return false;
  return isVisibleTexture(textures[face.texture]);
}

// ── vertex buffer packing ────────────────────────────────────────────
//
// Interleaved layout per vertex (32 bytes):
//   float32 posX, posY, posZ    (bytes  0–11)
//   float32 lmS, lmT            (bytes 12–19)
//   float32 texS, texT          (bytes 20–27, for future diffuse textures)
//   uint8   colorR, G, B, A     (bytes 28–31)

const VERTEX_STRIDE = 32;

function buildVertexBuffer(gl, vertices) {
  const n = vertices.length;
  const buf = new ArrayBuffer(n * VERTEX_STRIDE);
  const f32 = new Float32Array(buf);
  const u8  = new Uint8Array(buf);

  for (let i = 0; i < n; i++) {
    const v = vertices[i];
    const fOff = i * 8; // 32 / 4 = 8 floats per vertex
    f32[fOff + 0] = v.posX;
    f32[fOff + 1] = v.posY;
    f32[fOff + 2] = v.posZ;
    f32[fOff + 3] = v.lmS;
    f32[fOff + 4] = v.lmT;
    f32[fOff + 5] = v.texS;
    f32[fOff + 6] = v.texT;
    const bOff = i * VERTEX_STRIDE + 28;
    u8[bOff + 0] = v.colorR;
    u8[bOff + 1] = v.colorG;
    u8[bOff + 2] = v.colorB;
    u8[bOff + 3] = v.colorA;
  }

  const vbo = gl.createBuffer();
  gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
  gl.bufferData(gl.ARRAY_BUFFER, buf, gl.STATIC_DRAW);
  return vbo;
}

// ── index buffer + draw groups ───────────────────────────────────────
//
// Group faces by lightmap index so we can batch draw calls.
// Returns { ibo, groups: [{ lmIndex, start, count }], indexType, indexSize }.

function buildIndexBuffer(gl, bsp, patchGroupMap, totalVertexCount) {
  const { faces, meshVerts, textures } = bsp;

  // First pass: count total indices and group by lightmap
  const groupMap = new Map(); // lmIndex -> [indices...]
  for (let fi = 0; fi < faces.length; fi++) {
    const face = faces[fi];
    if (!shouldDrawFace(face, textures)) continue;

    const lmIdx = face.lmIndex;
    if (!groupMap.has(lmIdx)) groupMap.set(lmIdx, []);
    const arr = groupMap.get(lmIdx);

    for (let j = 0; j < face.nMeshverts; j++) {
      arr.push(face.vertex + meshVerts[face.meshvert + j]);
    }
  }

  // Merge tessellated bezier patch indices into the same lightmap groups
  for (const [lmIdx, patchIndices] of patchGroupMap) {
    if (!groupMap.has(lmIdx)) groupMap.set(lmIdx, []);
    const arr = groupMap.get(lmIdx);
    for (const idx of patchIndices) arr.push(idx);
  }

  // Flatten groups into a single index array, recording start/count
  let totalIndices = 0;
  for (const arr of groupMap.values()) totalIndices += arr.length;

  // Choose index type based on total vertex count (BSP + tessellated patches)
  const needU32 = totalVertexCount > 65535;
  if (needU32) {
    const ext = gl.getExtension('OES_element_index_uint');
    if (!ext) throw new Error('OES_element_index_uint not supported');
  }

  const indexType = needU32 ? gl.UNSIGNED_INT : gl.UNSIGNED_SHORT;
  const indexSize = needU32 ? 4 : 2;
  const indexData = needU32
    ? new Uint32Array(totalIndices)
    : new Uint16Array(totalIndices);

  const groups = [];
  let offset = 0;
  for (const [lmIdx, arr] of groupMap) {
    groups.push({ lmIndex: lmIdx, start: offset, count: arr.length });
    for (let i = 0; i < arr.length; i++) {
      indexData[offset + i] = arr[i];
    }
    offset += arr.length;
  }

  const ibo = gl.createBuffer();
  gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, ibo);
  gl.bufferData(gl.ELEMENT_ARRAY_BUFFER, indexData, gl.STATIC_DRAW);

  return { ibo, groups, indexType, indexSize };
}

// ── lightmap textures ────────────────────────────────────────────────

function uploadLightmaps(gl, bsp) {
  const textures = [];

  for (let i = 0; i < bsp.lightmaps.length; i++) {
    const rgb = bsp.lightmaps[i];
    // WebGL texImage2D with RGB can have alignment issues on some
    // implementations; expand to RGBA for safety.
    const rgba = new Uint8Array(128 * 128 * 4);
    for (let p = 0; p < 128 * 128; p++) {
      rgba[p * 4 + 0] = rgb[p * 3 + 0];
      rgba[p * 4 + 1] = rgb[p * 3 + 1];
      rgba[p * 4 + 2] = rgb[p * 3 + 2];
      rgba[p * 4 + 3] = 255;
    }

    const tex = gl.createTexture();
    gl.bindTexture(gl.TEXTURE_2D, tex);
    gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, 128, 128, 0,
                  gl.RGBA, gl.UNSIGNED_BYTE, rgba);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.LINEAR);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_S, gl.CLAMP_TO_EDGE);
    gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_WRAP_T, gl.CLAMP_TO_EDGE);
    textures.push(tex);
  }

  // Fallback white 1x1 texture for faces without a lightmap (lmIndex === -1)
  const white = gl.createTexture();
  gl.bindTexture(gl.TEXTURE_2D, white);
  gl.texImage2D(gl.TEXTURE_2D, 0, gl.RGBA, 1, 1, 0,
                gl.RGBA, gl.UNSIGNED_BYTE, new Uint8Array([255, 255, 255, 255]));
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MIN_FILTER, gl.NEAREST);
  gl.texParameteri(gl.TEXTURE_2D, gl.TEXTURE_MAG_FILTER, gl.NEAREST);

  return { textures, white };
}

// ── minimal mat4 utilities ───────────────────────────────────────────
//
// Just enough to set up a default projection and identity view.
// The camera module (coming later) will provide its own lookAt.

/** Write a 4x4 identity matrix into `out`. */
export function mat4Identity(out) {
  out.fill(0);
  out[0] = out[5] = out[10] = out[15] = 1;
  return out;
}

/** Symmetric perspective projection (column-major). */
export function mat4Perspective(out, fovY, aspect, near, far) {
  const f = 1.0 / Math.tan(fovY / 2);
  const nf = 1.0 / (near - far);
  out[0]  = f / aspect;
  out[1]  = 0;
  out[2]  = 0;
  out[3]  = 0;
  out[4]  = 0;
  out[5]  = f;
  out[6]  = 0;
  out[7]  = 0;
  out[8]  = 0;
  out[9]  = 0;
  out[10] = (far + near) * nf;
  out[11] = -1;
  out[12] = 0;
  out[13] = 0;
  out[14] = 2 * far * near * nf;
  out[15] = 0;
  return out;
}

/**
 * Build a view matrix from eye, center, and up vectors (column-major).
 * Works correctly with Q3's Z-up coordinate system when up = [0,0,1].
 */
export function mat4LookAt(out, eye, center, up) {
  let fx = center[0] - eye[0];
  let fy = center[1] - eye[1];
  let fz = center[2] - eye[2];
  let len = Math.hypot(fx, fy, fz);
  if (len > 0) { fx /= len; fy /= len; fz /= len; }

  // side = forward × up
  let sx = fy * up[2] - fz * up[1];
  let sy = fz * up[0] - fx * up[2];
  let sz = fx * up[1] - fy * up[0];
  len = Math.hypot(sx, sy, sz);
  if (len > 0) { sx /= len; sy /= len; sz /= len; }

  // recomputed up = side × forward
  const ux = sy * fz - sz * fy;
  const uy = sz * fx - sx * fz;
  const uz = sx * fy - sy * fx;

  out[0]  = sx;
  out[1]  = ux;
  out[2]  = -fx;
  out[3]  = 0;
  out[4]  = sy;
  out[5]  = uy;
  out[6]  = -fy;
  out[7]  = 0;
  out[8]  = sz;
  out[9]  = uz;
  out[10] = -fz;
  out[11] = 0;
  out[12] = -(sx * eye[0] + sy * eye[1] + sz * eye[2]);
  out[13] = -(ux * eye[0] + uy * eye[1] + uz * eye[2]);
  out[14] =  (fx * eye[0] + fy * eye[1] + fz * eye[2]);
  out[15] = 1;
  return out;
}

// ── renderer factory ─────────────────────────────────────────────────

/**
 * Create a WebGL renderer for Q3 BSP face geometry.
 *
 * @param {HTMLCanvasElement} canvas — the target canvas
 * @param {object} bsp — parsed BSP data from parseBsp()
 * @returns {{ render(view: Float32Array, proj: Float32Array): void, destroy(): void }}
 */
export function createRenderer(canvas, bsp) {
  const gl = canvas.getContext('webgl', { antialias: false, alpha: false });
  if (!gl) throw new Error('WebGL not available');

  // ── compile shaders ──────────────────────────────────────────────
  const vs = compileShader(gl, gl.VERTEX_SHADER, VERT_SRC);
  const fs = compileShader(gl, gl.FRAGMENT_SHADER, FRAG_SRC);
  const program = linkProgram(gl, vs, fs);
  gl.deleteShader(vs);
  gl.deleteShader(fs);

  // ── attribute / uniform locations ────────────────────────────────
  const aPosition = gl.getAttribLocation(program, 'a_position');
  const aLmCoord  = gl.getAttribLocation(program, 'a_lmCoord');
  const aTexCoord = gl.getAttribLocation(program, 'a_texCoord');
  const aColor    = gl.getAttribLocation(program, 'a_color');
  const uView     = gl.getUniformLocation(program, 'u_view');
  const uProj     = gl.getUniformLocation(program, 'u_proj');
  const uLightmap = gl.getUniformLocation(program, 'u_lightmap');

  // ── tessellate bezier patches ───────────────────────────────────
  const patches = tessellatePatches(bsp);
  const allVertices = bsp.vertices.concat(patches.vertices);

  // ── build GPU buffers ────────────────────────────────────────────
  const vbo = buildVertexBuffer(gl, allVertices);
  const { ibo, groups, indexType, indexSize } =
    buildIndexBuffer(gl, bsp, patches.groupMap, allVertices.length);
  const lm = uploadLightmaps(gl, bsp);

  // ── GL state ─────────────────────────────────────────────────────
  gl.clearColor(0.05, 0.05, 0.05, 1.0);
  gl.enable(gl.DEPTH_TEST);
  gl.enable(gl.CULL_FACE);
  // Q3 BSP meshverts produce clockwise front-facing triangles
  gl.frontFace(gl.CW);

  // ── render function ──────────────────────────────────────────────
  function render(viewMatrix, projMatrix) {
    gl.viewport(0, 0, canvas.width, canvas.height);
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
    gl.useProgram(program);

    // Matrices
    gl.uniformMatrix4fv(uView, false, viewMatrix);
    gl.uniformMatrix4fv(uProj, false, projMatrix);

    // Bind VBO and set attribute pointers
    gl.bindBuffer(gl.ARRAY_BUFFER, vbo);
    gl.enableVertexAttribArray(aPosition);
    gl.vertexAttribPointer(aPosition, 3, gl.FLOAT, false, VERTEX_STRIDE, 0);
    gl.enableVertexAttribArray(aLmCoord);
    gl.vertexAttribPointer(aLmCoord, 2, gl.FLOAT, false, VERTEX_STRIDE, 12);
    if (aTexCoord >= 0) {
      gl.enableVertexAttribArray(aTexCoord);
      gl.vertexAttribPointer(aTexCoord, 2, gl.FLOAT, false, VERTEX_STRIDE, 20);
    }
    gl.enableVertexAttribArray(aColor);
    gl.vertexAttribPointer(aColor, 4, gl.UNSIGNED_BYTE, true, VERTEX_STRIDE, 28);

    // Lightmap sampler
    gl.activeTexture(gl.TEXTURE0);
    gl.uniform1i(uLightmap, 0);

    // Bind IBO
    gl.bindBuffer(gl.ELEMENT_ARRAY_BUFFER, ibo);

    // Draw each lightmap group
    for (const g of groups) {
      const tex = (g.lmIndex >= 0 && g.lmIndex < lm.textures.length)
        ? lm.textures[g.lmIndex]
        : lm.white;
      gl.bindTexture(gl.TEXTURE_2D, tex);
      gl.drawElements(gl.TRIANGLES, g.count, indexType, g.start * indexSize);
    }
  }

  // ── cleanup ──────────────────────────────────────────────────────
  function destroy() {
    gl.deleteProgram(program);
    gl.deleteBuffer(vbo);
    gl.deleteBuffer(ibo);
    for (const t of lm.textures) gl.deleteTexture(t);
    gl.deleteTexture(lm.white);
  }

  return { render, destroy, gl };
}
