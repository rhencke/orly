// ── Q3 BSP binary reader ──────────────────────────────────────────
//
// Mirrors the Rocq-side BSP parser (theories/BspFormat.v, BspFace.v,
// BspPlaneVertex.v, etc.) but reads directly from an ArrayBuffer for
// WebGL consumption.  All field names and byte offsets match the Rocq
// definitions so the two parsers stay in sync.
//
// Usage:
//   import { parseBsp } from './bsp.js';
//   const bsp = parseBsp(arrayBuffer, { onDiagnostic });  // throws on invalid input

// ── constants ────────────────────────────────────────────────────────
const BSP_MAGIC   = 0x49425350;  // "IBSP" as stored in the file header
const BSP_VERSION = 46;
const NUM_LUMPS   = 17;

// Lump indices — must match BspFormat.v LumpIndex enumeration
const LUMP_ENTITIES     =  0;
const LUMP_TEXTURES     =  1;
const LUMP_PLANES       =  2;
const LUMP_NODES        =  3;
const LUMP_LEAVES       =  4;
const LUMP_LEAF_FACES   =  5;
const LUMP_LEAF_BRUSHES =  6;
const LUMP_MODELS       =  7;
const LUMP_BRUSHES      =  8;
const LUMP_BRUSH_SIDES  =  9;
const LUMP_VERTEXES     = 10;
const LUMP_MESH_VERTS   = 11;
const LUMP_EFFECTS      = 12;
const LUMP_FACES        = 13;
const LUMP_LIGHTMAPS    = 14;
const LUMP_LIGHT_VOLS   = 15;
const LUMP_VIS_DATA     = 16;

// Entry sizes in bytes — must match Rocq *_size definitions
const TEXTURE_SIZE    = 72;
const PLANE_SIZE      = 16;
const NODE_SIZE       = 36;
const LEAF_SIZE       = 48;
const BRUSH_SIZE      = 12;
const BRUSH_SIDE_SIZE =  8;
const VERTEX_SIZE     = 44;
const FACE_SIZE       = 104;
const EFFECT_SIZE     = 72;
const LIGHTMAP_SIZE   = 49152;  // 128 * 128 * 3
const MODEL_SIZE      = 40;

// ── lump directory ───────────────────────────────────────────────────

function nowMs() {
  if (typeof globalThis.performance?.now === 'function') {
    return globalThis.performance.now();
  }
  return Date.now();
}

function roundDurationMs(durationMs) {
  return Number.isFinite(durationMs)
    ? Math.round(durationMs * 1000) / 1000
    : 0;
}

function emitParseDiagnostic(onDiagnostic, stage, payload = null) {
  if (typeof onDiagnostic !== 'function') return;
  const normalizedPayload =
    typeof payload === 'object' && payload !== null
      ? JSON.parse(JSON.stringify(payload))
      : payload ?? null;
  onDiagnostic({
    stage,
    at: new Date().toISOString(),
    payload: normalizedPayload,
  });
}

function timeParseStep(onDiagnostic, stage, payload, reader, summarizeResult = () => null) {
  const startedAtMs = nowMs();
  emitParseDiagnostic(onDiagnostic, `${stage}:start`, payload);
  try {
    const result = reader();
    emitParseDiagnostic(onDiagnostic, `${stage}:complete`, {
      ...(payload ?? {}),
      durationMs: roundDurationMs(nowMs() - startedAtMs),
      ...(summarizeResult(result) ?? {}),
    });
    return result;
  } catch (error) {
    emitParseDiagnostic(onDiagnostic, `${stage}:failed`, {
      ...(payload ?? {}),
      durationMs: roundDurationMs(nowMs() - startedAtMs),
      error: error instanceof Error ? error.message : String(error),
    });
    throw error;
  }
}

function summarizeLump(entry, entrySize = 0) {
  return {
    offset: Number.isInteger(entry?.offset) ? entry.offset : 0,
    byteLength: Number.isInteger(entry?.length) ? entry.length : 0,
    count: entrySize > 0 ? lumpCount(entry, entrySize) : 0,
  };
}

function readLumpDirectory(view) {
  const dir = new Array(NUM_LUMPS);
  // Directory starts at byte 8 (after magic + version); 8 bytes per entry.
  for (let i = 0; i < NUM_LUMPS; i++) {
    const base = 8 + i * 8;
    dir[i] = {
      offset: view.getInt32(base, true),
      length: view.getInt32(base + 4, true),
    };
  }
  return dir;
}

// ── typed lump readers ───────────────────────────────────────────────

function lumpCount(entry, entrySize) {
  return entrySize > 0 ? Math.floor(entry.length / entrySize) : 0;
}

// Textures (lump 1) — matches BspTexture.v bsp_texture
function readTextures(view, entry) {
  const count = lumpCount(entry, TEXTURE_SIZE);
  const textures = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * TEXTURE_SIZE;
    // 64-byte null-terminated name string
    const nameBytes = new Uint8Array(view.buffer, base, 64);
    const nullIdx = nameBytes.indexOf(0);
    const name = new TextDecoder('ascii').decode(
      nameBytes.subarray(0, nullIdx >= 0 ? nullIdx : 64)
    );
    textures[i] = {
      name,
      flags:    view.getInt32(base + 64, true),
      contents: view.getInt32(base + 68, true),
    };
  }
  return textures;
}

// Planes (lump 2) — matches BspPlaneVertex.v bsp_plane
function readPlanes(view, entry) {
  const count = lumpCount(entry, PLANE_SIZE);
  const planes = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * PLANE_SIZE;
    planes[i] = {
      normalX: view.getFloat32(base,      true),
      normalY: view.getFloat32(base +  4, true),
      normalZ: view.getFloat32(base +  8, true),
      dist:    view.getFloat32(base + 12, true),
    };
  }
  return planes;
}

// Nodes (lump 3) — matches BspNodeLeaf.v bsp_node
function readNodes(view, entry) {
  const count = lumpCount(entry, NODE_SIZE);
  const nodes = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * NODE_SIZE;
    nodes[i] = {
      plane:      view.getInt32(base,      true),
      childFront: view.getInt32(base +  4, true),
      childBack:  view.getInt32(base +  8, true),
      minsX:      view.getInt32(base + 12, true),
      minsY:      view.getInt32(base + 16, true),
      minsZ:      view.getInt32(base + 20, true),
      maxsX:      view.getInt32(base + 24, true),
      maxsY:      view.getInt32(base + 28, true),
      maxsZ:      view.getInt32(base + 32, true),
    };
  }
  return nodes;
}

// Leaves (lump 4) — matches BspNodeLeaf.v bsp_leaf
function readLeaves(view, entry) {
  const count = lumpCount(entry, LEAF_SIZE);
  const leaves = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * LEAF_SIZE;
    leaves[i] = {
      cluster:         view.getInt32(base,      true),
      area:            view.getInt32(base +  4, true),
      minsX:           view.getInt32(base +  8, true),
      minsY:           view.getInt32(base + 12, true),
      minsZ:           view.getInt32(base + 16, true),
      maxsX:           view.getInt32(base + 20, true),
      maxsY:           view.getInt32(base + 24, true),
      maxsZ:           view.getInt32(base + 28, true),
      firstLeafFace:   view.getInt32(base + 32, true),
      numLeafFaces:    view.getInt32(base + 36, true),
      firstLeafBrush:  view.getInt32(base + 40, true),
      numLeafBrushes:  view.getInt32(base + 44, true),
    };
  }
  return leaves;
}

// Leaf-faces (lump 5) and leaf-brushes (lump 6) — i32 index arrays
function readI32Lump(view, entry) {
  const count = lumpCount(entry, 4);
  const arr = new Int32Array(count);
  for (let i = 0; i < count; i++) {
    arr[i] = view.getInt32(entry.offset + i * 4, true);
  }
  return arr;
}

// Models (lump 7) — matches BspBrush.v bsp_model
function readModels(view, entry) {
  const count = lumpCount(entry, MODEL_SIZE);
  const models = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * MODEL_SIZE;
    models[i] = {
      minsX:     view.getFloat32(base,      true),
      minsY:     view.getFloat32(base +  4, true),
      minsZ:     view.getFloat32(base +  8, true),
      maxsX:     view.getFloat32(base + 12, true),
      maxsY:     view.getFloat32(base + 16, true),
      maxsZ:     view.getFloat32(base + 20, true),
      firstFace: view.getInt32(base + 24, true),
      numFaces:  view.getInt32(base + 28, true),
      firstBrush: view.getInt32(base + 32, true),
      numBrushes: view.getInt32(base + 36, true),
    };
  }
  return models;
}

// Brushes (lump 8) — matches BspBrush.v bsp_brush
function readBrushes(view, entry) {
  const count = lumpCount(entry, BRUSH_SIZE);
  const brushes = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * BRUSH_SIZE;
    brushes[i] = {
      firstSide:    view.getInt32(base,     true),
      numSides:     view.getInt32(base + 4, true),
      textureIndex: view.getInt32(base + 8, true),
    };
  }
  return brushes;
}

// Brush sides (lump 9) — matches BspBrush.v bsp_brush_side
function readBrushSides(view, entry) {
  const count = lumpCount(entry, BRUSH_SIDE_SIZE);
  const sides = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * BRUSH_SIDE_SIZE;
    sides[i] = {
      planeIndex:   view.getInt32(base,     true),
      textureIndex: view.getInt32(base + 4, true),
    };
  }
  return sides;
}

// Vertices (lump 10) — matches BspPlaneVertex.v bsp_vertex
function readVertices(view, entry) {
  const count = lumpCount(entry, VERTEX_SIZE);
  const vertices = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * VERTEX_SIZE;
    vertices[i] = {
      posX:    view.getFloat32(base,      true),
      posY:    view.getFloat32(base +  4, true),
      posZ:    view.getFloat32(base +  8, true),
      texS:    view.getFloat32(base + 12, true),
      texT:    view.getFloat32(base + 16, true),
      lmS:     view.getFloat32(base + 20, true),
      lmT:     view.getFloat32(base + 24, true),
      normalX: view.getFloat32(base + 28, true),
      normalY: view.getFloat32(base + 32, true),
      normalZ: view.getFloat32(base + 36, true),
      colorR:  view.getUint8(base + 40),
      colorG:  view.getUint8(base + 41),
      colorB:  view.getUint8(base + 42),
      colorA:  view.getUint8(base + 43),
    };
  }
  return vertices;
}

// Mesh verts (lump 11) — i32 offset indices
// (reuses readI32Lump)

// Effects (lump 12) — matches BspLightmapVisEffect.v bsp_effect
function readEffects(view, entry) {
  const count = lumpCount(entry, EFFECT_SIZE);
  const effects = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * EFFECT_SIZE;
    const nameBytes = new Uint8Array(view.buffer, base, 64);
    const nullIdx = nameBytes.indexOf(0);
    const name = new TextDecoder('ascii').decode(
      nameBytes.subarray(0, nullIdx >= 0 ? nullIdx : 64)
    );
    effects[i] = {
      name,
      brushIndex: view.getInt32(base + 64, true),
      unknown:    view.getInt32(base + 68, true),
    };
  }
  return effects;
}

// Faces (lump 13) — matches BspFace.v bsp_face
function readFaces(view, entry) {
  const count = lumpCount(entry, FACE_SIZE);
  const faces = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * FACE_SIZE;
    faces[i] = {
      texture:     view.getInt32(base,       true),
      effect:      view.getInt32(base +   4, true),
      type:        view.getInt32(base +   8, true),
      vertex:      view.getInt32(base +  12, true),
      nVertexes:   view.getInt32(base +  16, true),
      meshvert:    view.getInt32(base +  20, true),
      nMeshverts:  view.getInt32(base +  24, true),
      lmIndex:     view.getInt32(base +  28, true),
      lmStartX:    view.getInt32(base +  32, true),
      lmStartY:    view.getInt32(base +  36, true),
      lmSizeX:     view.getInt32(base +  40, true),
      lmSizeY:     view.getInt32(base +  44, true),
      lmOriginX:   view.getFloat32(base + 48, true),
      lmOriginY:   view.getFloat32(base + 52, true),
      lmOriginZ:   view.getFloat32(base + 56, true),
      lmVecsSX:    view.getFloat32(base + 60, true),
      lmVecsSY:    view.getFloat32(base + 64, true),
      lmVecsSZ:    view.getFloat32(base + 68, true),
      lmVecsTX:    view.getFloat32(base + 72, true),
      lmVecsTY:    view.getFloat32(base + 76, true),
      lmVecsTZ:    view.getFloat32(base + 80, true),
      normalX:     view.getFloat32(base + 84, true),
      normalY:     view.getFloat32(base + 88, true),
      normalZ:     view.getFloat32(base + 92, true),
      sizeX:       view.getInt32(base +  96, true),
      sizeY:       view.getInt32(base + 100, true),
    };
  }
  return faces;
}

// Lightmaps (lump 14) — matches BspLightmapVisEffect.v bsp_lightmap
// Each lightmap is 128x128 RGB (49152 bytes).
function readLightmaps(view, entry) {
  const count = lumpCount(entry, LIGHTMAP_SIZE);
  const lightmaps = new Array(count);
  for (let i = 0; i < count; i++) {
    const base = entry.offset + i * LIGHTMAP_SIZE;
    lightmaps[i] = new Uint8Array(view.buffer, base, LIGHTMAP_SIZE);
  }
  return lightmaps;
}

// Vis data (lump 16) — matches BspLightmapVisEffect.v bsp_vis_data
function readVisData(view, entry) {
  if (entry.length < 8) return null;
  const numClusters = view.getInt32(entry.offset, true);
  const bytesPerCluster = view.getInt32(entry.offset + 4, true);
  const vecs = new Uint8Array(view.buffer, entry.offset + 8, entry.length - 8);
  return { numClusters, bytesPerCluster, vecs };
}

// Entities (lump 0) — matches BspEntity.v (raw text, parsed separately)
function readEntities(view, entry) {
  if (entry.length === 0) return '';
  const bytes = new Uint8Array(view.buffer, entry.offset, entry.length);
  // Strip trailing null byte(s)
  let end = bytes.length;
  while (end > 0 && bytes[end - 1] === 0) end--;
  return new TextDecoder('ascii').decode(bytes.subarray(0, end));
}

// ── entity string parser ─────────────────────────────────────────────
//
// Q3 entity strings are a sequence of { key "value" ... } blocks.
// Returns an array of Map<string, string> objects.

function parseEntities(entityString) {
  const entities = [];
  let current = null;
  // Tokenize: braces and quoted strings
  const re = /[{}]|"([^"]*)"/g;
  let m;
  const tokens = [];
  while ((m = re.exec(entityString)) !== null) {
    if (m[0] === '{' || m[0] === '}') {
      tokens.push({ type: m[0] });
    } else {
      tokens.push({ type: 'string', value: m[1] });
    }
  }
  let i = 0;
  while (i < tokens.length) {
    const tok = tokens[i];
    if (tok.type === '{') {
      current = new Map();
      i++;
    } else if (tok.type === '}') {
      if (current) entities.push(current);
      current = null;
      i++;
    } else if (tok.type === 'string' && current) {
      const key = tok.value;
      i++;
      if (i < tokens.length && tokens[i].type === 'string') {
        current.set(key, tokens[i].value);
        i++;
      }
    } else {
      i++;
    }
  }
  return entities;
}

// ── face type constants ──────────────────────────────────────────────
// Matches BspFace.v fc_type field values.
export const FACE_POLYGON  = 1;
export const FACE_PATCH    = 2;
export const FACE_MESH     = 3;
export const FACE_BILLBOARD = 4;

// ── surface visibility ──────────────────────────────────────────────
//
// Q3 content/surface flags that mark non-renderable geometry.  Shared
// by the polygon/mesh renderer and the bezier patch tessellator so
// filtering logic lives in one place.

const CONTENTS_PLAYERCLIP  = 0x10000;
const CONTENTS_MONSTERCLIP = 0x20000;
const SURF_NODRAW = 0x80;
const SURF_SKY    = 0x4;

/**
 * Returns true if the given BSP texture entry represents a visible,
 * drawable surface (not a clip brush, sky, nodraw, etc.).
 */
export function isVisibleTexture(tex) {
  if (!tex) return false;
  if (tex.name === '' || tex.name === 'noshader') return false;
  if (tex.flags & (SURF_NODRAW | SURF_SKY)) return false;
  if (tex.contents & (CONTENTS_PLAYERCLIP | CONTENTS_MONSTERCLIP)) return false;
  return true;
}

// ── top-level parser ─────────────────────────────────────────────────

/**
 * Parse a Q3 BSP file from an ArrayBuffer.
 *
 * Returns a structured object mirroring the Rocq-side bsp_file record
 * (theories/BspFile.v).  Throws on invalid magic or version.
 *
 * @param {ArrayBuffer} buffer
 * @param {{ onDiagnostic?: Function }} options
 * @returns {object} Parsed BSP data
 */
export function parseBsp(buffer, options = {}) {
  const onDiagnostic =
    typeof options?.onDiagnostic === 'function' ? options.onDiagnostic : null;
  const parseStartedAtMs = nowMs();
  emitParseDiagnostic(onDiagnostic, 'parse:start', {
    byteLength: buffer?.byteLength ?? 0,
  });

  if (buffer.byteLength < 8 + NUM_LUMPS * 8) {
    throw new Error(`BSP too short: ${buffer.byteLength} bytes (need at least ${8 + NUM_LUMPS * 8})`);
  }

  try {
    const view = new DataView(buffer);

    const { magic, version } = timeParseStep(
      onDiagnostic,
      'header',
      { byteLength: 8 + NUM_LUMPS * 8 },
      () => {
        // Validate header — matches BspFormat.v parse_bsp_header
        const magic = view.getUint32(0, false);
        const version = view.getInt32(4, true);
        if (magic !== BSP_MAGIC) {
          throw new Error(`Bad BSP magic: 0x${magic.toString(16)} (expected 0x${BSP_MAGIC.toString(16)})`);
        }
        if (version !== BSP_VERSION) {
          throw new Error(`Bad BSP version: ${version} (expected ${BSP_VERSION})`);
        }
        return { magic, version };
      },
      ({ magic, version }) => ({
        magic: `0x${magic.toString(16)}`,
        version,
      })
    );

    const dir = timeParseStep(
      onDiagnostic,
      'directory',
      { entryCount: NUM_LUMPS },
      () => readLumpDirectory(view),
      directory => ({
        totalByteLength: directory.reduce((total, entry) => total + Math.max(0, entry?.length ?? 0), 0),
      })
    );

    const entityString = timeParseStep(
      onDiagnostic,
      'lump:entities:text',
      summarizeLump(dir[LUMP_ENTITIES]),
      () => readEntities(view, dir[LUMP_ENTITIES]),
      value => ({
        charCount: typeof value === 'string' ? value.length : 0,
      })
    );

    const entities = timeParseStep(
      onDiagnostic,
      'lump:entities:parse',
      {
        charCount: typeof entityString === 'string' ? entityString.length : 0,
      },
      () => parseEntities(entityString),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );

    const textures = timeParseStep(
      onDiagnostic,
      'lump:textures',
      summarizeLump(dir[LUMP_TEXTURES], TEXTURE_SIZE),
      () => readTextures(view, dir[LUMP_TEXTURES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const planes = timeParseStep(
      onDiagnostic,
      'lump:planes',
      summarizeLump(dir[LUMP_PLANES], PLANE_SIZE),
      () => readPlanes(view, dir[LUMP_PLANES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const nodes = timeParseStep(
      onDiagnostic,
      'lump:nodes',
      summarizeLump(dir[LUMP_NODES], NODE_SIZE),
      () => readNodes(view, dir[LUMP_NODES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const leaves = timeParseStep(
      onDiagnostic,
      'lump:leaves',
      summarizeLump(dir[LUMP_LEAVES], LEAF_SIZE),
      () => readLeaves(view, dir[LUMP_LEAVES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const leafFaces = timeParseStep(
      onDiagnostic,
      'lump:leaf-faces',
      summarizeLump(dir[LUMP_LEAF_FACES], 4),
      () => readI32Lump(view, dir[LUMP_LEAF_FACES]),
      value => ({
        count: value?.length ?? 0,
      })
    );
    const leafBrushes = timeParseStep(
      onDiagnostic,
      'lump:leaf-brushes',
      summarizeLump(dir[LUMP_LEAF_BRUSHES], 4),
      () => readI32Lump(view, dir[LUMP_LEAF_BRUSHES]),
      value => ({
        count: value?.length ?? 0,
      })
    );
    const models = timeParseStep(
      onDiagnostic,
      'lump:models',
      summarizeLump(dir[LUMP_MODELS], MODEL_SIZE),
      () => readModels(view, dir[LUMP_MODELS]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const brushes = timeParseStep(
      onDiagnostic,
      'lump:brushes',
      summarizeLump(dir[LUMP_BRUSHES], BRUSH_SIZE),
      () => readBrushes(view, dir[LUMP_BRUSHES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const brushSides = timeParseStep(
      onDiagnostic,
      'lump:brush-sides',
      summarizeLump(dir[LUMP_BRUSH_SIDES], BRUSH_SIDE_SIZE),
      () => readBrushSides(view, dir[LUMP_BRUSH_SIDES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const vertices = timeParseStep(
      onDiagnostic,
      'lump:vertices',
      summarizeLump(dir[LUMP_VERTEXES], VERTEX_SIZE),
      () => readVertices(view, dir[LUMP_VERTEXES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const meshVerts = timeParseStep(
      onDiagnostic,
      'lump:mesh-verts',
      summarizeLump(dir[LUMP_MESH_VERTS], 4),
      () => readI32Lump(view, dir[LUMP_MESH_VERTS]),
      value => ({
        count: value?.length ?? 0,
      })
    );
    const effects = timeParseStep(
      onDiagnostic,
      'lump:effects',
      summarizeLump(dir[LUMP_EFFECTS], EFFECT_SIZE),
      () => readEffects(view, dir[LUMP_EFFECTS]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const faces = timeParseStep(
      onDiagnostic,
      'lump:faces',
      summarizeLump(dir[LUMP_FACES], FACE_SIZE),
      () => readFaces(view, dir[LUMP_FACES]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const lightmaps = timeParseStep(
      onDiagnostic,
      'lump:lightmaps',
      summarizeLump(dir[LUMP_LIGHTMAPS], LIGHTMAP_SIZE),
      () => readLightmaps(view, dir[LUMP_LIGHTMAPS]),
      value => ({
        count: Array.isArray(value) ? value.length : 0,
      })
    );
    const visData = timeParseStep(
      onDiagnostic,
      'lump:vis-data',
      summarizeLump(dir[LUMP_VIS_DATA]),
      () => readVisData(view, dir[LUMP_VIS_DATA]),
      value => ({
        clusterCount: Number.isInteger(value?.numClusters) ? value.numClusters : 0,
        bytesPerCluster: Number.isInteger(value?.bytesPerCluster) ? value.bytesPerCluster : 0,
      })
    );

    const bsp = {
      magic,
      version,
      directory: dir,
      entities,
      entityString,
      textures,
      planes,
      nodes,
      leaves,
      leafFaces,
      leafBrushes,
      models,
      brushes,
      brushSides,
      vertices,
      meshVerts,
      effects,
      faces,
      lightmaps,
      visData,
    };

    emitParseDiagnostic(onDiagnostic, 'parse:complete', {
      byteLength: buffer.byteLength,
      durationMs: roundDurationMs(nowMs() - parseStartedAtMs),
      entityCount: bsp.entities.length,
      textureCount: bsp.textures.length,
      planeCount: bsp.planes.length,
      nodeCount: bsp.nodes.length,
      leafCount: bsp.leaves.length,
      modelCount: bsp.models.length,
      brushCount: bsp.brushes.length,
      brushSideCount: bsp.brushSides.length,
      vertexCount: bsp.vertices.length,
      meshVertCount: bsp.meshVerts.length,
      effectCount: bsp.effects.length,
      faceCount: bsp.faces.length,
      lightmapCount: bsp.lightmaps.length,
      visClusterCount: Number.isInteger(bsp.visData?.numClusters) ? bsp.visData.numClusters : 0,
    });

    return bsp;
  } catch (error) {
    emitParseDiagnostic(onDiagnostic, 'parse:failed', {
      byteLength: buffer.byteLength,
      durationMs: roundDurationMs(nowMs() - parseStartedAtMs),
      error: error instanceof Error ? error.message : String(error),
    });
    throw error;
  }
}
