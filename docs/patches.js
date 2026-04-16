// ── Bezier patch tessellation for Q3 BSP type-2 faces ────────────
//
// SUPERSEDED: the authoritative tessellation logic now lives in Rocq
// (theories/BspPatch.v) with proofs.  This JS file remains as a
// temporary fallback until the JS-to-Rocq bridge is wired up,
// at which point JS will consume pre-tessellated meshes from Rocq.
//
// Q3 BSP patch faces store a grid of control points for bi-quadratic
// Bezier surfaces (3x3 control points per sub-patch).  This module
// tessellates them into triangle meshes that slot into the renderer's
// existing lightmap-grouped draw pipeline.
//
// Usage:
//   import { tessellatePatches } from './patches.js';
//   const { vertices, groupMap } = tessellatePatches(bsp);

import { FACE_PATCH, isVisibleTexture } from './bsp.js';

// ── config ──────────────────────────────────────────────────────────

// Subdivisions per patch edge.  Higher = smoother curves, more
// triangles.  8 matches Q3's default r_subdivisions and gives a
// good balance between visual quality and vertex count for q3dm1.
const TESS_LEVEL = 8;

// ── bi-quadratic Bezier evaluation ──────────────────────────────────
//
// Quadratic Bernstein basis:
//   B0(t) = (1-t)^2    B1(t) = 2t(1-t)    B2(t) = t^2
//
// Surface point at (s,t):
//   P(s,t) = sum_ij  Bi(s) * Bj(t) * C[j][i]
//
// All vertex attributes (position, texture coords, lightmap coords,
// color, normal) are interpolated through the same basis so the
// tessellated mesh carries correct data for rendering.

const FLOAT_ATTRS = [
  'posX','posY','posZ',
  'texS','texT',
  'lmS','lmT',
  'normalX','normalY','normalZ',
];
const COLOR_ATTRS = ['colorR','colorG','colorB','colorA'];

function evalPatch(ctrl, s, t) {
  const s0 = (1 - s) * (1 - s), s1 = 2 * s * (1 - s), s2 = s * s;
  const t0 = (1 - t) * (1 - t), t1 = 2 * t * (1 - t), t2 = t * t;
  const weights = [
    s0*t0, s1*t0, s2*t0,
    s0*t1, s1*t1, s2*t1,
    s0*t2, s1*t2, s2*t2,
  ];

  const v = {};
  for (const k of FLOAT_ATTRS) {
    let acc = 0;
    for (let i = 0; i < 9; i++) acc += weights[i] * ctrl[i][k];
    v[k] = acc;
  }
  for (const k of COLOR_ATTRS) {
    let acc = 0;
    for (let i = 0; i < 9; i++) acc += weights[i] * ctrl[i][k];
    v[k] = Math.round(Math.max(0, Math.min(255, acc)));
  }
  return v;
}

// ── tessellate one 3x3 sub-patch ────────────────────────────────────
//
// Generates a (level+1)x(level+1) vertex grid and 2*level*level
// triangles.  Indices are 0-based (relative to this sub-patch).

function tessellateSingle(ctrl, level) {
  const step = 1 / level;
  const vertices = [];

  for (let row = 0; row <= level; row++) {
    const t = row * step;
    for (let col = 0; col <= level; col++) {
      vertices.push(evalPatch(ctrl, col * step, t));
    }
  }

  // Two triangles per grid cell, CW winding to match Q3 convention
  const indices = [];
  const w = level + 1;
  for (let row = 0; row < level; row++) {
    for (let col = 0; col < level; col++) {
      const tl = row * w + col;
      const tr = tl + 1;
      const bl = tl + w;
      const br = bl + 1;
      indices.push(tl, bl, tr, tr, bl, br);
    }
  }

  return { vertices, indices };
}

// ── tessellate all patch faces ──────────────────────────────────────
//
// Processes every FACE_PATCH in the BSP.  Each patch face contains a
// grid of sizeX * sizeY control points, decomposed into
// ((sizeX-1)/2) * ((sizeY-1)/2) individual 3x3 sub-patches.
//
// Returns:
//   vertices  — array of vertex objects (same shape as BSP vertices)
//   groupMap  — Map<lmIndex, number[]> of indices into the combined
//               vertex array (BSP vertices + these patch vertices),
//               ready to merge into the renderer's lightmap groups.
//
// The caller must pass vertexBase = bsp.vertices.length so that
// returned indices are offset correctly for the combined buffer.

export function tessellatePatches(bsp, level = TESS_LEVEL) {
  const vertexBase = bsp.vertices.length;
  const vertices = [];
  const groupMap = new Map();

  for (const face of bsp.faces) {
    if (face.type !== FACE_PATCH) continue;
    if (face.nVertexes === 0) continue;
    if (!isVisibleTexture(bsp.textures[face.texture])) continue;

    const gw = face.sizeX;
    const gh = face.sizeY;
    // Valid patch grids are odd dimensions >= 3
    if (gw < 3 || gh < 3 || gw % 2 === 0 || gh % 2 === 0) continue;

    const numPatchesX = (gw - 1) / 2;
    const numPatchesY = (gh - 1) / 2;

    const lmIdx = face.lmIndex;
    if (!groupMap.has(lmIdx)) groupMap.set(lmIdx, []);
    const groupIndices = groupMap.get(lmIdx);

    for (let py = 0; py < numPatchesY; py++) {
      for (let px = 0; px < numPatchesX; px++) {
        // Extract the 3x3 control points for this sub-patch
        const ctrl = [];
        for (let row = 0; row < 3; row++) {
          for (let col = 0; col < 3; col++) {
            ctrl.push(bsp.vertices[face.vertex + (py * 2 + row) * gw + (px * 2 + col)]);
          }
        }

        const base = vertexBase + vertices.length;
        const patch = tessellateSingle(ctrl, level);

        for (const v of patch.vertices) vertices.push(v);
        for (const idx of patch.indices) groupIndices.push(base + idx);
      }
    }
  }

  return { vertices, groupMap };
}
