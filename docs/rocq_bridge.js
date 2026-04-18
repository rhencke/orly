import { mat4LookAt } from './renderer.js';

const DEG_TO_RAD = Math.PI / 180;
const BRIDGE_VERSION = 1;
const BRIDGE_HELPERS_DEFINITION = 'Definition step_world_words_in_world';
const CAMERA_WORDS_COUNT = 10;
const MIN_GAME_STATE_WORDS_COUNT = 19;
const GEOMETRY_Q_SCALE = 1000000;
const CONTENTS_SOLID = 1;
const CONTENTS_PLAYERCLIP = 65536;
const SENTENCE_PHASE_PROCESSED = 'processed';
const SENTENCE_PHASE_ERROR = 'error';
const SENTENCE_PHASE_CANCELLING = 'cancelling';

function nextTick() {
  return new Promise(resolve => setTimeout(resolve, 0));
}

function encodeAsciiBytes(str) {
  const bytes = [];
  for (let i = 0; i < str.length; i++) {
    bytes.push(str.charCodeAt(i) & 0xff);
  }
  return bytes;
}

function formatZList(values) {
  return `[${values.join('; ')}]`;
}

function formatQ(value, scale = GEOMETRY_Q_SCALE) {
  const numerator = Math.round(value * scale);
  return `(${numerator} # ${scale})`;
}

function formatEntity(entity) {
  const kvs = [];
  for (const [key, value] of entity.entries()) {
    kvs.push(`(${formatZList(encodeAsciiBytes(key))}, ${formatZList(encodeAsciiBytes(value))})`);
  }
  return `[${kvs.join('; ')}]`;
}

function formatEntities(entities) {
  return `[${entities.map(formatEntity).join('; ')}]`;
}

function formatTexture(texture) {
  return `(mk_render_texture_input ${formatZList(encodeAsciiBytes(texture.name))} ` +
    `${texture.flags} ${texture.contents})`;
}

function formatTextures(textures) {
  return `[${textures.map(formatTexture).join('; ')}]`;
}

function formatCollisionTexture(texture) {
  return `(mk_collision_texture_input ${texture.contents})`;
}

function formatCollisionTextures(textures) {
  return `[${textures.map(formatCollisionTexture).join('; ')}]`;
}

function formatModel(model) {
  return `(mk_collision_model_input ${model.firstBrush} ${model.numBrushes})`;
}

function formatModels(models) {
  return `[${models.map(formatModel).join('; ')}]`;
}

function formatFace(face) {
  return `(mk_render_face_input ${face.texture} ${face.type} ${face.nVertexes} ` +
    `${face.nMeshverts} ${face.sizeX} ${face.sizeY})`;
}

function formatFaces(faces) {
  return `[${faces.map(formatFace).join('; ')}]`;
}

function formatPlane(plane) {
  return `(mk_collision_plane_input ${formatQ(plane.normalX)} ${formatQ(plane.normalY)} ` +
    `${formatQ(plane.normalZ)} ${formatQ(plane.dist)})`;
}

function formatPlanes(planes) {
  return `[${planes.map(formatPlane).join('; ')}]`;
}

function formatBrush(brush) {
  return `(mk_collision_brush_input ${brush.firstSide} ${brush.numSides} ${brush.textureIndex})`;
}

function formatBrushes(brushes) {
  return `[${brushes.map(formatBrush).join('; ')}]`;
}

function formatBrushSide(side) {
  return `(mk_collision_brush_side_input ${side.planeIndex})`;
}

function formatBrushSides(brushSides) {
  return `[${brushSides.map(formatBrushSide).join('; ')}]`;
}

function formatCollisionWorld(world) {
  return `(mk_collision_world_input ` +
    `${formatPlanes(world.planes)} ` +
    `${formatCollisionTextures(world.textures)} ` +
    `${formatModels(world.models || [])} ` +
    `${formatBrushes(world.brushes)} ` +
    `${formatBrushSides(world.brushSides)})`;
}

function flattenMessages(manager, messages) {
  return messages
    .map(({ msg }) => manager.pprint.pp2Text(msg))
    .join('\n');
}

function parseZList(text) {
  const match = text.match(/=\s*\[([^\]]*)\]/s);
  if (!match) {
    throw new Error(`unexpected Rocq list payload: ${text}`);
  }
  return (match[1].match(/-?\d+/g) || []).map(Number);
}

function parseCameraWords(text) {
  const words = parseZList(text);
  if (words.length !== CAMERA_WORDS_COUNT) {
    throw new Error(`expected ${CAMERA_WORDS_COUNT} camera words, got ${words.length}`);
  }
  return words;
}

function cameraSnapshotFromWords(words) {
  const toNumber = (num, den) => num / den;
  return {
    position: {
      x: toNumber(words[0], words[1]),
      y: toNumber(words[2], words[3]),
      z: toNumber(words[4], words[5]),
    },
    yaw: toNumber(words[6], words[7]),
    pitch: toNumber(words[8], words[9]),
  };
}

/**
 * Extract a camera snapshot from a serialized game-state word list.
 *
 * Word layout (see game_state_to_words in GameState.v):
 *   0-5   position xyz  (three Q rationals, num/den pairs)
 *   6-11  velocity xyz  (three Q rationals, num/den pairs — not needed here)
 *   12-13 yaw           (Q rational, num/den)
 *   14-15 pitch         (Q rational, num/den)
 *   16    on_ground
 *   17    tick
 *   18    entity_count
 *   19... serialized entity states
 */
function cameraSnapshotFromGameStateWords(words) {
  const toQ = (n, d) => n / d;
  return {
    position: {
      x: toQ(words[0],  words[1]),
      y: toQ(words[2],  words[3]),
      z: toQ(words[4],  words[5]),
    },
    yaw:   toQ(words[12], words[13]),
    pitch: toQ(words[14], words[15]),
  };
}

function snapshotFromGameStateWords(gsWords, visibleFaces) {
  const camera = cameraSnapshotFromGameStateWords(gsWords);
  return {
    ...camera,
    visibleFaces: [...visibleFaces],
    viewMatrix: buildViewMatrix(camera),
  };
}

/**
 * Format a JS input snapshot (or null) as a Rocq input_snapshot expression.
 * Null still maps to the zero snapshot so callers can opt out of driving
 * movement for a frame without special-case bridge logic.
 */
function formatInputSnapshot(input) {
  if (!input) return 'input_snapshot_zero';
  const fmt = b => (b ? 'true' : 'false');
  return `(mk_input_snapshot ` +
    `${fmt(input.forward)} ${fmt(input.back)} ` +
    `${fmt(input.left)} ${fmt(input.right)} ` +
    `${fmt(input.jump)} ` +
    `${formatQ(input.yawDelta || 0, 1000)} ${formatQ(input.pitchDelta || 0, 1000)} ` +
    `${Math.round(input.dtMs || 0)})`;
}

function buildViewMatrix(camera) {
  const viewMatrix = new Float32Array(16);
  const yawRad = camera.yaw * DEG_TO_RAD;
  const pitchRad = camera.pitch * DEG_TO_RAD;
  const cosYaw = Math.cos(yawRad);
  const sinYaw = Math.sin(yawRad);
  const cosPitch = Math.cos(pitchRad);
  const pos = camera.position;

  mat4LookAt(
    viewMatrix,
    [pos.x, pos.y, pos.z],
    [
      pos.x + cosYaw * cosPitch,
      pos.y + sinYaw * cosPitch,
      pos.z + Math.sin(pitchRad),
    ],
    [0, 0, 1]
  );

  return viewMatrix;
}

function cloneSnapshot(snapshot) {
  return {
    position: { ...snapshot.position },
    yaw: snapshot.yaw,
    pitch: snapshot.pitch,
    visibleFaces: [...snapshot.visibleFaces],
    viewMatrix: new Float32Array(snapshot.viewMatrix),
  };
}

function summarizeWorld(world) {
  return {
    entityCount: Array.isArray(world?.entities) ? world.entities.length : 0,
    faceCount: Array.isArray(world?.faces) ? world.faces.length : 0,
    textureCount: Array.isArray(world?.textures) ? world.textures.length : 0,
    planeCount: Array.isArray(world?.planes) ? world.planes.length : 0,
    modelCount: Array.isArray(world?.models) ? world.models.length : 0,
    brushCount: Array.isArray(world?.brushes) ? world.brushes.length : 0,
    brushSideCount: Array.isArray(world?.brushSides) ? world.brushSides.length : 0,
  };
}

function summarizeWordList(words, previewLength = 8) {
  return {
    count: words.length,
    preview: words.slice(0, previewLength),
  };
}

function summarizeSnapshot(snapshot) {
  return {
    position: { ...snapshot.position },
    yaw: snapshot.yaw,
    pitch: snapshot.pitch,
    visibleFaceCount: snapshot.visibleFaces.length,
  };
}

function summarizeError(err) {
  return {
    message: err instanceof Error ? err.message : String(err),
    stack: err instanceof Error ? (err.stack || '') : '',
  };
}

function emitDiagnostic(emit, stage, payload = {}) {
  if (!emit) return;
  emit({
    stage,
    at: new Date().toISOString(),
    payload,
  });
}

async function waitForSentenceSid(sentence) {
  while (!sentence.coq_sid) {
    await nextTick();
  }
  return sentence.coq_sid;
}

async function waitForManagerReady(manager) {
  if (manager?.when_ready?.promise) {
    await manager.when_ready.promise;
    return;
  }
  while (!manager?.coq) {
    await nextTick();
  }
}

async function waitForSentenceProcessed(sentence, sid) {
  while (true) {
    const phase = typeof sentence?.phase === 'string' ? sentence.phase : '';
    if (phase === SENTENCE_PHASE_PROCESSED) return;
    if (phase === SENTENCE_PHASE_ERROR || phase === SENTENCE_PHASE_CANCELLING) {
      throw new Error(`Rocq sentence ${sid} stopped before it finished processing (phase: ${phase})`);
    }
    await nextTick();
  }
}

async function ensureBridgeHelpersReady(manager) {
  await waitForManagerReady(manager);

  let sentence = manager.doc.sentences.find(stm =>
    stm.coq_sid && stm.text.includes(BRIDGE_HELPERS_DEFINITION));
  if (sentence) {
    await waitForSentenceProcessed(sentence, sentence.coq_sid);
    return sentence.coq_sid;
  }

  while (manager.goNext(false)) {
    sentence = manager.doc.sentences[manager.doc.sentences.length - 1];
    const sid = await waitForSentenceSid(sentence);
    await waitForSentenceProcessed(sentence, sid);
    if (sentence.text.includes(BRIDGE_HELPERS_DEFINITION)) {
      return sid;
    }
  }

  throw new Error('Rocq bridge helper definitions were not found in the loaded theory');
}

async function evalInitialGameStateWords(manager, sid, world) {
  const command =
    `Eval vm_compute in (initial_game_state_words_from_entities ` +
    `${formatEntities(world.entities)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  const words = parseZList(flattenMessages(manager, messages));
  if (words.length < MIN_GAME_STATE_WORDS_COUNT) {
    throw new Error(
      `expected at least ${MIN_GAME_STATE_WORDS_COUNT} game-state words, got ${words.length}`);
  }
  return words;
}

async function evalVisibleFaces(manager, sid, world) {
  const command =
    `Eval vm_compute in (initial_visible_faces_from_inputs ` +
    `${formatEntities(world.entities)} ${formatFaces(world.faces)} ${formatTextures(world.textures)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  return parseZList(flattenMessages(manager, messages));
}

async function evalStepWorldWords(manager, sid, collisionWorldExpr, gsWords, inputSnapshot) {
  const command =
    `Eval vm_compute in (step_world_words_in_world ${collisionWorldExpr} ` +
    `${formatZList(gsWords)} ${formatInputSnapshot(inputSnapshot)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  const words = parseZList(flattenMessages(manager, messages));
  if (words.length < MIN_GAME_STATE_WORDS_COUNT) {
    throw new Error(
      `expected at least ${MIN_GAME_STATE_WORDS_COUNT} game-state words from step, got ${words.length}`);
  }
  return words;
}

export function createRocqBridge(manager, options = {}) {
  let bridgeHelpersSidPromise = null;
  let gsWords = null;        // current game-state word list
  let initialGsWords = null; // snapshot saved at load_world for reset()
  let visibleFaces = null;   // static visible-face indices (no PVS yet)
  let collisionWorldExpr = null;
  const onDiagnostic =
    typeof options.onDiagnostic === 'function' ? options.onDiagnostic : null;

  function getBridgeHelpersSid() {
    bridgeHelpersSidPromise ||= ensureBridgeHelpersReady(manager);
    return bridgeHelpersSidPromise;
  }

  function assertLoaded() {
    if (!gsWords) throw new Error('load_world must run before step/reset');
  }

  return {
    version: BRIDGE_VERSION,

    async prepare() {
      await getBridgeHelpersSid();
    },

    async load_world(world) {
      try {
        emitDiagnostic(onDiagnostic, 'load_world:requested', summarizeWorld(world));
        const sid = await getBridgeHelpersSid();
        emitDiagnostic(onDiagnostic, 'load_world:helpers-ready', { sid });
        // Fires right before queryPromise calls — confirms Rocq worker is being
        // invoked.  A timeout gap between helpers-ready and received means the
        // manager handoff stalled; a gap after received means the WASM worker
        // itself stalled (case B in #74).
        emitDiagnostic(onDiagnostic, 'load_world:received', { sid });
        const wordsPromise = evalInitialGameStateWords(manager, sid, world)
          .then(words => {
            emitDiagnostic(onDiagnostic, 'load_world:game-state-words', summarizeWordList(words));
            return words;
          });
        const facesPromise = evalVisibleFaces(manager, sid, world)
          .then(faces => {
            emitDiagnostic(onDiagnostic, 'load_world:visible-faces', summarizeWordList(faces));
            return faces;
          });
        const [words, faces] = await Promise.all([wordsPromise, facesPromise]);
        // Both Rocq queries resolved and their outputs are parsed — all Rocq
        // data is in hand.  A gap here (after visible-faces/game-state-words
        // but before decoded) would indicate one query stalled.
        emitDiagnostic(onDiagnostic, 'load_world:decoded', {
          gsWordCount: words.length,
          visibleFaceCount: faces.length,
        });
        collisionWorldExpr = formatCollisionWorld(world);
        gsWords        = words;
        initialGsWords = [...words];
        visibleFaces   = faces;
        const snapshot = snapshotFromGameStateWords(gsWords, visibleFaces);
        // Snapshot object is fully constructed on the JS side.  A gap between
        // snapshot_built and complete would indicate the return path stalled
        // (case C in #74).
        emitDiagnostic(onDiagnostic, 'load_world:snapshot_built', summarizeSnapshot(snapshot));
        emitDiagnostic(onDiagnostic, 'load_world:complete', summarizeSnapshot(snapshot));
        return snapshot;
      } catch (err) {
        emitDiagnostic(onDiagnostic, 'load_world:failed', summarizeError(err));
        throw err;
      }
    },

    async step(inputSnapshot) {
      assertLoaded();
      const sid = await getBridgeHelpersSid();
      gsWords = await evalStepWorldWords(manager, sid, collisionWorldExpr, gsWords, inputSnapshot);
      return snapshotFromGameStateWords(gsWords, visibleFaces);
    },

    async reset() {
      assertLoaded();
      gsWords = [...initialGsWords];
      return snapshotFromGameStateWords(gsWords, visibleFaces);
    },
  };
}
