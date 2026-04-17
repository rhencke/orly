import { mat4LookAt } from './renderer.js';

const DEG_TO_RAD = Math.PI / 180;
const BRIDGE_VERSION = 1;
const BRIDGE_HELPERS_DEFINITION = 'Definition step_world_words';
const CAMERA_WORDS_COUNT = 10;
const GAME_STATE_WORDS_COUNT = 18;

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

function formatFace(face) {
  return `(mk_render_face_input ${face.texture} ${face.type} ${face.nVertexes} ` +
    `${face.nMeshverts} ${face.sizeX} ${face.sizeY})`;
}

function formatFaces(faces) {
  return `[${faces.map(formatFace).join('; ')}]`;
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
 * Until keyboard/mouse wiring lands in a later task, null maps to the zero
 * snapshot so that step calls are valid Rocq before input is plumbed.
 */
function formatInputSnapshot(input) {
  if (!input) return 'input_snapshot_zero';
  const fmt = b => (b ? 'true' : 'false');
  const fmtQ = x => {
    const r = Math.round(x * 1000);
    return `(${r} # 1000)`;
  };
  return `(mk_input_snapshot ` +
    `${fmt(input.forward)} ${fmt(input.back)} ` +
    `${fmt(input.left)} ${fmt(input.right)} ` +
    `${fmt(input.jump)} ` +
    `${fmtQ(input.yawDelta || 0)} ${fmtQ(input.pitchDelta || 0)} ` +
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

async function waitForSentenceSid(sentence) {
  while (!sentence.coq_sid) {
    await nextTick();
  }
  return sentence.coq_sid;
}

async function ensureBridgeHelpersReady(manager) {
  await manager.when_ready.promise;

  let sentence = manager.doc.sentences.find(stm =>
    stm.coq_sid && stm.text.includes(BRIDGE_HELPERS_DEFINITION));
  if (sentence) return sentence.coq_sid;

  while (manager.goNext(false)) {
    sentence = manager.doc.sentences[manager.doc.sentences.length - 1];
    const sid = await waitForSentenceSid(sentence);
    await manager.coq.sids[sid].promise;
    if (sentence.text.includes(BRIDGE_HELPERS_DEFINITION)) {
      return sid;
    }
  }

  throw new Error('Rocq bridge helper definitions were not found in the loaded theory');
}

async function evalInitialGameStateWords(manager, sid, world) {
  const command =
    `Eval cbv in (initial_game_state_words_from_entities ` +
    `${formatEntities(world.entities)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  const words = parseZList(flattenMessages(manager, messages));
  if (words.length !== GAME_STATE_WORDS_COUNT) {
    throw new Error(
      `expected ${GAME_STATE_WORDS_COUNT} game-state words, got ${words.length}`);
  }
  return words;
}

async function evalVisibleFaces(manager, sid, world) {
  const command =
    `Eval cbv in (initial_visible_faces_from_inputs ` +
    `${formatEntities(world.entities)} ${formatFaces(world.faces)} ${formatTextures(world.textures)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  return parseZList(flattenMessages(manager, messages));
}

async function evalStepWorldWords(manager, sid, gsWords, inputSnapshot) {
  const command =
    `Eval cbv in (step_world_words ` +
    `${formatZList(gsWords)} ${formatInputSnapshot(inputSnapshot)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  const words = parseZList(flattenMessages(manager, messages));
  if (words.length !== GAME_STATE_WORDS_COUNT) {
    throw new Error(
      `expected ${GAME_STATE_WORDS_COUNT} game-state words from step, got ${words.length}`);
  }
  return words;
}

export function createRocqBridge(manager) {
  let bridgeHelpersSidPromise = null;
  let gsWords = null;        // current game-state word list
  let initialGsWords = null; // snapshot saved at load_world for reset()
  let visibleFaces = null;   // static visible-face indices (no PVS yet)

  function getBridgeHelpersSid() {
    bridgeHelpersSidPromise ||= ensureBridgeHelpersReady(manager);
    return bridgeHelpersSidPromise;
  }

  function assertLoaded() {
    if (!gsWords) throw new Error('load_world must run before step/reset');
  }

  return {
    version: BRIDGE_VERSION,

    async load_world(world) {
      const sid = await getBridgeHelpersSid();
      const [words, faces] = await Promise.all([
        evalInitialGameStateWords(manager, sid, world),
        evalVisibleFaces(manager, sid, world),
      ]);
      gsWords        = words;
      initialGsWords = [...words];
      visibleFaces   = faces;
      return snapshotFromGameStateWords(gsWords, visibleFaces);
    },

    async step(inputSnapshot) {
      assertLoaded();
      const sid = await getBridgeHelpersSid();
      gsWords = await evalStepWorldWords(manager, sid, gsWords, inputSnapshot);
      return snapshotFromGameStateWords(gsWords, visibleFaces);
    },

    async reset() {
      assertLoaded();
      gsWords = [...initialGsWords];
      return snapshotFromGameStateWords(gsWords, visibleFaces);
    },
  };
}
