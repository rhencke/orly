import { mat4LookAt } from './renderer.js';

const DEG_TO_RAD = Math.PI / 180;
const BRIDGE_VERSION = 1;
const CAMERA_WORDS_DEFINITION = 'Definition initial_camera_words_from_entities';
const CAMERA_WORDS_COUNT = 10;

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

function flattenMessages(manager, messages) {
  return messages
    .map(({ msg }) => manager.pprint.pp2Text(msg))
    .join('\n');
}

function parseCameraWords(text) {
  const match = text.match(/=\s*\[([^\]]*)\]/s);
  if (!match) {
    throw new Error(`unexpected Rocq camera payload: ${text}`);
  }
  const words = (match[1].match(/-?\d+/g) || []).map(Number);
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
    viewMatrix: new Float32Array(snapshot.viewMatrix),
  };
}

async function waitForSentenceSid(sentence) {
  while (!sentence.coq_sid) {
    await nextTick();
  }
  return sentence.coq_sid;
}

async function ensureCameraWordsReady(manager) {
  await manager.when_ready.promise;

  let sentence = manager.doc.sentences.find(stm =>
    stm.coq_sid && stm.text.includes(CAMERA_WORDS_DEFINITION));
  if (sentence) return sentence.coq_sid;

  while (manager.goNext(false)) {
    sentence = manager.doc.sentences[manager.doc.sentences.length - 1];
    const sid = await waitForSentenceSid(sentence);
    await manager.coq.sids[sid].promise;
    if (sentence.text.includes(CAMERA_WORDS_DEFINITION)) {
      return sid;
    }
  }

  throw new Error('Rocq bridge helper definitions were not found in the loaded theory');
}

async function evalCameraWords(manager, sid, entities) {
  const command =
    `Eval cbv in (initial_camera_words_from_entities ${formatEntities(entities)}).`;
  const messages = await manager.coq.queryPromise(sid, ['Vernac', command]);
  return parseCameraWords(flattenMessages(manager, messages));
}

export function createRocqBridge(manager) {
  let cameraWordsSidPromise = null;
  let initialSnapshot = null;

  function getCameraWordsSid() {
    cameraWordsSidPromise ||= ensureCameraWordsReady(manager);
    return cameraWordsSidPromise;
  }

  return {
    version: BRIDGE_VERSION,

    async load_world(entities) {
      const sid = await getCameraWordsSid();
      const words = await evalCameraWords(manager, sid, entities);
      const camera = cameraSnapshotFromWords(words);
      initialSnapshot = {
        ...camera,
        viewMatrix: buildViewMatrix(camera),
      };
      return cloneSnapshot(initialSnapshot);
    },

    async step(_inputSnapshot) {
      if (!initialSnapshot) {
        throw new Error('load_world must run before step');
      }
      return cloneSnapshot(initialSnapshot);
    },

    async reset() {
      if (!initialSnapshot) {
        throw new Error('load_world must run before reset');
      }
      return cloneSnapshot(initialSnapshot);
    },
  };
}
