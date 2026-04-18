import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { spawn } from 'node:child_process';
import { chromium, devices } from 'playwright';

const ROOT = process.cwd();
const DOCS_DIR = path.join(ROOT, 'docs');
const LICENSED_MAP_PATH = 'maps/am_lavaarena.bsp';
const BSP_MAGIC_BYTES = [0x49, 0x42, 0x53, 0x50];
const LICENSED_MAP_SOURCE = path.join(
  DOCS_DIR,
  'vendor',
  'maps',
  'openarena',
  'am_lavaarena.bsp'
);
const DEPLOYED_URL = process.env.ORLY_REPRO_DEPLOYED_URL?.trim() || null;
const SKIP_LOCAL_SCENARIOS = /^(1|true)$/i.test(process.env.ORLY_REPRO_SKIP_LOCAL ?? '');
const PORT_BASE = Number.parseInt(process.env.ORLY_REPRO_PORT ?? '18080', 10);
const TIMEOUT_MS = Number.parseInt(process.env.ORLY_REPRO_TIMEOUT_MS ?? '20000', 10);
const POLL_MS = 500;
const BOOTSTRAP_FAILURE_RE =
  /launch failure SecurityError|Failed to construct 'Worker'|JsCoq bootstrap failed/i;
const ROCQ_STARTUP_FAILURE_RE =
  /Coq Exception|Cannot find a physical path bound to logical path|Rocq bridge helper definitions were not found/i;
const RENDER_FAILURE_RE = /BSP render init failed|Render error:/i;
const SUCCESSFUL_RENDER_RE = /render pipeline active/i;
const MIN_TOUCH_TARGET_PX = 44;
const MIN_SAFE_AREA_PADDING_PX = 12;

const IPHONE_13 = devices['iPhone 13'];
const IPHONE_13_LANDSCAPE = {
  ...IPHONE_13,
  viewport: {
    width: IPHONE_13.viewport.height,
    height: IPHONE_13.viewport.width,
  },
};

const STUB_BRIDGE_SOURCE = `
const VIEW_MATRIX = [1, 0, 0, 0,
                     0, 1, 0, 0,
                     0, 0, 1, 0,
                     0, 0, 0, 1];

export function createRocqBridge(_manager, options = {}) {
  let visibleFaces = [];
  const onDiagnostic =
    typeof options?.onDiagnostic === 'function' ? options.onDiagnostic : null;

  function emit(stage, payload = {}) {
    onDiagnostic?.({
      stage,
      at: new Date().toISOString(),
      payload,
    });
  }

  function snapshot() {
    return {
      position: { x: 0, y: 0, z: 0 },
      yaw: 0,
      pitch: 0,
      visibleFaces: [...visibleFaces],
      viewMatrix: new Float32Array(VIEW_MATRIX),
    };
  }

  return {
    version: 1,

    async prepare() {},

    async load_world(world) {
      visibleFaces = Array.isArray(world?.faces)
        ? world.faces.map((_, fi) => fi)
        : [];
      emit('load_world:requested', {
        faceCount: visibleFaces.length,
      });
      emit('load_world:received', {});
      const nextSnapshot = snapshot();
      emit('load_world:decoded', {
        gsWordCount: 0,
        visibleFaceCount: nextSnapshot.visibleFaces.length,
      });
      emit('load_world:snapshot_built', {
        visibleFaceCount: nextSnapshot.visibleFaces.length,
      });
      emit('load_world:complete', {
        visibleFaceCount: nextSnapshot.visibleFaces.length,
      });
      return nextSnapshot;
    },

    async step() {
      return snapshot();
    },

    async reset() {
      return snapshot();
    },
  };
}
`;

const HANGING_BRIDGE_SOURCE = `
export function createRocqBridge(_manager, options = {}) {
  const onDiagnostic =
    typeof options?.onDiagnostic === 'function' ? options.onDiagnostic : null;

  function emit(stage, payload = {}) {
    onDiagnostic?.({
      stage,
      at: new Date().toISOString(),
      payload,
    });
  }

  return {
    version: 1,

    async prepare() {},

    async load_world(world) {
      emit('load_world:requested', {
        entityCount: Array.isArray(world?.entities) ? world.entities.length : 0,
        faceCount: Array.isArray(world?.faces) ? world.faces.length : 0,
        textureCount: Array.isArray(world?.textures) ? world.textures.length : 0,
      });
      emit('load_world:waiting', {
        reason: 'repro bridge intentionally never resolves load_world',
      });
      await new Promise(() => {});
    },

    async step() {
      throw new Error('step should not run while load_world is hanging');
    },

    async reset() {
      throw new Error('reset should not run while load_world is hanging');
    },
  };
}
`;

// Bridge that simulates slow theory compilation by emitting compile:sentence
// events at 100 ms intervals (6 sentences, 600 ms total) before completing.
// With rocq_sync_timeout_ms=500 a flat withTimeout would fire at 500 ms and
// kill the load mid-compile; withActivityTimeout resets on every event and
// lets it finish.  Used by the activity-timeout and progress-overlay tests.
const SLOW_COMPILE_BRIDGE_SOURCE = `
const VIEW_MATRIX = [1, 0, 0, 0,
                     0, 1, 0, 0,
                     0, 0, 1, 0,
                     0, 0, 0, 1];

export function createRocqBridge(_manager, options = {}) {
  let visibleFaces = [];
  const onDiagnostic =
    typeof options?.onDiagnostic === 'function' ? options.onDiagnostic : null;

  function emit(stage, payload = {}) {
    onDiagnostic?.({
      stage,
      at: new Date().toISOString(),
      payload,
    });
  }

  function snapshot() {
    return {
      position: { x: 0, y: 0, z: 0 },
      yaw: 0,
      pitch: 0,
      visibleFaces: [...visibleFaces],
      viewMatrix: new Float32Array(VIEW_MATRIX),
    };
  }

  return {
    version: 1,

    async prepare() {},

    async load_world(world) {
      visibleFaces = Array.isArray(world?.faces)
        ? world.faces.map((_, fi) => fi)
        : [];
      emit('load_world:requested', { faceCount: visibleFaces.length });

      // Simulate six sentences compiling at 100 ms intervals.
      // Total theory-compile window: 600 ms.  The activity-based timeout
      // (withActivityTimeout) resets on each compile:sentence event so the
      // load is never killed mid-compile even with rocq_sync_timeout_ms=500.
      const SENTENCE_COUNT = 6;
      for (let i = 1; i <= SENTENCE_COUNT; i++) {
        await new Promise(resolve => setTimeout(resolve, 100));
        emit('compile:sentence', {
          sid: i,
          sentenceIndex: i,
          isTarget: i === SENTENCE_COUNT,
        });
      }

      const nextSnapshot = snapshot();
      emit('load_world:helpers-ready', { sid: SENTENCE_COUNT });
      emit('load_world:received', { sid: SENTENCE_COUNT });
      emit('load_world:decoded', {
        gsWordCount: 0,
        visibleFaceCount: nextSnapshot.visibleFaces.length,
      });
      emit('load_world:snapshot_built', {
        visibleFaceCount: nextSnapshot.visibleFaces.length,
      });
      emit('load_world:complete', {
        visibleFaceCount: nextSnapshot.visibleFaces.length,
      });
      return nextSnapshot;
    },

    async step() {
      return snapshot();
    },

    async reset() {
      return snapshot();
    },
  };
}
`;

async function withNodeTimeout(promise, timeoutMs, message) {
  let timeoutId = null;
  try {
    return await Promise.race([
      promise,
      new Promise((_, reject) => {
        timeoutId = setTimeout(() => reject(new Error(message)), timeoutMs);
      }),
    ]);
  } finally {
    if (timeoutId !== null) clearTimeout(timeoutId);
  }
}

async function sleep(ms) {
  await new Promise(resolve => setTimeout(resolve, ms));
}

async function runMissingSentencePromiseRegression() {
  const scenario = 'bridge-missing-sentence-promise-regression';

  try {
    const { createRocqBridge } =
      await import(new URL('../docs/rocq_bridge.js', import.meta.url));
    const diagnostics = [];
    const queryCalls = [];
    const helperSentence = {
      text: 'Definition step_world_words_in_world := step_world_words_in_world.',
      coq_sid: 7,
      phase: 'processing',
    };
    const manager = {
      when_ready: {
        promise: Promise.resolve(),
      },
      doc: {
        sentences: [helperSentence],
      },
      goNext() {
        return false;
      },
      pprint: {
        pp2Text(message) {
          return message;
        },
      },
      coq: {
        // The regression is that helper readiness must not depend on
        // coq.sids[sid].promise existing on the manager.
        queryPromise(sid, query) {
          const command = Array.isArray(query) ? String(query[1] ?? '') : String(query ?? '');
          queryCalls.push({ sid, command });

          if (command.includes('initial_game_state_words_from_entities')) {
            return Promise.resolve([
              { msg: '= [0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 0]' },
            ]);
          }
          if (command.includes('initial_visible_faces_from_inputs')) {
            return Promise.resolve([{ msg: '= []' }]);
          }

          throw new Error(`unexpected Rocq query in regression: ${command}`);
        },
      },
    };
    const bridge = createRocqBridge(manager, {
      onDiagnostic(event) {
        diagnostics.push(event);
      },
    });
    const world = {
      entities: [],
      faces: [],
      textures: [],
      planes: [],
      models: [],
      brushes: [],
      brushSides: [],
    };

    const preparePromise = bridge.prepare();
    const loadWorldPromise = bridge.load_world(world);

    setTimeout(() => {
      helperSentence.phase = 'processed';
    }, 25);

    const snapshot = await withNodeTimeout(
      loadWorldPromise,
      1000,
      'timed out waiting for load_world after load_world:requested without a JsCoq sentence promise'
    );
    await withNodeTimeout(
      preparePromise,
      1000,
      'timed out waiting for prepare without a JsCoq sentence promise'
    );

    const stages = diagnostics.map(event => event.stage);
    if (stages[0] !== 'load_world:requested') {
      throw new Error(`unexpected first regression stage: ${stages[0] ?? '(missing)'}`);
    }
    if (!stages.includes('rocq:alive')) {
      throw new Error('helper readiness regression never received rocq:alive heartbeat');
    }
    if (!stages.includes('load_world:helpers-ready')) {
      throw new Error('helper readiness regression never reached load_world:helpers-ready');
    }
    if (!stages.includes('load_world:received')) {
      throw new Error('helper readiness regression never reached load_world:received');
    }
    if (!stages.includes('load_world:decoded')) {
      throw new Error('helper readiness regression never reached load_world:decoded');
    }
    if (!stages.includes('load_world:snapshot_built')) {
      throw new Error('helper readiness regression never reached load_world:snapshot_built');
    }
    if (!stages.includes('load_world:complete')) {
      throw new Error('helper readiness regression never reached load_world:complete');
    }
    if (queryCalls.length !== 2) {
      throw new Error(`expected two Rocq queries in regression, got ${queryCalls.length}`);
    }
    if (!Array.isArray(snapshot.visibleFaces)) {
      throw new Error('regression snapshot did not include visibleFaces');
    }

    return {
      scenario,
      passed: true,
      details: {
        diagnostics,
        queryCalls,
        snapshot: {
          position: snapshot.position,
          yaw: snapshot.yaw,
          pitch: snapshot.pitch,
          visibleFaceCount: snapshot.visibleFaces.length,
        },
      },
    };
  } catch (error) {
    return {
      scenario,
      passed: false,
      failure: error.message,
      stack: error.stack ?? '',
    };
  }
}

async function runCompileSentenceDiagnosticsRegression() {
  const scenario = 'bridge-compile-sentence-diagnostics-regression';

  try {
    const { createRocqBridge } =
      await import(new URL('../docs/rocq_bridge.js', import.meta.url));
    const diagnostics = [];
    const queryCalls = [];

    // Three sentences: two non-target, then the target (contains
    // BRIDGE_HELPERS_DEFINITION).  goNext() adds them one at a time so the
    // loop in ensureBridgeHelpersReady exercises the compile:sentence path.
    const sentences = [
      { text: 'Require Import Foo.',           coq_sid: null, phase: 'processing' },
      { text: 'Definition bar := 42.',          coq_sid: null, phase: 'processing' },
      {
        text: 'Definition step_world_words_in_world := step_world_words_in_world.',
        coq_sid: null,
        phase: 'processing',
      },
    ];
    let goNextCallCount = 0;

    const manager = {
      when_ready: { promise: Promise.resolve() },
      doc: { sentences: [] },
      goNext() {
        if (goNextCallCount >= sentences.length) return false;
        const sentence = sentences[goNextCallCount];
        goNextCallCount++;
        manager.doc.sentences.push(sentence);
        // coq_sid assigned synchronously; phase transitions after a short delay
        // so waitForSentenceProcessed has something to poll.
        sentence.coq_sid = goNextCallCount;
        const delay = 10 * goNextCallCount;
        setTimeout(() => { sentence.phase = 'processed'; }, delay);
        return true;
      },
      pprint: { pp2Text(message) { return message; } },
      coq: {
        queryPromise(sid, query) {
          const command = Array.isArray(query) ? String(query[1] ?? '') : String(query ?? '');
          queryCalls.push({ sid, command });
          if (command.includes('initial_game_state_words_from_entities')) {
            return Promise.resolve([
              { msg: '= [0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 0; 1; 1; 0; 0]' },
            ]);
          }
          if (command.includes('initial_visible_faces_from_inputs')) {
            return Promise.resolve([{ msg: '= []' }]);
          }
          throw new Error(`unexpected Rocq query in regression: ${command}`);
        },
      },
    };

    const bridge = createRocqBridge(manager, {
      onDiagnostic(event) { diagnostics.push(event); },
    });
    const world = {
      entities: [], faces: [], textures: [], planes: [],
      models: [], brushes: [], brushSides: [],
    };

    const snapshot = await withNodeTimeout(
      bridge.load_world(world),
      2000,
      'timed out waiting for load_world during compile-sentence regression'
    );

    const stages = diagnostics.map(event => event.stage);
    const compileSentenceEvents = diagnostics.filter(event => event.stage === 'compile:sentence');

    if (compileSentenceEvents.length !== 3) {
      throw new Error(
        `expected 3 compile:sentence events, got ${compileSentenceEvents.length}`
      );
    }

    for (let i = 0; i < compileSentenceEvents.length; i++) {
      const { sentenceIndex, isTarget } = compileSentenceEvents[i].payload;
      if (sentenceIndex !== i + 1) {
        throw new Error(
          `compile:sentence[${i}].sentenceIndex should be ${i + 1}, got ${sentenceIndex}`
        );
      }
      const expectedTarget = i === compileSentenceEvents.length - 1;
      if (isTarget !== expectedTarget) {
        throw new Error(
          `compile:sentence[${i}].isTarget should be ${expectedTarget}, got ${isTarget}`
        );
      }
    }

    if (!stages.includes('load_world:helpers-ready')) {
      throw new Error('compile-sentence regression never reached load_world:helpers-ready');
    }
    if (!stages.includes('load_world:complete')) {
      throw new Error('compile-sentence regression never completed load_world');
    }
    if (!Array.isArray(snapshot.visibleFaces)) {
      throw new Error('compile-sentence regression snapshot did not include visibleFaces');
    }

    return {
      scenario,
      passed: true,
      details: { diagnostics, compileSentenceEvents, queryCalls },
    };
  } catch (error) {
    return {
      scenario,
      passed: false,
      failure: error.message,
      stack: error.stack ?? '',
    };
  }
}

async function waitForUrl(url, timeoutMs) {
  const deadline = Date.now() + timeoutMs;
  let lastError = null;

  while (Date.now() < deadline) {
    try {
      const response = await fetch(url, { method: 'HEAD' });
      if (response.ok) return;
      lastError = new Error(`HTTP ${response.status}`);
    } catch (error) {
      lastError = error;
    }
    await sleep(250);
  }

  throw new Error(`timed out waiting for ${url}: ${lastError?.message ?? 'unknown error'}`);
}

async function inspectDeployedAssetCaching(baseUrl) {
  const manifestUrl = new URL('assets/manifest.json', baseUrl).href;
  const mapUrl = new URL(`assets/${LICENSED_MAP_PATH}`, baseUrl).href;

  async function readHeaders(url, init = {}) {
    const response = await fetch(url, init);
    return {
      url,
      status: response.status,
      ok: response.ok,
      headers: Object.fromEntries(response.headers.entries()),
    };
  }

  const [manifestHead, mapHead, mapGet] = await Promise.all([
    readHeaders(manifestUrl, { method: 'HEAD' }),
    readHeaders(mapUrl, { method: 'HEAD' }),
    (async () => {
      const response = await fetch(mapUrl);
      const buffer = await response.arrayBuffer();
      return {
        url: mapUrl,
        status: response.status,
        ok: response.ok,
        headers: Object.fromEntries(response.headers.entries()),
        firstBytes: Array.from(new Uint8Array(buffer).slice(0, BSP_MAGIC_BYTES.length)),
      };
    })(),
  ]);

  const etag = mapHead.headers.etag ?? mapGet.headers.etag ?? null;
  const revalidateHead = etag
    ? await readHeaders(mapUrl, { method: 'HEAD', headers: { 'If-None-Match': etag } })
    : null;

  return {
    manifestHead,
    mapHead,
    mapGet,
    revalidateHead,
  };
}

function startStaticServer(rootDir, port) {
  const server = spawn(
    'python3',
    ['-m', 'http.server', String(port), '--directory', rootDir],
    {
      cwd: ROOT,
      stdio: ['ignore', 'pipe', 'pipe'],
    }
  );

  let stdout = '';
  let stderr = '';
  server.stdout.on('data', chunk => {
    stdout += chunk.toString();
  });
  server.stderr.on('data', chunk => {
    stderr += chunk.toString();
  });

  return { server, readLogs: () => ({ stdout, stderr }) };
}

async function createScenarioRoot(scenarioName) {
  const rootDir = await fs.mkdtemp(path.join(os.tmpdir(), `orly-${scenarioName}-`));
  await fs.cp(DOCS_DIR, rootDir, { recursive: true });
  await fs.rm(path.join(rootDir, 'assets'), { recursive: true, force: true });

  if (scenarioName === 'licensed-map-render-startup' ||
      scenarioName === 'licensed-map-parse-handoff' ||
      scenarioName === 'full-theory-with-proofs-compiles' ||
      scenarioName === 'rocq-sync-timeout-overlay' ||
      scenarioName === 'slow-compile-overlay') {
    await fs.mkdir(path.join(rootDir, 'assets', 'maps'), { recursive: true });
    await fs.writeFile(
      path.join(rootDir, 'assets', 'manifest.json'),
      `${JSON.stringify([LICENSED_MAP_PATH])}\n`
    );
    await fs.copyFile(LICENSED_MAP_SOURCE, path.join(rootDir, 'assets', LICENSED_MAP_PATH));
  }

  if (scenarioName === 'licensed-map-render-startup' ||
      scenarioName === 'rocq-sync-timeout-overlay' ||
      scenarioName === 'slow-compile-overlay') {
    const bridgeSource =
      scenarioName === 'rocq-sync-timeout-overlay' ? HANGING_BRIDGE_SOURCE :
      scenarioName === 'slow-compile-overlay'       ? SLOW_COMPILE_BRIDGE_SOURCE :
                                                      STUB_BRIDGE_SOURCE;
    await fs.writeFile(path.join(rootDir, 'rocq_bridge.js'), bridgeSource);
  }

  return rootDir;
}

async function gatherSnapshot(page) {
  return page.evaluate(() => {
    const statusBar = document.getElementById('status-bar');
    const placeholder = document.getElementById('game-placeholder');
    const placeholderTitle = placeholder?.querySelector('[data-placeholder-role="title"]');
    const placeholderDetail = placeholder?.querySelector('[data-placeholder-role="detail"]');
    const copyButton = placeholder?.querySelector('[data-placeholder-role="copy-button"]');
    const copyFallback = placeholder?.querySelector('[data-placeholder-role="copy-fallback"]');
    const canvas = document.getElementById('game-canvas');
    const overlay = document.getElementById('game-overlay');
    const main = document.getElementById('main');
    const jscoqPanel = document.getElementById('jscoq-panel');
    const ideWrapper = document.getElementById('ide-wrapper');
    const jscoqEditor = document.getElementById('document');
    const panelWrapper = document.getElementById('panel-wrapper');
    const toolbar = document.getElementById('toolbar');
    const goalPanel = document.getElementById('goal-panel');
    const queryPanel = document.getElementById('query-panel');
    const packagesPanel = document.getElementById('packages-panel');
    const helpPanel = document.getElementById('help-panel');
    const lowerPanelShell = document.getElementById('lower-panel-shell');
    const lowerPanelHeader = document.getElementById('lower-panel-header');
    const lowerPanelLabel = document.getElementById('lower-panel-label');
    const lowerPanelTitle = document.getElementById('lower-panel-title');
    const lowerPanelCopy = document.getElementById('lower-panel-copy');
    const lowerPanelFocus = document.getElementById('lower-panel-focus');
    const lowerPanelFocusLabel = document.getElementById('lower-panel-focus-label');
    const lowerPanelSectionButtons = Array.from(document.querySelectorAll('.lower-panel-section-button'));
    const resizeHandle = document.getElementById('resize-handle');
    const touchControls = document.getElementById('touch-controls');
    const movePad = document.querySelector('[data-touch-control="move-pad"]');
    const lookPad = document.querySelector('[data-touch-control="look-pad"]');
    const jumpButton = document.querySelector('[data-touch-control="jump"]');
    const desktopHint = document.getElementById('game-hint-desktop');
    const mobileHint = document.getElementById('game-hint-mobile');
    const assetMap = window.orlyAssets instanceof Map ? window.orlyAssets : null;
    const buildInfo = window.orlyBuildInfo && typeof window.orlyBuildInfo === 'object'
      ? structuredClone(window.orlyBuildInfo)
      : null;
    const errorReport = window.orlyErrorReport && typeof window.orlyErrorReport === 'object'
      ? structuredClone(window.orlyErrorReport)
      : null;
    const rocqSyncDiagnostics =
      window.orlyRocqSyncDiagnostics && typeof window.orlyRocqSyncDiagnostics === 'object'
        ? structuredClone(window.orlyRocqSyncDiagnostics)
        : null;
    const bspParseDiagnostics =
      window.orlyBspParseDiagnostics && typeof window.orlyBspParseDiagnostics === 'object'
        ? structuredClone(window.orlyBspParseDiagnostics)
        : null;

    function rectOf(element) {
      if (!element) return null;
      const rect = element.getBoundingClientRect();
      return {
        left: rect.left,
        top: rect.top,
        right: rect.right,
        bottom: rect.bottom,
        width: rect.width,
        height: rect.height,
      };
    }

    function visibilityOf(element) {
      if (!element) return null;
      const style = window.getComputedStyle(element);
      const rect = element.getBoundingClientRect();
      return {
        hidden: Boolean(element.hidden),
        display: style.display,
        visibility: style.visibility,
        opacity: style.opacity,
        visible:
          !element.hidden &&
          style.display !== 'none' &&
          style.visibility !== 'hidden' &&
          Number.parseFloat(style.opacity || '1') > 0 &&
          rect.width > 0 &&
          rect.height > 0,
      };
    }

    function flexPanelState(element) {
      if (!element) return null;
      const panel = element.closest('.flex-panel') ?? element;
      const caption = panel.querySelector('.caption');
      return {
        rect: rectOf(element),
        panelRect: rectOf(panel),
        captionRect: rectOf(caption),
        captionText: caption?.textContent?.trim() ?? '',
        className: panel.className,
        collapsed: panel.classList.contains('collapsed'),
      };
    }

    const overlayStyle = overlay ? window.getComputedStyle(overlay) : null;
    const mainStyle = main ? window.getComputedStyle(main) : null;
    const ideWrapperStyle = ideWrapper ? window.getComputedStyle(ideWrapper) : null;

    return {
      viewport: {
        width: window.innerWidth,
        height: window.innerHeight,
      },
      pointer: {
        coarse: window.matchMedia('(pointer: coarse)').matches,
      },
      status: statusBar
        ? {
            hidden: statusBar.hidden,
            text: statusBar.textContent?.trim() ?? '',
            className: statusBar.className,
          }
        : null,
      placeholder: placeholder
        ? {
            hidden: placeholder.hidden,
            state: placeholder.dataset.state ?? '',
            title: placeholderTitle?.textContent?.trim() ?? '',
            detail: placeholderDetail?.textContent?.trim() ?? '',
          }
        : null,
      errorCopy: {
        button: copyButton
          ? {
              ...visibilityOf(copyButton),
              text: copyButton.textContent?.trim() ?? '',
            }
          : null,
        fallback: copyFallback
          ? {
              ...visibilityOf(copyFallback),
              value: copyFallback.value ?? '',
              selectionStart: copyFallback.selectionStart,
              selectionEnd: copyFallback.selectionEnd,
            }
          : null,
      },
      canvas: canvas
        ? {
          width: canvas.width,
          height: canvas.height,
          rect: rectOf(canvas),
        }
        : null,
      overlayPadding: overlayStyle
        ? {
            top: Number.parseFloat(overlayStyle.paddingTop),
            right: Number.parseFloat(overlayStyle.paddingRight),
            bottom: Number.parseFloat(overlayStyle.paddingBottom),
            left: Number.parseFloat(overlayStyle.paddingLeft),
          }
        : null,
      main: mainStyle
        ? {
            flexDirection: mainStyle.flexDirection,
          }
        : null,
      jscoqPanel: jscoqPanel
        ? {
            rect: rectOf(jscoqPanel),
            ideWrapper: ideWrapper
              ? {
                  rect: rectOf(ideWrapper),
                  display: ideWrapperStyle?.display ?? '',
                  flexDirection: ideWrapperStyle?.flexDirection ?? '',
                }
              : null,
            editor: jscoqEditor
              ? {
                  rect: rectOf(jscoqEditor),
                }
              : null,
            panelWrapper: panelWrapper
              ? {
                  rect: rectOf(panelWrapper),
                }
              : null,
            toolbar: toolbar
              ? {
                  rect: rectOf(toolbar),
                  buttonCount: toolbar.querySelectorAll('#buttons button').length,
                  buttons: Array.from(toolbar.querySelectorAll('#buttons button')).map(rectOf),
                }
              : null,
            goalPanel: flexPanelState(goalPanel),
            queryPanel: flexPanelState(queryPanel),
            packagesPanel: flexPanelState(packagesPanel),
            helpPanel: flexPanelState(helpPanel),
          }
        : null,
      lowerPanel: {
        shell: lowerPanelShell
          ? {
              ...visibilityOf(lowerPanelShell),
              rect: rectOf(lowerPanelShell),
            }
          : null,
        header: rectOf(lowerPanelHeader),
        label: lowerPanelLabel
          ? {
              ...visibilityOf(lowerPanelLabel),
              text: lowerPanelLabel.textContent?.trim() ?? '',
            }
          : null,
        title: lowerPanelTitle
          ? {
              ...visibilityOf(lowerPanelTitle),
              rect: rectOf(lowerPanelTitle),
              text: lowerPanelTitle.textContent?.trim() ?? '',
            }
          : null,
        copy: lowerPanelCopy
          ? {
              ...visibilityOf(lowerPanelCopy),
              text: lowerPanelCopy.textContent?.trim() ?? '',
            }
          : null,
        focus: lowerPanelFocus
          ? {
              ...visibilityOf(lowerPanelFocus),
              rect: rectOf(lowerPanelFocus),
            }
          : null,
        focusLabel: lowerPanelFocusLabel
          ? {
              ...visibilityOf(lowerPanelFocusLabel),
              text: lowerPanelFocusLabel.textContent?.trim() ?? '',
            }
          : null,
        activeSection:
          lowerPanelSectionButtons.find(button => button.classList.contains('is-active'))?.dataset.lowerPanelSection
          ?? lowerPanelSectionButtons.find(button => button.getAttribute('aria-pressed') === 'true')?.dataset.lowerPanelSection
          ?? null,
        buttons: lowerPanelSectionButtons.map(button => ({
          ...visibilityOf(button),
          rect: rectOf(button),
          section: button.dataset.lowerPanelSection ?? '',
          text: button.textContent?.trim() ?? '',
          disabled: button.disabled,
          ariaPressed: button.getAttribute('aria-pressed'),
          className: button.className,
        })),
      },
      resizeHandle: resizeHandle
        ? {
            rect: rectOf(resizeHandle),
            orientation: resizeHandle.getAttribute('aria-orientation'),
            valueMin: resizeHandle.getAttribute('aria-valuemin'),
            valueMax: resizeHandle.getAttribute('aria-valuemax'),
            valueNow: resizeHandle.getAttribute('aria-valuenow'),
            valueText: resizeHandle.getAttribute('aria-valuetext'),
          }
        : null,
      hints: {
        desktop: visibilityOf(desktopHint),
        mobile: visibilityOf(mobileHint),
      },
      touchControls: {
        ...visibilityOf(touchControls),
        movePad: rectOf(movePad),
        lookPad: rectOf(lookPad),
        jumpButton: rectOf(jumpButton),
      },
      buildInfo,
      errorReport,
      bspParseDiagnostics,
      rocqSyncDiagnostics,
      assetCount: assetMap?.size ?? null,
      jscoqLoaded: Boolean(document.querySelector('.CodeMirror')),
    };
  });
}

async function gatherSnapshotWithRetry(page, attempts = 10) {
  let lastError = null;

  for (let attempt = 0; attempt < attempts; attempt++) {
    try {
      return await gatherSnapshot(page);
    } catch (error) {
      lastError = error;
      if (!String(error?.message ?? '').includes('Execution context was destroyed')) {
        throw error;
      }
      await page.waitForLoadState('domcontentloaded').catch(() => {});
      await page.waitForTimeout(250);
    }
  }

  throw lastError;
}

function hasEvent(consoleEvents, pattern) {
  return consoleEvents.some(event => pattern.test(event.text));
}

function findEvent(consoleEvents, predicate) {
  return consoleEvents.find(predicate) ?? null;
}

function formatEventLocation(event) {
  const url = event.location?.url;
  const lineNumber = event.location?.lineNumber;
  const columnNumber = event.location?.columnNumber;
  if (!url) return '';
  const line = Number.isInteger(lineNumber) ? lineNumber + 1 : null;
  const column = Number.isInteger(columnNumber) ? columnNumber + 1 : null;
  if (line !== null && column !== null) {
    return ` @ ${url}:${line}:${column}`;
  }
  if (line !== null) {
    return ` @ ${url}:${line}`;
  }
  return ` @ ${url}`;
}

function summarizeEvent(event) {
  if (!event) return '';
  const text = String(event.text ?? '').trim();
  if (event.kind === 'pageerror') {
    const stack = String(event.stack ?? '').trim();
    if (stack) {
      return `${text}\n${stack}`;
    }
  }
  return `${text}${formatEventLocation(event)}`;
}

function detectRocqStartupFailure(consoleEvents) {
  return findEvent(
    consoleEvents,
    event =>
      ROCQ_STARTUP_FAILURE_RE.test(event.text) ||
      (event.kind === 'console' && event.type === 'error' && /CoqExn/i.test(event.text))
  );
}

function detectFailure(snapshot, consoleEvents) {
  const rocqStartupFailure = detectRocqStartupFailure(consoleEvents);
  if (rocqStartupFailure) {
    return `rocq-startup-failed: ${summarizeEvent(rocqStartupFailure)}`;
  }
  if (hasEvent(consoleEvents, BOOTSTRAP_FAILURE_RE)) {
    return 'jscoq-bootstrap-failed';
  }
  if (hasEvent(consoleEvents, RENDER_FAILURE_RE)) {
    return 'render-startup-failed';
  }
  if (snapshot.status?.className === 'error') {
    return 'status-bar-error';
  }
  return null;
}

function detectStalledRocqSync(snapshot) {
  const statusText = snapshot?.status?.text ?? '';
  const placeholder = snapshot?.placeholder ?? null;
  if (statusText !== 'Syncing Rocq render state…') {
    return null;
  }
  if (snapshot?.status?.hidden !== false) {
    return null;
  }
  if (placeholder?.hidden !== false || placeholder.state !== 'loading') {
    return null;
  }
  if (placeholder.title !== 'Syncing Rocq render state…') {
    return null;
  }
  return (
    'rocq-sync-stalled: ' +
    `status="${statusText}", ` +
    `detail="${placeholder.detail || '(empty)'}"`
  );
}

function summarizeBspParseState(snapshot) {
  const diagnostics = snapshot?.bspParseDiagnostics ?? null;
  if (!diagnostics) return 'parseDiagnostics=(missing)';

  const parts = [
    `state="${diagnostics.state ?? '(missing)'}"`,
    `map="${diagnostics.mapLabel ?? '(missing)'}"`,
  ];
  if (Number.isFinite(diagnostics.totalDurationMs)) {
    parts.push(`durationMs=${Math.round(diagnostics.totalDurationMs)}`);
  }
  if (diagnostics.lastEvent?.stage) {
    parts.push(`lastEvent="${diagnostics.lastEvent.stage}"`);
  }
  return parts.join(', ');
}

function detectStalledBspParse(snapshot) {
  const statusText = snapshot?.status?.text ?? '';
  const placeholder = snapshot?.placeholder ?? null;
  const placeholderTitle = String(placeholder?.title ?? '').trim();
  if (statusText !== 'Parsing BSP…') {
    return null;
  }
  if (snapshot?.status?.hidden !== false) {
    return null;
  }
  if (placeholder?.hidden !== false || placeholder.state !== 'loading') {
    return null;
  }
  if (!placeholderTitle.startsWith('Parsing ') || !placeholderTitle.endsWith(' BSP…')) {
    return null;
  }
  return `bsp-parse-stalled: ${summarizeBspParseState(snapshot)}`;
}

async function waitForScenario(page, consoleEvents, predicate, timeoutFailure = null, stopOnFailure = true, timeoutMs = TIMEOUT_MS) {
  const deadline = Date.now() + timeoutMs;
  let snapshot = await gatherSnapshotWithRetry(page);

  while (Date.now() < deadline) {
    if (predicate(snapshot, consoleEvents) || (stopOnFailure && detectFailure(snapshot, consoleEvents))) {
      return snapshot;
    }
    await page.waitForTimeout(POLL_MS);
    snapshot = await gatherSnapshotWithRetry(page);
  }

  const timeoutMessage = timeoutFailure?.(snapshot, consoleEvents);
  if (timeoutMessage) {
    throw new Error(timeoutMessage);
  }
  return snapshot;
}

function attachEventCapture(page, consoleEvents) {
  page.on('console', msg => {
    const location = msg.location();
    consoleEvents.push({
      kind: 'console',
      type: msg.type(),
      text: msg.text(),
      location: location?.url
        ? {
            url: location.url,
            lineNumber: location.lineNumber,
            columnNumber: location.columnNumber,
          }
        : null,
    });
  });
  page.on('pageerror', error => {
    consoleEvents.push({
      kind: 'pageerror',
      text: error.message,
      stack: error.stack ?? '',
    });
  });
  page.on('requestfailed', request => {
    consoleEvents.push({
      kind: 'requestfailed',
      text: `${request.method()} ${request.url()} :: ${request.failure()?.errorText ?? 'unknown failure'}`,
    });
  });
}

function assertNoAssetsScenario(snapshot, consoleEvents) {
  const failure = detectFailure(snapshot, consoleEvents);
  if (failure) {
    throw new Error(failure);
  }
  if (!snapshot.jscoqLoaded) {
    throw new Error('JsCoq editor did not load');
  }
  if (!snapshot.status?.hidden) {
    throw new Error(`status bar stayed visible: ${snapshot.status?.text ?? '(empty)'}`);
  }
  if (snapshot.assetCount !== 0) {
    throw new Error(`expected no assets, got ${snapshot.assetCount}`);
  }
  if (snapshot.placeholder?.hidden !== false) {
    throw new Error('placeholder should stay visible when no playable BSP is available');
  }
  if (snapshot.placeholder?.state !== 'idle') {
    throw new Error(`expected idle placeholder state, got ${snapshot.placeholder?.state ?? '(missing)'}`);
  }
  if (snapshot.placeholder?.title !== 'No playable BSP found') {
    throw new Error(`unexpected no-assets placeholder title: ${snapshot.placeholder?.title ?? '(missing)'}`);
  }
  if (!snapshot.placeholder?.detail.includes('make stage-pages-map')) {
    throw new Error(`unexpected no-assets placeholder detail: ${snapshot.placeholder?.detail ?? '(missing)'}`);
  }
  if (!snapshot.placeholder?.detail.includes('make assets DEMO=')) {
    throw new Error(`unexpected no-assets placeholder detail: ${snapshot.placeholder?.detail ?? '(missing)'}`);
  }
  if (!snapshot.canvas || snapshot.canvas.width <= 0 || snapshot.canvas.height <= 0) {
    throw new Error('game canvas never reached a drawable size in the no-assets scenario');
  }
}

function assertRenderStartupScenario(snapshot, consoleEvents) {
  const failure = detectFailure(snapshot, consoleEvents);
  if (failure) {
    throw new Error(failure);
  }
  if (!snapshot.jscoqLoaded) {
    throw new Error('JsCoq editor did not load');
  }
  if (!snapshot.status?.hidden) {
    throw new Error(`status bar stayed visible: ${snapshot.status?.text ?? '(empty)'}`);
  }
  if (snapshot.assetCount !== 1) {
    throw new Error(`expected one licensed map asset, got ${snapshot.assetCount}`);
  }
  if (snapshot.placeholder?.hidden !== true) {
    throw new Error('placeholder never hid after licensed-map render startup');
  }
  if (snapshot.placeholder?.state !== 'ready') {
    throw new Error(`expected ready placeholder state after render, got ${snapshot.placeholder?.state ?? '(missing)'}`);
  }
  if (!snapshot.canvas || snapshot.canvas.width <= 0 || snapshot.canvas.height <= 0) {
    throw new Error('game canvas never reached a drawable size');
  }
  if (!hasEvent(consoleEvents, SUCCESSFUL_RENDER_RE)) {
    throw new Error('render pipeline never reported a Rocq-seeded frame');
  }
}

function assertDesktopRenderStartupScenario(snapshot, consoleEvents) {
  assertRenderStartupScenario(snapshot, consoleEvents);
  if (snapshot.pointer?.coarse) {
    throw new Error('desktop render scenario unexpectedly reported a coarse pointer');
  }
  if (snapshot.touchControls?.visible) {
    throw new Error('desktop render scenario unexpectedly showed touch controls');
  }
  if (!snapshot.hints?.desktop?.visible) {
    throw new Error('desktop hint should stay visible in desktop render scenario');
  }
}

const LOWER_PANEL_SECTIONS = ['goals', 'messages', 'packages', 'help'];

function getLowerPanelButton(snapshot, section) {
  return snapshot?.lowerPanel?.buttons?.find(button => button.section === section) ?? null;
}

function assertLowerPanelChrome(snapshot, pointerMode) {
  const lowerPanel = snapshot?.lowerPanel;
  if (!lowerPanel?.shell?.visible) {
    throw new Error('lower-panel shell should be visible');
  }
  if (!lowerPanel?.title?.visible) {
    throw new Error('lower-panel title should be visible');
  }
  if (!lowerPanel?.focus?.visible) {
    throw new Error('lower-panel focus controls should be visible');
  }

  const sections = lowerPanel.buttons?.map(button => button.section) ?? [];
  if (JSON.stringify(sections) !== JSON.stringify(LOWER_PANEL_SECTIONS)) {
    throw new Error(`unexpected lower-panel button set: [${sections.join(', ')}]`);
  }

  lowerPanel.buttons.forEach(button => {
    if (!button.visible) {
      throw new Error(`lower-panel ${button.section} button should be visible`);
    }
    if (button.disabled) {
      throw new Error(`lower-panel ${button.section} button should be enabled`);
    }
  });

  if (pointerMode === 'mobile') {
    if (lowerPanel.label?.visible) {
      throw new Error('mobile lower-panel label should stay hidden');
    }
    if (lowerPanel.focusLabel?.visible) {
      throw new Error('mobile lower-panel focus label should stay hidden');
    }
    if (lowerPanel.copy?.visible) {
      throw new Error('mobile lower-panel copy should stay hidden');
    }
    lowerPanel.buttons.forEach(button => {
      assertNearTouchTarget(`mobile lower-panel ${button.section} button`, button.rect);
    });
  } else if (pointerMode === 'desktop') {
    if (!lowerPanel.label?.visible) {
      throw new Error('desktop lower-panel label should stay visible');
    }
    if (!lowerPanel.copy?.visible) {
      throw new Error('desktop lower-panel copy should stay visible');
    }
  }
}

function assertLowerPanelActiveSection(snapshot, expectedSection) {
  assertLowerPanelChrome(snapshot, snapshot?.pointer?.coarse ? 'mobile' : 'desktop');

  if (snapshot.lowerPanel?.activeSection !== expectedSection) {
    throw new Error(
      `expected active lower-panel section ${expectedSection}, got ${snapshot.lowerPanel?.activeSection ?? '(missing)'}`
    );
  }

  LOWER_PANEL_SECTIONS.forEach(section => {
    const button = getLowerPanelButton(snapshot, section);
    if (!button) {
      throw new Error(`lower-panel ${section} button diagnostics missing`);
    }
    const expectedPressed = section === expectedSection ? 'true' : 'false';
    if (button.ariaPressed !== expectedPressed) {
      throw new Error(
        `expected lower-panel ${section} button aria-pressed=${expectedPressed}, got ${button.ariaPressed ?? '(missing)'}`
      );
    }
  });
}

function assertLowerPanelPanelsForSection(snapshot, expectedSection) {
  const panelHasOpenBody = panel => {
    const contentHeight = panel?.rect?.height ?? 0;
    const panelHeight = panel?.panelRect?.height ?? 0;
    const captionHeight = panel?.captionRect?.height ?? 0;
    return contentHeight > 2 || panelHeight > captionHeight + 8;
  };

  if (expectedSection === 'goals' && !panelHasOpenBody(snapshot?.jscoqPanel?.goalPanel)) {
    throw new Error('goals focus should keep the goal panel visibly open');
  }

  if (expectedSection === 'help' && !panelHasOpenBody(snapshot?.jscoqPanel?.helpPanel)) {
    throw new Error('help focus should open the help panel');
  }

  if (expectedSection !== 'help' && panelHasOpenBody(snapshot?.jscoqPanel?.helpPanel)) {
    throw new Error('help panel should close when another lower-panel section is focused');
  }
}

function assertLowerPanelSectionSwitcherInteraction(interactions) {
  if (!interactions) {
    throw new Error('lower-panel section-switcher interactions missing');
  }

  LOWER_PANEL_SECTIONS.forEach(section => {
    const snapshot = interactions[section];
    if (!snapshot) {
      throw new Error(`lower-panel ${section} interaction snapshot missing`);
    }
    assertLowerPanelActiveSection(snapshot, section);
    assertLowerPanelPanelsForSection(snapshot, section);
  });
}

function assertKeyboardResizeInteraction(interaction) {
  if (!interaction) {
    throw new Error('keyboard resize interaction missing');
  }

  const beforeWidth = interaction.before?.jscoqPanel?.rect?.width;
  const afterGrowWidth = interaction.afterGrow?.jscoqPanel?.rect?.width;
  const afterRestoreWidth = interaction.afterRestore?.jscoqPanel?.rect?.width;
  if (!Number.isFinite(beforeWidth) || !Number.isFinite(afterGrowWidth) || !Number.isFinite(afterRestoreWidth)) {
    throw new Error('keyboard resize interaction missing panel widths');
  }

  if (interaction.before?.resizeHandle?.orientation !== 'vertical') {
    throw new Error(
      `desktop resize handle should be vertical, got ${interaction.before?.resizeHandle?.orientation ?? '(missing)'}`
    );
  }

  if (afterGrowWidth <= beforeWidth + 10) {
    throw new Error('keyboard resize did not grow the desktop lower panel');
  }

  if (afterRestoreWidth >= afterGrowWidth - 10) {
    throw new Error('keyboard resize did not restore the desktop lower panel');
  }

  const beforeValue = Number.parseFloat(interaction.before?.resizeHandle?.valueNow ?? 'NaN');
  const afterGrowValue = Number.parseFloat(interaction.afterGrow?.resizeHandle?.valueNow ?? 'NaN');
  if (!Number.isFinite(beforeValue) || !Number.isFinite(afterGrowValue) || afterGrowValue <= beforeValue) {
    throw new Error('keyboard resize handle aria-valuenow did not increase');
  }
}

function assertRealBridgeParseHandoffScenario(snapshot, consoleEvents) {
  const failure = detectFailure(snapshot, consoleEvents);
  if (failure) {
    throw new Error(failure);
  }
  if (!snapshot.jscoqLoaded) {
    throw new Error('JsCoq editor did not load');
  }
  if (snapshot.assetCount !== 1) {
    throw new Error(`expected one licensed map asset, got ${snapshot.assetCount}`);
  }

  const diagnostics = snapshot.bspParseDiagnostics;
  if (!diagnostics) {
    throw new Error('BSP parse diagnostics were not captured');
  }
  if (diagnostics.state !== 'ready') {
    throw new Error(`expected BSP parse diagnostics to be ready, got ${diagnostics.state ?? '(missing)'}`);
  }
  if (!Number.isFinite(diagnostics.totalDurationMs) || diagnostics.totalDurationMs <= 0) {
    throw new Error(`unexpected BSP parse duration: ${diagnostics.totalDurationMs ?? '(missing)'}`);
  }
  if ((diagnostics.summary?.faceCount ?? 0) <= 0) {
    throw new Error(`unexpected BSP face count: ${diagnostics.summary?.faceCount ?? '(missing)'}`);
  }
  if ((diagnostics.summary?.lightmapCount ?? 0) <= 0) {
    throw new Error(`unexpected BSP lightmap count: ${diagnostics.summary?.lightmapCount ?? '(missing)'}`);
  }
  if (diagnostics.lastEvent?.stage !== 'parse:complete') {
    throw new Error(`unexpected BSP parse last event: ${diagnostics.lastEvent?.stage ?? '(missing)'}`);
  }

  if (snapshot.status?.hidden !== false) {
    throw new Error('status bar hid before Rocq sync started');
  }
  if (snapshot.status?.text !== 'Syncing Rocq render state…') {
    throw new Error(`expected Rocq sync status after BSP parse, got ${snapshot.status?.text ?? '(empty)'}`);
  }
  if (snapshot.status?.className !== 'loading') {
    throw new Error(`expected loading status during Rocq handoff, got ${snapshot.status?.className ?? '(missing)'}`);
  }

  if (snapshot.placeholder?.hidden !== false || snapshot.placeholder?.state !== 'loading') {
    throw new Error('placeholder should stay visible while Rocq sync is loading');
  }
  if (snapshot.placeholder?.title !== 'Syncing Rocq render state…') {
    throw new Error(`unexpected placeholder title after parse handoff: ${snapshot.placeholder?.title ?? '(missing)'}`);
  }
  if (!snapshot.placeholder?.detail.includes('verified game core')) {
    throw new Error(`unexpected placeholder detail after parse handoff: ${snapshot.placeholder?.detail ?? '(missing)'}`);
  }

  if (!hasEvent(consoleEvents, /orly: parsed BSP/i)) {
    throw new Error('console never reported a parsed BSP before the Rocq handoff');
  }
}

// Asserts that the full BspCore.v theory — proofs included — compiled
// successfully under JsCoq.
// Key checks:
//   • compile:sentence events were emitted, confirming JsCoq compiled the
//     theory on the fly (not from a preloaded .vo cache).
//   • The sentence count is high enough to prove proof lemmas were processed
//     (BspBinary.v's first Lemma is sentence ~33; by sentence 100 we are
//     well into proof territory across all three bundled theories).
//   • load_world:helpers-ready fired, meaning every helper definition the
//     bridge depends on was compiled without a Rocq error.
//
// Render completion (placeholder hidden, canvas live, load_world:complete) is
// intentionally NOT checked here.  On constrained CI hardware the Rocq
// eval queries that follow helpers-ready can take longer than the 60 s
// inactivity timeout, causing a render-startup-failed that has nothing to do
// with theory correctness.  Render startup is covered by the dedicated
// licensed-map render-startup scenarios.
function assertFullTheoryWithProofsCompilesScenario(snapshot, consoleEvents) {
  if (!snapshot.jscoqLoaded) {
    throw new Error('full-theory compile: JsCoq editor did not load');
  }

  const events = Array.isArray(snapshot.rocqSyncDiagnostics?.events)
    ? snapshot.rocqSyncDiagnostics.events
    : [];

  if (!events.some(e => e.stage === 'load_world:helpers-ready')) {
    // Surface any non-render failure to give a meaningful diagnosis.
    const failure = detectFailure(snapshot, consoleEvents);
    if (failure && !failure.startsWith('render-startup-failed')) {
      throw new Error(`full-theory compile: ${failure}`);
    }
    throw new Error(
      'full-theory compile: load_world:helpers-ready never fired — ' +
      'theory did not finish compiling or JsCoq worker stalled'
    );
  }

  const sentenceEvents = events.filter(e => e.stage === 'compile:sentence');
  if (sentenceEvents.length < 100) {
    const stages = events.map(e => e.stage).join(', ') || '(none)';
    throw new Error(
      `full-theory compile: expected at least 100 compile:sentence events (proves proofs were compiled), ` +
      `got ${sentenceEvents.length}; all stages: ${stages}`
    );
  }
}

function assertDeployedPagesScenario(snapshot, consoleEvents, interactions) {
  const assetChecks = interactions.deployedAssetChecks;
  if (!assetChecks) {
    throw new Error('deployed asset diagnostics missing');
  }

  if (!assetChecks.manifestHead?.ok) {
    throw new Error(`deployed manifest HEAD failed: HTTP ${assetChecks.manifestHead?.status ?? 'unknown'}`);
  }
  if (!assetChecks.mapHead?.ok) {
    throw new Error(`deployed BSP HEAD failed: HTTP ${assetChecks.mapHead?.status ?? 'unknown'}`);
  }
  if (!assetChecks.mapGet?.ok) {
    throw new Error(`deployed BSP GET failed: HTTP ${assetChecks.mapGet?.status ?? 'unknown'}`);
  }

  const magic = assetChecks.mapGet.firstBytes ?? [];
  if (JSON.stringify(magic) !== JSON.stringify(BSP_MAGIC_BYTES)) {
    throw new Error(`deployed BSP magic mismatch: got [${magic.join(', ')}]`);
  }

  const cacheControl = assetChecks.mapHead.headers['cache-control'] ?? '';
  if (!/\bmax-age=\d+/.test(cacheControl)) {
    throw new Error(`deployed BSP is not cacheable: ${cacheControl || '(missing cache-control)'}`);
  }

  const etag = assetChecks.mapHead.headers.etag ?? assetChecks.mapGet.headers.etag ?? '';
  if (!etag) {
    throw new Error('deployed BSP is missing an ETag for cache revalidation');
  }

  if (assetChecks.revalidateHead?.status !== 304) {
    throw new Error(
      `deployed BSP conditional HEAD should return 304, got ${assetChecks.revalidateHead?.status ?? 'unknown'}`
    );
  }

  const failure = detectFailure(snapshot, consoleEvents);
  if (!failure) {
    assertDesktopRenderStartupScenario(snapshot, consoleEvents);
    return;
  }

  const copy = interactions.copyOverlay;
  if (!copy) {
    throw new Error(`${failure}\ndeployed error overlay was not captured`);
  }

  const capturedText = copy.fallbackText || copy.clipboardText || '';
  if (capturedText.length === 0) {
    throw new Error(`${failure}\ndeployed error overlay copy payload was empty`);
  }
  if (!capturedText.includes('Page URL: https://rhencke.github.io/orly/')) {
    throw new Error(`${failure}\ndeployed error overlay copy payload was missing the page URL`);
  }
  if (!capturedText.includes('Source: ')) {
    throw new Error(`${failure}\ndeployed error overlay copy payload was missing the error source`);
  }

  throw new Error(`${failure}\nCaptured deployed error report:\n${capturedText}`);
}

function assertRectWithinViewport(name, rect, viewport) {
  if (!rect) {
    throw new Error(`${name} rect missing`);
  }
  if (rect.left < -1 || rect.top < -1 ||
      rect.right > viewport.width + 1 || rect.bottom > viewport.height + 1) {
    throw new Error(`${name} fell outside the viewport`);
  }
}

function assertTouchTarget(name, rect) {
  if (!rect) {
    throw new Error(`${name} rect missing`);
  }
  if (rect.width < MIN_TOUCH_TARGET_PX || rect.height < MIN_TOUCH_TARGET_PX) {
    throw new Error(`${name} target smaller than ${MIN_TOUCH_TARGET_PX}px`);
  }
}

function assertNearTouchTarget(name, rect, tolerance = 1) {
  if (!rect) {
    throw new Error(`${name} rect missing`);
  }
  const minimum = MIN_TOUCH_TARGET_PX - tolerance;
  if (rect.width < minimum || rect.height < minimum) {
    throw new Error(`${name} target smaller than ${minimum}px`);
  }
}

function assertCollapsedFlexPanel(name, panel) {
  if (!panel) {
    throw new Error(`${name} diagnostics missing`);
  }
  if (!panel.collapsed) {
    throw new Error(`${name} should start collapsed on mobile`);
  }
  if ((panel.rect?.height ?? 0) > 2) {
    throw new Error(`${name} content stayed open on mobile`);
  }
}

function assertMobileLowerPanelUsability(snapshot, orientation) {
  const jscoqPanel = snapshot.jscoqPanel;
  const panelRect = jscoqPanel?.rect;
  const layout = jscoqPanel?.ideWrapper;
  const editorRect = jscoqPanel?.editor?.rect;
  const panelWrapperRect = jscoqPanel?.panelWrapper?.rect;
  const toolbar = jscoqPanel?.toolbar;
  const toolbarRect = toolbar?.rect;
  const goalPanel = jscoqPanel?.goalPanel;

  if (!panelRect || !layout || !editorRect || !panelWrapperRect || !toolbarRect || !goalPanel?.rect) {
    throw new Error('mobile lower-panel diagnostics missing');
  }

  assertLowerPanelChrome(snapshot, 'mobile');
  assertLowerPanelActiveSection(snapshot, 'goals');

  if (layout.display !== 'flex' || layout.flexDirection !== 'column') {
    throw new Error(
      `mobile lower panel should stack beneath the editor, got ${layout.display}/${layout.flexDirection}`
    );
  }

  if (panelWrapperRect.top < layout.rect.top + layout.rect.height * 0.35) {
    throw new Error('mobile lower panel did not move into the lower portion of the card');
  }

  if (panelWrapperRect.width < panelRect.width * 0.8) {
    throw new Error('mobile lower panel lost too much horizontal space');
  }

  if (Math.abs(panelWrapperRect.width - editorRect.width) > 24) {
    throw new Error('mobile lower panel width drifted too far from the editor width');
  }

  if (panelWrapperRect.height < 96) {
    throw new Error('mobile lower panel became too short to be useful');
  }

  const maxPanelFraction = orientation === 'portrait' ? 0.72 : 0.6;
  if (panelWrapperRect.height > panelRect.height * maxPanelFraction) {
    throw new Error(`${orientation} lower panel consumed too much of the phone panel`);
  }

  if (toolbarRect.height < 28 || toolbarRect.height > 52) {
    throw new Error(`mobile lower-panel toolbar height is out of bounds: ${toolbarRect.height}`);
  }

  if ((toolbar.buttonCount ?? 0) < 4) {
    throw new Error('mobile lower-panel toolbar is missing core controls');
  }

  if (goalPanel.rect.height < 44) {
    throw new Error('mobile lower-panel goal area became too small to read');
  }

  assertNearTouchTarget('mobile goal caption', jscoqPanel.goalPanel?.captionRect);
  assertNearTouchTarget('mobile messages caption', jscoqPanel.queryPanel?.captionRect);
  assertNearTouchTarget('mobile packages caption', jscoqPanel.packagesPanel?.captionRect);

  assertCollapsedFlexPanel('mobile message panel', jscoqPanel.queryPanel);
  assertCollapsedFlexPanel('mobile packages panel', jscoqPanel.packagesPanel);

  if (!jscoqPanel.helpPanel?.collapsed) {
    throw new Error('mobile help panel should start collapsed');
  }
}

function assertMobileRenderStartupScenario(snapshot, consoleEvents, orientation) {
  assertRenderStartupScenario(snapshot, consoleEvents);
  if (!snapshot.pointer?.coarse) {
    throw new Error('mobile render scenario did not report a coarse pointer');
  }
  if (!snapshot.touchControls?.visible) {
    throw new Error('mobile render scenario did not show touch controls');
  }
  if (!snapshot.hints?.mobile?.visible || snapshot.hints?.desktop?.visible) {
    throw new Error('mobile hints did not switch correctly for coarse pointers');
  }

  assertTouchTarget('move pad', snapshot.touchControls.movePad);
  assertTouchTarget('look pad', snapshot.touchControls.lookPad);
  assertTouchTarget('jump button', snapshot.touchControls.jumpButton);

  if (snapshot.touchControls.lookPad.width < snapshot.touchControls.movePad.width) {
    throw new Error('look pad should be at least as wide as the move pad on mobile');
  }

  assertRectWithinViewport('move pad', snapshot.touchControls.movePad, snapshot.viewport);
  assertRectWithinViewport('look pad', snapshot.touchControls.lookPad, snapshot.viewport);
  assertRectWithinViewport('jump button', snapshot.touchControls.jumpButton, snapshot.viewport);
  assertRectWithinViewport('resize handle', snapshot.resizeHandle?.rect, snapshot.viewport);

  if (!snapshot.overlayPadding ||
      snapshot.overlayPadding.top < MIN_SAFE_AREA_PADDING_PX ||
      snapshot.overlayPadding.right < MIN_SAFE_AREA_PADDING_PX ||
      snapshot.overlayPadding.bottom < MIN_SAFE_AREA_PADDING_PX ||
      snapshot.overlayPadding.left < MIN_SAFE_AREA_PADDING_PX) {
    throw new Error('mobile overlay padding did not preserve safe-area spacing');
  }

  if (!snapshot.canvas?.rect || !snapshot.jscoqPanel?.rect) {
    throw new Error('mobile render scenario missing canvas or JsCoq panel bounds');
  }

  if (orientation === 'portrait') {
    if (snapshot.main?.flexDirection !== 'column') {
      throw new Error(`expected portrait layout to stack panels, got ${snapshot.main?.flexDirection}`);
    }
    if (snapshot.canvas.rect.height < 200) {
      throw new Error('portrait canvas became too short for playability');
    }
  } else if (orientation === 'landscape') {
    if (snapshot.main?.flexDirection !== 'row') {
      throw new Error(`expected landscape layout to split horizontally, got ${snapshot.main?.flexDirection}`);
    }
    if (snapshot.canvas.rect.width < 240) {
      throw new Error('landscape canvas became too narrow for playability');
    }
  }

  assertMobileLowerPanelUsability(snapshot, orientation);
}

function assertErrorOverlayCopyScenario(snapshot, consoleEvents, interactions) {
  assertNoAssetsScenario(interactions.readySnapshot, consoleEvents);

  const copy = interactions.copyOverlay;
  if (!copy) {
    throw new Error('copy overlay diagnostics missing');
  }

  const errorSnapshot = copy.snapshot ?? snapshot;
  if (errorSnapshot.placeholder?.state !== 'error') {
    throw new Error(`expected error placeholder state, got ${errorSnapshot.placeholder?.state ?? '(missing)'}`);
  }
  if (errorSnapshot.placeholder?.title !== 'Browser startup failed') {
    throw new Error(`unexpected error placeholder title: ${errorSnapshot.placeholder?.title ?? '(missing)'}`);
  }
  if (!errorSnapshot.placeholder?.detail.includes('Copy smoke error')) {
    throw new Error(`unexpected error placeholder detail: ${errorSnapshot.placeholder?.detail ?? '(missing)'}`);
  }
  if (errorSnapshot.status?.className !== 'error') {
    throw new Error(`expected status bar error class, got ${errorSnapshot.status?.className ?? '(missing)'}`);
  }
  if (!errorSnapshot.status?.text.includes('Copy smoke error')) {
    throw new Error(`unexpected status bar text: ${errorSnapshot.status?.text ?? '(missing)'}`);
  }
  if (!errorSnapshot.errorCopy?.button?.visible) {
    throw new Error('copy button did not become visible in error state');
  }
  if (errorSnapshot.errorCopy?.button?.text !== 'Copy') {
    throw new Error(`copy button did not reset label: ${errorSnapshot.errorCopy?.button?.text ?? '(missing)'}`);
  }
  if (!errorSnapshot.errorCopy?.fallback?.visible) {
    throw new Error('fallback textarea stayed hidden after clipboard API removal');
  }
  if (errorSnapshot.errorCopy?.fallback?.selectionStart !== 0) {
    throw new Error(`fallback selection start should be 0, got ${errorSnapshot.errorCopy?.fallback?.selectionStart}`);
  }
  if (errorSnapshot.errorCopy?.fallback?.selectionEnd !== copy.fallbackText.length) {
    throw new Error(
      `fallback selection end should cover full payload, got ${errorSnapshot.errorCopy?.fallback?.selectionEnd}`
    );
  }

  if (errorSnapshot.errorReport?.message !== 'Copy smoke error') {
    throw new Error(`unexpected captured error message: ${errorSnapshot.errorReport?.message ?? '(missing)'}`);
  }
  if (errorSnapshot.errorReport?.build?.gitSha !== 'unknown') {
    throw new Error(`unexpected captured build SHA: ${errorSnapshot.errorReport?.build?.gitSha ?? '(missing)'}`);
  }
  if (errorSnapshot.buildInfo?.source !== 'checked-in-default') {
    throw new Error(`unexpected local build metadata source: ${errorSnapshot.buildInfo?.source ?? '(missing)'}`);
  }

  if (copy.copiedLabel !== 'Copied!') {
    throw new Error(`copy button did not show success label: ${copy.copiedLabel}`);
  }
  if (copy.resetLabel !== 'Copy') {
    throw new Error(`copy button did not reset after feedback: ${copy.resetLabel}`);
  }

  assertClipboardPayload(copy.clipboardText, 'clipboard payload');
  assertClipboardPayload(copy.fallbackText, 'fallback payload');
}

function assertRocqSyncTimeoutScenario(snapshot, consoleEvents, interactions) {
  const failure = detectFailure(snapshot, consoleEvents);
  if (failure && !failure.startsWith('status-bar-error') && !failure.startsWith('render-startup-failed')) {
    throw new Error(failure);
  }

  const copy = interactions.copyOverlay;
  if (!copy) {
    throw new Error('timeout overlay copy diagnostics missing');
  }

  const errorSnapshot = copy.snapshot ?? snapshot;
  if (errorSnapshot.placeholder?.state !== 'error') {
    throw new Error(`expected error placeholder state, got ${errorSnapshot.placeholder?.state ?? '(missing)'}`);
  }
  if (errorSnapshot.placeholder?.title !== 'Rocq render sync timed out') {
    throw new Error(`unexpected timeout placeholder title: ${errorSnapshot.placeholder?.title ?? '(missing)'}`);
  }
  if (!errorSnapshot.placeholder?.detail.includes('Timed out after')) {
    throw new Error(`timeout placeholder detail missing timeout text: ${errorSnapshot.placeholder?.detail ?? '(missing)'}`);
  }
  if (!errorSnapshot.placeholder?.detail.includes('Last bridge event: load_world:waiting')) {
    throw new Error(`timeout placeholder detail missing last bridge event: ${errorSnapshot.placeholder?.detail ?? '(missing)'}`);
  }
  if (errorSnapshot.status?.className !== 'error') {
    throw new Error(`expected error status class, got ${errorSnapshot.status?.className ?? '(missing)'}`);
  }
  if (!errorSnapshot.status?.text.includes('Rocq sync timeout: Timed out after')) {
    throw new Error(`unexpected timeout status text: ${errorSnapshot.status?.text ?? '(missing)'}`);
  }
  if (!errorSnapshot.errorCopy?.button?.visible) {
    throw new Error('copy button did not become visible for timeout overlay');
  }
  if (errorSnapshot.errorReport?.source !== 'rocq-sync-timeout') {
    throw new Error(`unexpected timeout report source: ${errorSnapshot.errorReport?.source ?? '(missing)'}`);
  }
  if (errorSnapshot.errorReport?.diagnostics?.state !== 'timed-out') {
    throw new Error(`unexpected timeout diagnostics state: ${errorSnapshot.errorReport?.diagnostics?.state ?? '(missing)'}`);
  }
  if (errorSnapshot.errorReport?.diagnostics?.lastEvent?.stage !== 'load_world:waiting') {
    throw new Error(
      `unexpected timeout last bridge event: ${errorSnapshot.errorReport?.diagnostics?.lastEvent?.stage ?? '(missing)'}`
    );
  }
  if ((errorSnapshot.errorReport?.diagnostics?.request?.faceCount ?? 0) <= 0) {
    throw new Error(
      `unexpected timeout request face count: ${errorSnapshot.errorReport?.diagnostics?.request?.faceCount ?? '(missing)'}`
    );
  }
  if (errorSnapshot.rocqSyncDiagnostics?.state !== 'timed-out') {
    throw new Error(`unexpected live sync diagnostics state: ${errorSnapshot.rocqSyncDiagnostics?.state ?? '(missing)'}`);
  }

  if (copy.copiedLabel !== 'Copied!') {
    throw new Error(`copy button did not show success label: ${copy.copiedLabel}`);
  }
  if (copy.resetLabel !== 'Copy') {
    throw new Error(`copy button did not reset after feedback: ${copy.resetLabel}`);
  }
  if (errorSnapshot.errorCopy?.fallback?.selectionStart !== 0) {
    throw new Error(
      `fallback selection start should be 0, got ${errorSnapshot.errorCopy?.fallback?.selectionStart}`
    );
  }
  if (errorSnapshot.errorCopy?.fallback?.selectionEnd !== copy.fallbackText.length) {
    throw new Error(
      `fallback selection end should cover full timeout payload, got ${errorSnapshot.errorCopy?.fallback?.selectionEnd}`
    );
  }

  for (const [label, text] of [
    ['timeout clipboard payload', copy.clipboardText],
    ['timeout fallback payload', copy.fallbackText],
  ]) {
    if (!text.includes('Title: Rocq render sync timed out')) {
      throw new Error(`${label} missing timeout title`);
    }
    if (!text.includes('Source: rocq-sync-timeout')) {
      throw new Error(`${label} missing timeout source`);
    }
    if (!text.includes('Rocq sync diagnostics:')) {
      throw new Error(`${label} missing sync diagnostics heading`);
    }
    if (!text.includes('State: timed-out')) {
      throw new Error(`${label} missing timed-out diagnostics state`);
    }
    if (!text.includes('Last bridge event: load_world:waiting')) {
      throw new Error(`${label} missing last bridge event`);
    }
    if (!text.includes('repro bridge intentionally never resolves load_world')) {
      throw new Error(`${label} missing bridge payload reason`);
    }
    if (!text.includes('Request counts: entities=')
        || !text.includes('faces=')
        || !text.includes('textures=')) {
      throw new Error(`${label} missing request count summary`);
    }
  }
}

// Asserts that the activity-based Rocq sync timeout did NOT fire prematurely
// for a slow-but-progressing compilation.  The SLOW_COMPILE_BRIDGE_SOURCE
// emits 6 compile:sentence events at 100 ms intervals (600 ms total); with
// rocq_sync_timeout_ms=500 a flat withTimeout would kill it, but
// withActivityTimeout resets on each event and allows completion.
function assertRocqSyncActivityTimeoutScenario(snapshot, consoleEvents) {
  const failure = detectFailure(snapshot, consoleEvents);
  if (failure) {
    throw new Error(`activity timeout regression unexpectedly detected failure: ${failure}`);
  }
  // Overlay must be hidden — render started, timeout did not fire.
  if (snapshot.placeholder?.hidden !== true) {
    throw new Error(
      `activity timeout: overlay still visible after load_world should have completed — ` +
      `state=${snapshot.placeholder?.state ?? '(missing)'}, ` +
      `detail="${snapshot.placeholder?.detail ?? '(empty)'}"`
    );
  }
  // Diagnostics state must be 'ready', not 'timed-out'.
  if (snapshot.rocqSyncDiagnostics?.state !== 'ready') {
    throw new Error(
      `activity timeout: expected rocq sync diagnostics state 'ready', ` +
      `got '${snapshot.rocqSyncDiagnostics?.state ?? '(missing)'}'`
    );
  }
  // Event history must include at least one compile:sentence event — proves
  // the events arrived and were recorded (not silently dropped).
  const events = Array.isArray(snapshot.rocqSyncDiagnostics?.events)
    ? snapshot.rocqSyncDiagnostics.events
    : [];
  if (!events.some(e => e.stage === 'compile:sentence')) {
    const stages = events.map(e => e.stage).join(', ') || '(none)';
    throw new Error(
      `activity timeout: expected compile:sentence events in rocq sync diagnostics, ` +
      `got: ${stages}`
    );
  }
}

// Asserts that the loading overlay showed per-sentence compilation progress
// while the SLOW_COMPILE_BRIDGE_SOURCE was compiling theory.  The
// readyWhen predicate fires as soon as the detail text shows "Compiling
// game-core theory", so interactions.readySnapshot captures the live state.
function assertRocqSyncCompileProgressOverlayScenario(snapshot, consoleEvents, interactions) {
  const failure = detectFailure(snapshot, consoleEvents);
  if (failure && !failure.startsWith('status-bar-error') && !failure.startsWith('render-startup-failed')) {
    throw new Error(failure);
  }

  const progressSnapshot = interactions.readySnapshot;
  if (!progressSnapshot?.placeholder) {
    throw new Error('compile progress overlay: readySnapshot is missing the placeholder element');
  }
  if (progressSnapshot.placeholder.hidden) {
    throw new Error(
      'compile progress overlay: placeholder was hidden when progress text was expected — ' +
      'compile:sentence events may not be reaching the overlay'
    );
  }
  // Detail must start with the canonical progress prefix.
  const detail = progressSnapshot.placeholder.detail ?? '';
  if (!detail.startsWith('Compiling game-core theory')) {
    throw new Error(
      `compile progress overlay: expected detail to start with ` +
      `"Compiling game-core theory", got: "${detail || '(empty)'}"`
    );
  }
  // Detail must end with "sentence done" or "sentences done".
  if (!detail.includes('sentence') || !detail.includes('done')) {
    throw new Error(
      `compile progress overlay: detail missing "sentence … done" progress text, got: "${detail}"`
    );
  }
  // Title must remain "Syncing Rocq render state\u2026" — we only update the detail.
  if (progressSnapshot.placeholder.title !== 'Syncing Rocq render state\u2026') {
    throw new Error(
      `compile progress overlay: title changed unexpectedly during compile progress, ` +
      `got: "${progressSnapshot.placeholder.title ?? '(empty)'}"`
    );
  }
}

async function dragResizeHandle(page, { deltaX = 0, deltaY = 0 }) {
  const handle = page.locator('#resize-handle');
  const box = await handle.boundingBox();
  if (!box) {
    throw new Error('resize handle is not visible');
  }

  const startX = box.x + box.width / 2;
  const startY = box.y + box.height / 2;
  await page.mouse.move(startX, startY);
  await page.mouse.down();
  await page.mouse.move(startX + deltaX, startY + deltaY, { steps: 8 });
  await page.mouse.up();
  await page.waitForTimeout(150);
}

async function exerciseResizeHandle(page, orientation) {
  const before = await gatherSnapshotWithRetry(page);
  if (orientation === 'portrait') {
    await dragResizeHandle(page, { deltaY: -80 });
  } else {
    await dragResizeHandle(page, { deltaX: -100 });
  }
  const after = await gatherSnapshotWithRetry(page);

  const beforePanel = before.jscoqPanel?.rect;
  const afterPanel = after.jscoqPanel?.rect;
  if (!beforePanel || !afterPanel) {
    throw new Error('resize handle diagnostics missing JsCoq panel bounds');
  }

  if (orientation === 'portrait') {
    if (afterPanel.height <= beforePanel.height + 20) {
      throw new Error('portrait resize handle did not grow the JsCoq panel');
    }
  } else if (afterPanel.width <= beforePanel.width + 20) {
    throw new Error('landscape resize handle did not grow the JsCoq panel');
  }

  return { before, after };
}

async function clickLowerPanelSection(page, section) {
  const button = page.locator(`.lower-panel-section-button[data-lower-panel-section="${section}"]`);
  await button.waitFor({ state: 'visible' });
  await button.click();
  await page.waitForFunction(expectedSection => {
    const activeButton = document.querySelector('.lower-panel-section-button.is-active');
    const sectionFromPanel = panelId => {
      if (panelId === 'goal-panel') return 'goals';
      if (panelId === 'query-panel') return 'messages';
      if (panelId === 'packages-panel') return 'packages';
      if (panelId === 'help-panel') return 'help';
      return null;
    };

    if (activeButton?.dataset.lowerPanelSection !== expectedSection) {
      return false;
    }

    return Array.from(document.querySelectorAll('#panel-wrapper .flex-panel')).every(panel => {
      const section = sectionFromPanel(panel.id);
      if (!section) return true;
      return panel.classList.contains('collapsed') === (section !== expectedSection);
    });
  }, section, { timeout: 10000 });
  await page.waitForTimeout(100);
  return gatherSnapshotWithRetry(page);
}

async function exerciseLowerPanelSectionSwitcher(page) {
  const snapshots = {};
  for (const section of ['goals', 'messages', 'packages', 'help', 'goals']) {
    snapshots[section] = await clickLowerPanelSection(page, section);
  }
  return snapshots;
}

async function exerciseKeyboardResize(page) {
  const handle = page.locator('#resize-handle');
  await handle.focus();
  const before = await gatherSnapshotWithRetry(page);
  await handle.press('ArrowLeft');
  await page.waitForTimeout(100);
  const afterGrow = await gatherSnapshotWithRetry(page);
  await handle.press('ArrowRight');
  await page.waitForTimeout(100);
  const afterRestore = await gatherSnapshotWithRetry(page);
  return { before, afterGrow, afterRestore };
}

async function copyCurrentErrorOverlay(page) {
  const copyButton = page.locator('#copy-error-report');
  await copyButton.waitFor({ state: 'visible' });
  await copyButton.click();

  const clipboardText = await page.evaluate(() => navigator.clipboard.readText());
  const copiedLabel = (await copyButton.textContent())?.trim() ?? '';
  await page.waitForTimeout(1200);
  const resetLabel = (await copyButton.textContent())?.trim() ?? '';

  await page.evaluate(() => {
    Object.defineProperty(navigator, 'clipboard', {
      configurable: true,
      value: undefined,
    });
  });
  await copyButton.click();

  const fallback = page.locator('#error-copy-fallback');
  await fallback.waitFor({ state: 'visible' });
  const fallbackText = await fallback.inputValue();
  const fallbackSelection = await page.evaluate(() => {
    const element = document.getElementById('error-copy-fallback');
    return {
      start: element?.selectionStart ?? null,
      end: element?.selectionEnd ?? null,
    };
  });
  const snapshot = await gatherSnapshotWithRetry(page);

  return {
    clipboardText,
    copiedLabel,
    resetLabel,
    fallbackText,
    fallbackSelection,
    snapshot,
  };
}

async function copyCurrentErrorOverlayIfVisible(page) {
  const copyButton = page.locator('#copy-error-report');
  if (!await copyButton.isVisible().catch(() => false)) {
    return null;
  }
  return copyCurrentErrorOverlay(page);
}

async function exerciseErrorOverlayCopy(page) {
  await page.evaluate(() => {
    const error = new Error('Copy smoke error');
    window.dispatchEvent(new ErrorEvent('error', {
      message: error.message,
      error,
      filename: 'http://example.test/copy.js',
      lineno: 9,
      colno: 5,
    }));
  });

  return copyCurrentErrorOverlay(page);
}

function assertClipboardPayload(text, label = 'clipboard payload') {
  if (!text.startsWith('```text\n')) {
    throw new Error(`${label} should start with a fenced code block`);
  }
  if (!text.includes('Message: Copy smoke error')) {
    throw new Error(`${label} missing error message`);
  }
  if (!text.includes('Stack trace:\nError: Copy smoke error')) {
    throw new Error(`${label} missing stack trace`);
  }
  if (!text.includes('User agent:')) {
    throw new Error(`${label} missing user agent`);
  }
  if (!text.includes('Page URL: http://127.0.0.1:')) {
    throw new Error(`${label} missing page URL`);
  }
  if (!text.includes('Build git SHA: unknown')) {
    throw new Error(`${label} missing build SHA`);
  }
  if (!text.includes('Build source: checked-in-default')) {
    throw new Error(`${label} missing build source`);
  }
  if (!text.includes('Location: http://example.test/copy.js, line 9, column 5')) {
    throw new Error(`${label} missing source location`);
  }
}

async function runScenario(browser, scenario, outDir, port) {
  const scenarioRoot = scenario.url ? null : await createScenarioRoot(scenario.rootScenario ?? scenario.name);
  const serverInfo = scenario.url ? null : startStaticServer(scenarioRoot, port);
  const baseUrl = scenario.url ?? `http://127.0.0.1:${port}/`;
  const url = scenario.query
    ? `${baseUrl}${baseUrl.includes('?') ? '&' : '?'}${scenario.query}`
    : baseUrl;
  const consoleEvents = [];
  let context = null;
  let page = null;
  let interactions = null;

  try {
    await waitForUrl(url, scenario.url ? 30000 : 10000).catch(error => {
      const logs = serverInfo?.readLogs() ?? { stdout: '', stderr: '' };
      throw new Error(
        `${error.message}\nstdout:\n${logs.stdout || '(empty)'}\nstderr:\n${logs.stderr || '(empty)'}`
      );
    });

    context = await browser.newContext(scenario.contextOptions ?? { viewport: { width: 1280, height: 720 } });
    if (Array.isArray(scenario.permissions) && scenario.permissions.length > 0) {
      await context.grantPermissions(scenario.permissions, { origin: new URL(url).origin });
    }
    page = await context.newPage();
    attachEventCapture(page, consoleEvents);

    await page.goto(url, { waitUntil: 'domcontentloaded', timeout: 120000 });
    await page.waitForLoadState('load').catch(() => {});

    const readyWhen = scenario.readyWhen ?? (
      scenario.name === 'browser-load-no-assets'
        ? current => current.jscoqLoaded && current.status?.hidden === true
        : current => current.placeholder?.hidden === true
    );
    const snapshot = await waitForScenario(
      page,
      consoleEvents,
      readyWhen,
      scenario.timeoutFailure ?? null,
      scenario.stopOnFailure ?? true,
      scenario.timeoutMs ?? TIMEOUT_MS
    );

    interactions = {
      readySnapshot: snapshot,
    };
    if (scenario.afterReady) {
      Object.assign(interactions, await scenario.afterReady(page, snapshot, consoleEvents));
    }
    const finalSnapshot = await gatherSnapshotWithRetry(page);

    const screenshotPath = path.join(outDir, `${scenario.name}.png`);
    await page.screenshot({ path: screenshotPath, fullPage: true });

    scenario.assert(finalSnapshot, consoleEvents, interactions);

    return {
      scenario: scenario.name,
      passed: true,
      url,
      snapshot: finalSnapshot,
      interactions,
      consoleEvents,
      serverLogs: serverInfo?.readLogs() ?? null,
      screenshotPath,
    };
  } catch (error) {
    const screenshotPath = path.join(outDir, `${scenario.name}.png`);
    await page?.screenshot({ path: screenshotPath, fullPage: true }).catch(() => {});
    const failureSnapshot = page
      ? await gatherSnapshotWithRetry(page).catch(() => null)
      : null;
    return {
      scenario: scenario.name,
      passed: false,
      url,
      failure: error.message,
      snapshot: failureSnapshot,
      interactions,
      consoleEvents,
      serverLogs: serverInfo?.readLogs() ?? null,
      screenshotPath,
    };
  } finally {
    await context?.close().catch(() => {});
    if (serverInfo) {
      serverInfo.server.kill('SIGTERM');
      await new Promise(resolve => {
        if (serverInfo.server.exitCode !== null) {
          resolve();
        } else {
          serverInfo.server.once('exit', resolve);
        }
      });
    }
    if (scenarioRoot) {
      await fs.rm(scenarioRoot, { recursive: true, force: true }).catch(() => {});
    }
  }
}

async function main() {
  const browser = await chromium.launch({ headless: true });

  try {
    if (SKIP_LOCAL_SCENARIOS && !DEPLOYED_URL) {
      throw new Error('ORLY_REPRO_DEPLOYED_URL is required when ORLY_REPRO_SKIP_LOCAL is set');
    }

    const outDir = await fs.mkdtemp(path.join(os.tmpdir(), 'orly-licensed-map-regression-'));
    const diagnosticsPath = path.join(outDir, 'diagnostics.json');
    const scenarios = [];

    if (!SKIP_LOCAL_SCENARIOS) {
      scenarios.push(await runMissingSentencePromiseRegression());
      scenarios.push(await runCompileSentenceDiagnosticsRegression());
    }

    const scenarioConfigs = [];

    if (!SKIP_LOCAL_SCENARIOS) {
      scenarioConfigs.push(
        {
          name: 'browser-load-no-assets',
          assert(snapshot, consoleEvents) {
            assertNoAssetsScenario(snapshot, consoleEvents);
          },
        },
        {
          name: 'licensed-map-render-startup-desktop',
          rootScenario: 'licensed-map-render-startup',
          contextOptions: {
            viewport: { width: 1280, height: 720 },
          },
          async afterReady(page) {
            return {
              sectionSwitcher: await exerciseLowerPanelSectionSwitcher(page),
              keyboardResize: await exerciseKeyboardResize(page),
            };
          },
          assert(snapshot, consoleEvents, interactions) {
            assertDesktopRenderStartupScenario(interactions.readySnapshot, consoleEvents);
            assertLowerPanelChrome(interactions.readySnapshot, 'desktop');
            assertLowerPanelActiveSection(interactions.readySnapshot, 'goals');
            assertLowerPanelSectionSwitcherInteraction(interactions.sectionSwitcher);
            assertKeyboardResizeInteraction(interactions.keyboardResize);
          },
        },
        {
          name: 'licensed-map-parse-handoff-real-bridge',
          rootScenario: 'licensed-map-parse-handoff',
          contextOptions: {
            viewport: { width: 1280, height: 720 },
          },
          readyWhen(current) {
            return current.bspParseDiagnostics?.state === 'ready'
              && current.status?.text === 'Syncing Rocq render state…'
              && current.placeholder?.title === 'Syncing Rocq render state…';
          },
          assert(snapshot, consoleEvents, interactions) {
            assertRealBridgeParseHandoffScenario(interactions.readySnapshot, consoleEvents);
          },
        },
        {
          name: 'licensed-map-render-startup-mobile-portrait',
          rootScenario: 'licensed-map-render-startup',
          contextOptions: IPHONE_13,
          async afterReady(page) {
            return {
              sectionSwitcher: await exerciseLowerPanelSectionSwitcher(page),
              resize: await exerciseResizeHandle(page, 'portrait'),
            };
          },
          assert(snapshot, consoleEvents, interactions) {
            assertMobileRenderStartupScenario(interactions.readySnapshot, consoleEvents, 'portrait');
            assertLowerPanelSectionSwitcherInteraction(interactions.sectionSwitcher);
          },
        },
        {
          name: 'licensed-map-render-startup-mobile-landscape',
          rootScenario: 'licensed-map-render-startup',
          contextOptions: IPHONE_13_LANDSCAPE,
          async afterReady(page) {
            return {
              resize: await exerciseResizeHandle(page, 'landscape'),
            };
          },
          assert(snapshot, consoleEvents, interactions) {
            assertMobileRenderStartupScenario(interactions.readySnapshot, consoleEvents, 'landscape');
          },
        },
        {
          name: 'browser-error-overlay-copy',
          permissions: ['clipboard-read', 'clipboard-write'],
          readyWhen(current) {
            return current.jscoqLoaded && current.status?.hidden === true && current.placeholder?.state === 'idle';
          },
          async afterReady(page) {
            return {
              copyOverlay: await exerciseErrorOverlayCopy(page),
            };
          },
          assert(snapshot, consoleEvents, interactions) {
            assertErrorOverlayCopyScenario(snapshot, consoleEvents, interactions);
          },
        },
        {
          name: 'browser-rocq-sync-timeout-overlay',
          rootScenario: 'rocq-sync-timeout-overlay',
          permissions: ['clipboard-read', 'clipboard-write'],
          query: 'rocq_sync_timeout_ms=750',
          stopOnFailure: false,
          readyWhen(current) {
            return current.placeholder?.state === 'error'
              && current.placeholder?.title === 'Rocq render sync timed out'
              && current.errorCopy?.button?.visible === true;
          },
          async afterReady(page) {
            return {
              copyOverlay: await copyCurrentErrorOverlay(page),
            };
          },
          assert(snapshot, consoleEvents, interactions) {
            assertRocqSyncTimeoutScenario(snapshot, consoleEvents, interactions);
          },
        },
        {
          // Regression for the activity-based timeout: SLOW_COMPILE_BRIDGE_SOURCE
          // emits 6 compile:sentence events at 100 ms intervals (600 ms total).
          // With rocq_sync_timeout_ms=500 a flat withTimeout would fire at 500 ms
          // and produce a timeout error; withActivityTimeout resets on each event
          // and lets load_world complete.  If this scenario fails with a timeout
          // overlay, withActivityTimeout is broken.
          name: 'browser-rocq-sync-activity-timeout',
          rootScenario: 'slow-compile-overlay',
          query: 'rocq_sync_timeout_ms=500',
          readyWhen(current) {
            return current.placeholder?.hidden === true;
          },
          assert(snapshot, consoleEvents) {
            assertRocqSyncActivityTimeoutScenario(snapshot, consoleEvents);
          },
        },
        {
          // Verifies that BspCore.v — proofs included — compiles to
          // completion in JsCoq without errors.  Uses the real
          // rocq_bridge.js and the real BSP map so the Rocq sync
          // diagnostic events flow (compile:sentence, helpers-ready).
          //
          // readyWhen fires as soon as load_world:helpers-ready appears,
          // which means every bridge-helper definition was compiled
          // successfully.  We stop there deliberately: the Rocq eval
          // queries that follow helpers-ready can exceed the 60 s
          // inactivity timer on slow CI hardware, making the render
          // timeout fire even though theory compilation succeeded.
          // Render startup is validated separately by the
          // licensed-map-render-startup-desktop scenario.
          //
          // In CI the theory takes ~230 s to compile.  timeoutMs is set
          // to 5 minutes so headless CI has breathing room.
          name: 'full-theory-with-proofs-compiles',
          rootScenario: 'full-theory-with-proofs-compiles',
          contextOptions: {
            viewport: { width: 1280, height: 720 },
          },
          timeoutMs: 300000,
          readyWhen(current) {
            // Stop as soon as the bridge helpers are compiled — that
            // proves the full theory (proofs included) compiled cleanly.
            return Array.isArray(current.rocqSyncDiagnostics?.events) &&
              current.rocqSyncDiagnostics.events.some(
                e => e.stage === 'load_world:helpers-ready'
              );
          },
          assert(snapshot, consoleEvents) {
            assertFullTheoryWithProofsCompilesScenario(snapshot, consoleEvents);
          },
        },
        {
          // Verifies that the loading overlay detail text updates to show
          // per-sentence compilation progress while theory is compiling.
          // readyWhen fires as soon as the detail shows the progress prefix,
          // giving interactions.readySnapshot the live overlay state.
          name: 'browser-rocq-sync-compile-progress-overlay',
          rootScenario: 'slow-compile-overlay',
          readyWhen(current) {
            return !current.placeholder?.hidden
              && typeof current.placeholder?.detail === 'string'
              && current.placeholder.detail.startsWith('Compiling game-core theory');
          },
          assert(snapshot, consoleEvents, interactions) {
            assertRocqSyncCompileProgressOverlayScenario(snapshot, consoleEvents, interactions);
          },
        }
      );
    }

    if (DEPLOYED_URL) {
      scenarioConfigs.push({
        name: 'deployed-pages-licensed-map-smoke',
        url: DEPLOYED_URL,
        contextOptions: {
          viewport: { width: 1280, height: 720 },
        },
        permissions: ['clipboard-read', 'clipboard-write'],
        async afterReady(page, snapshot, consoleEvents) {
          const shouldCaptureErrorOverlay = Boolean(detectFailure(snapshot, consoleEvents));
          const [deployedAssetChecks, copyOverlay] = await Promise.all([
            inspectDeployedAssetCaching(DEPLOYED_URL),
            shouldCaptureErrorOverlay ? copyCurrentErrorOverlayIfVisible(page) : Promise.resolve(null),
          ]);
          return {
            deployedAssetChecks,
            copyOverlay,
          };
        },
        timeoutFailure(snapshot) {
          return detectStalledBspParse(snapshot) ?? detectStalledRocqSync(snapshot);
        },
        assert(snapshot, consoleEvents, interactions) {
          assertDeployedPagesScenario(snapshot, consoleEvents, interactions);
        },
      });
    }

    if (scenarioConfigs.length === 0) {
      throw new Error('no Playwright scenarios configured');
    }

    for (const [index, scenario] of scenarioConfigs.entries()) {
      scenarios.push(await runScenario(browser, scenario, outDir, PORT_BASE + index));
    }

    const diagnostics = {
      scenarios,
    };
    await fs.writeFile(diagnosticsPath, `${JSON.stringify(diagnostics, null, 2)}\n`);
    process.stdout.write(`${JSON.stringify({ ...diagnostics, diagnosticsPath }, null, 2)}\n`);

    const failed = scenarios.find(scenario => !scenario.passed);
    if (failed) {
      throw new Error(`scenario ${failed.scenario} failed; inspect ${diagnosticsPath}`);
    }
  } finally {
    await browser.close().catch(() => {});
  }
}

await main().catch(error => {
  console.error(error.message);
  process.exitCode = 1;
});
