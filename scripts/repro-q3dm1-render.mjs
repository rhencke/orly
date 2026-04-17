import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { spawn } from 'node:child_process';
import { chromium } from 'playwright';

const ROOT = process.cwd();
const DOCS_DIR = path.join(ROOT, 'docs');
const PORT_BASE = Number.parseInt(process.env.ORLY_REPRO_PORT ?? '18080', 10);
const TIMEOUT_MS = Number.parseInt(process.env.ORLY_REPRO_TIMEOUT_MS ?? '20000', 10);
const POLL_MS = 500;
const BSP_MAGIC = 0x49425350;
const BSP_VERSION = 46;
const NUM_LUMPS = 17;
const HEADER_SIZE = 8 + NUM_LUMPS * 8;
const BOOTSTRAP_FAILURE_RE =
  /launch failure SecurityError|Failed to construct 'Worker'|JsCoq bootstrap failed/i;
const RENDER_FAILURE_RE = /BSP render init failed|Render error:/i;
const SUCCESSFUL_RENDER_RE = /render pipeline active/i;

const STUB_BRIDGE_SOURCE = `
const VIEW_MATRIX = [1, 0, 0, 0,
                     0, 1, 0, 0,
                     0, 0, 1, 0,
                     0, 0, 0, 1];

export function createRocqBridge() {
  let visibleFaces = [];

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

    async load_world(world) {
      visibleFaces = Array.isArray(world?.faces)
        ? world.faces.map((_, fi) => fi)
        : [];
      return snapshot();
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

async function sleep(ms) {
  await new Promise(resolve => setTimeout(resolve, ms));
}

async function waitForServer(url, timeoutMs) {
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

function createSyntheticBsp() {
  const buffer = new ArrayBuffer(HEADER_SIZE);
  const view = new DataView(buffer);
  view.setUint32(0, BSP_MAGIC, true);
  view.setInt32(4, BSP_VERSION, true);
  return Buffer.from(buffer);
}

async function createScenarioRoot(scenarioName) {
  const rootDir = await fs.mkdtemp(path.join(os.tmpdir(), `orly-${scenarioName}-`));
  await fs.cp(DOCS_DIR, rootDir, { recursive: true });
  await fs.rm(path.join(rootDir, 'assets'), { recursive: true, force: true });

  if (scenarioName === 'q3dm1-render-startup') {
    await fs.mkdir(path.join(rootDir, 'assets', 'maps'), { recursive: true });
    await fs.writeFile(
      path.join(rootDir, 'assets', 'manifest.json'),
      `${JSON.stringify(['maps/q3dm1.bsp'])}\n`
    );
    await fs.writeFile(path.join(rootDir, 'assets', 'maps', 'q3dm1.bsp'), createSyntheticBsp());
    await fs.writeFile(path.join(rootDir, 'rocq_bridge.js'), STUB_BRIDGE_SOURCE);
  }

  return rootDir;
}

async function gatherSnapshot(page) {
  return page.evaluate(() => {
    const statusBar = document.getElementById('status-bar');
    const placeholder = document.getElementById('game-placeholder');
    const placeholderTitle = placeholder?.querySelector('[data-placeholder-role="title"]');
    const placeholderDetail = placeholder?.querySelector('[data-placeholder-role="detail"]');
    const canvas = document.getElementById('game-canvas');
    const assetMap = window.orlyAssets instanceof Map ? window.orlyAssets : null;

    return {
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
      canvas: canvas
        ? {
            width: canvas.width,
            height: canvas.height,
          }
        : null,
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

function detectFailure(snapshot, consoleEvents) {
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

async function waitForScenario(page, consoleEvents, predicate) {
  const deadline = Date.now() + TIMEOUT_MS;
  let snapshot = await gatherSnapshotWithRetry(page);

  while (Date.now() < deadline) {
    if (predicate(snapshot, consoleEvents) || detectFailure(snapshot, consoleEvents)) {
      return snapshot;
    }
    await page.waitForTimeout(POLL_MS);
    snapshot = await gatherSnapshotWithRetry(page);
  }

  return snapshot;
}

function attachEventCapture(page, consoleEvents) {
  page.on('console', msg => {
    consoleEvents.push({
      kind: 'console',
      type: msg.type(),
      text: msg.text(),
    });
  });
  page.on('pageerror', error => {
    consoleEvents.push({
      kind: 'pageerror',
      text: error.message,
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
    throw new Error('placeholder should stay visible when q3dm1 assets are absent');
  }
  if (snapshot.placeholder?.state !== 'idle') {
    throw new Error(`expected idle placeholder state, got ${snapshot.placeholder?.state ?? '(missing)'}`);
  }
  if (snapshot.placeholder?.title !== 'q3dm1 assets not found') {
    throw new Error(`unexpected no-assets placeholder title: ${snapshot.placeholder?.title ?? '(missing)'}`);
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
    throw new Error(`expected one stubbed q3dm1 asset, got ${snapshot.assetCount}`);
  }
  if (snapshot.placeholder?.hidden !== true) {
    throw new Error('placeholder never hid after q3dm1 render startup');
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

async function runScenario(browser, scenarioName, outDir, port) {
  const scenarioRoot = await createScenarioRoot(scenarioName);
  const { server, readLogs } = startStaticServer(scenarioRoot, port);
  const url = `http://127.0.0.1:${port}/`;
  const consoleEvents = [];
  let page = null;

  try {
    await waitForServer(url, 10000).catch(error => {
      const logs = readLogs();
      throw new Error(
        `${error.message}\nstdout:\n${logs.stdout || '(empty)'}\nstderr:\n${logs.stderr || '(empty)'}`
      );
    });

    page = await browser.newPage({ viewport: { width: 1280, height: 720 } });
    attachEventCapture(page, consoleEvents);

    await page.goto(url, { waitUntil: 'domcontentloaded', timeout: 120000 });
    await page.waitForLoadState('load').catch(() => {});

    const snapshot = await waitForScenario(
      page,
      consoleEvents,
      scenarioName === 'browser-load-no-assets'
        ? current => current.jscoqLoaded && current.status?.hidden === true
        : current => current.placeholder?.hidden === true
    );

    const screenshotPath = path.join(outDir, `${scenarioName}.png`);
    await page.screenshot({ path: screenshotPath, fullPage: true });

    if (scenarioName === 'browser-load-no-assets') {
      assertNoAssetsScenario(snapshot, consoleEvents);
    } else {
      assertRenderStartupScenario(snapshot, consoleEvents);
    }

    return {
      scenario: scenarioName,
      passed: true,
      url,
      snapshot,
      consoleEvents,
      serverLogs: readLogs(),
      screenshotPath,
    };
  } catch (error) {
    const screenshotPath = path.join(outDir, `${scenarioName}.png`);
    await page?.screenshot({ path: screenshotPath, fullPage: true }).catch(() => {});
    const failureSnapshot = page
      ? await gatherSnapshotWithRetry(page).catch(() => null)
      : null;
    return {
      scenario: scenarioName,
      passed: false,
      url,
      failure: error.message,
      snapshot: failureSnapshot,
      consoleEvents,
      serverLogs: readLogs(),
      screenshotPath,
    };
  } finally {
    await page?.close().catch(() => {});
    server.kill('SIGTERM');
    await new Promise(resolve => {
      if (server.exitCode !== null) {
        resolve();
      } else {
        server.once('exit', resolve);
      }
    });
    await fs.rm(scenarioRoot, { recursive: true, force: true }).catch(() => {});
  }
}

async function main() {
  const browser = await chromium.launch({ headless: true });

  try {
    const outDir = await fs.mkdtemp(path.join(os.tmpdir(), 'orly-q3dm1-regression-'));
    const diagnosticsPath = path.join(outDir, 'diagnostics.json');
    const scenarios = [];

    for (const [index, scenarioName] of ['browser-load-no-assets', 'q3dm1-render-startup'].entries()) {
      scenarios.push(await runScenario(browser, scenarioName, outDir, PORT_BASE + index));
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
