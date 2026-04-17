import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import process from 'node:process';
import { spawn } from 'node:child_process';
import { chromium } from 'playwright';

const ROOT = process.cwd();
const PORT = Number.parseInt(process.env.ORLY_REPRO_PORT ?? '8080', 10);
const URL = `http://127.0.0.1:${PORT}/`;
const TIMEOUT_MS = Number.parseInt(process.env.ORLY_REPRO_TIMEOUT_MS ?? '20000', 10);
const POLL_MS = 500;

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

function startStaticServer() {
  const server = spawn(
    'make',
    ['serve'],
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

async function maybeStartServer() {
  try {
    await waitForServer(URL, 1000);
    return {
      server: null,
      reused: true,
      readLogs: () => ({ stdout: '', stderr: '' }),
    };
  } catch (_) {
    const started = startStaticServer();
    await waitForServer(URL, 10000).catch(error => {
      const logs = started.readLogs();
      throw new Error(
        `${error.message}\nstdout:\n${logs.stdout || '(empty)'}\nstderr:\n${logs.stderr || '(empty)'}`
      );
    });
    return {
      ...started,
      reused: false,
    };
  }
}

async function gatherSnapshot(page) {
  return page.evaluate(() => {
    const statusBar = document.getElementById('status-bar');
    const placeholder = document.getElementById('game-placeholder');
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
      placeholderHidden: placeholder?.hidden ?? null,
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

function detectFailure(snapshot, consoleEvents) {
  if (consoleEvents.some(event =>
    /launch failure SecurityError|Failed to construct 'Worker'/.test(event.text)
  )) {
    return 'jscoq-worker-security-error';
  }

  if (snapshot.assetCount !== null &&
      snapshot.assetCount > 0 &&
      snapshot.placeholderHidden === false) {
    return 'placeholder-still-visible';
  }

  return null;
}

async function main() {
  const bspPath = path.join(ROOT, 'docs/assets/maps/q3dm1.bsp');
  await fs.access(bspPath).catch(() => {
    throw new Error('docs/assets/maps/q3dm1.bsp is missing; run `make assets` first');
  });

  const { server, reused, readLogs } = await maybeStartServer();
  let browser;

  const consoleEvents = [];

  try {
    await waitForServer(URL, 10000);

    browser = await chromium.launch({ headless: true });
    const page = await browser.newPage({ viewport: { width: 1280, height: 720 } });

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

    await page.goto(URL, { waitUntil: 'domcontentloaded', timeout: 120000 });
    await page.waitForLoadState('load').catch(() => {});

    let snapshot = await gatherSnapshotWithRetry(page);
    const deadline = Date.now() + TIMEOUT_MS;
    while (Date.now() < deadline) {
      if (detectFailure(snapshot, consoleEvents) || snapshot.placeholderHidden === true || snapshot.status?.className === 'error') {
        break;
      }
      await page.waitForTimeout(POLL_MS);
      snapshot = await gatherSnapshotWithRetry(page);
    }

    const outDir = await fs.mkdtemp(path.join(os.tmpdir(), 'orly-q3dm1-repro-'));
    const screenshotPath = path.join(outDir, 'page.png');
    const diagnosticsPath = path.join(outDir, 'diagnostics.json');

    await page.screenshot({ path: screenshotPath, fullPage: true });

    const failureReason = detectFailure(snapshot, consoleEvents);
    const diagnostics = {
      url: URL,
      reproduced: failureReason !== null,
      failureReason,
      snapshot,
      consoleEvents,
      reusedServer: reused,
      serverLogs: readLogs(),
      screenshotPath,
    };
    await fs.writeFile(diagnosticsPath, `${JSON.stringify(diagnostics, null, 2)}\n`);

    process.stdout.write(`${JSON.stringify({ ...diagnostics, diagnosticsPath }, null, 2)}\n`);

    if (!diagnostics.reproduced) {
      throw new Error(`q3dm1 render failure did not reproduce; inspect ${diagnosticsPath}`);
    }
  } finally {
    await browser?.close().catch(() => {});
    if (server) {
      server.kill('SIGTERM');
      await new Promise(resolve => {
        if (server.exitCode !== null) {
          resolve();
        } else {
          server.once('exit', resolve);
        }
      });
    }
  }
}

await main().catch(error => {
  console.error(error.message);
  process.exitCode = 1;
});
