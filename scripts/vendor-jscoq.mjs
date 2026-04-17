import fs from 'node:fs/promises';
import path from 'node:path';
import process from 'node:process';

const ROOT = process.cwd();
const SRC_ROOT = path.join(ROOT, 'node_modules', 'jscoq');
const DEST_ROOT = path.join(ROOT, 'docs', 'vendor', 'jscoq');
const RUNTIME_PATHS = [
  'backend/jsoo',
  'backend/wasm',
  'coq-pkgs',
  'dist',
  'dist-webpack',
  'docs/quick-help.html',
  'frontend/classic',
  'jscoq.js',
];

async function pathExists(target) {
  try {
    await fs.access(target);
    return true;
  } catch {
    return false;
  }
}

async function copyRuntimePath(relativePath) {
  const src = path.join(SRC_ROOT, relativePath);
  const dest = path.join(DEST_ROOT, relativePath);

  if (!(await pathExists(src))) {
    throw new Error(`missing jscoq runtime path: ${relativePath}`);
  }

  await fs.mkdir(path.dirname(dest), { recursive: true });
  await fs.cp(src, dest, { recursive: true });
}

await fs.rm(DEST_ROOT, { recursive: true, force: true });
await fs.mkdir(DEST_ROOT, { recursive: true });

for (const relativePath of RUNTIME_PATHS) {
  await copyRuntimePath(relativePath);
}

console.log(`Vendored JsCoq runtime into ${path.relative(ROOT, DEST_ROOT)}`);
