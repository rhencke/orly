// ── Keyboard + mouse fly camera for Q3 BSP level inspection ─────
//
// Noclip-style free camera in Q3's Z-up right-handed coordinate
// system.  Click the canvas to engage pointer lock; WASD to fly,
// mouse to look, Space/Shift for vertical movement.
//
// Usage:
//   import { createFlyCamera } from './camera.js';
//   const cam = createFlyCamera(canvas, { x, y, z, yaw, pitch });
//   // in render loop:
//   cam.update(dt);
//   renderer.render(cam.viewMatrix, projMatrix);
//   // cleanup:
//   cam.destroy();

import { mat4LookAt } from './renderer.js';

const DEG_TO_RAD = Math.PI / 180;

// ── default config ───────────────────────────────────────────────────

const DEFAULT_SPEED     = 320;   // units/sec (Q3 run speed)
const DEFAULT_FAST_MULT = 3;     // shift multiplier
const MOUSE_SENSITIVITY = 0.15;  // degrees per pixel of mouse movement
const PITCH_LIMIT       = 89;    // ±degrees — prevent gimbal flip

// ── key bindings ─────────────────────────────────────────────────────

const KEY_FORWARD  = new Set(['KeyW', 'ArrowUp']);
const KEY_BACK     = new Set(['KeyS', 'ArrowDown']);
const KEY_LEFT     = new Set(['KeyA', 'ArrowLeft']);
const KEY_RIGHT    = new Set(['KeyD', 'ArrowRight']);
const KEY_UP       = new Set(['Space']);
const KEY_DOWN     = new Set(['ShiftLeft', 'ShiftRight']);
const KEY_FAST     = new Set(['ShiftLeft', 'ShiftRight']);

/**
 * Create a fly camera attached to a canvas element.
 *
 * @param {HTMLCanvasElement} canvas — click to engage pointer lock
 * @param {{ x?: number, y?: number, z?: number, yaw?: number, pitch?: number }} init
 * @returns {{ viewMatrix: Float32Array, update(dt: number): void, destroy(): void }}
 */
export function createFlyCamera(canvas, init = {}) {
  // ── state ────────────────────────────────────────────────────────
  let posX  = init.x     ?? 0;
  let posY  = init.y     ?? 0;
  let posZ  = init.z     ?? 0;
  let yaw   = init.yaw   ?? 0;   // degrees, 0 = +X, 90 = +Y (Q3 convention)
  let pitch = init.pitch ?? 0;   // degrees, positive = look up

  const viewMatrix = new Float32Array(16);
  const pressed = new Set();      // currently held key codes
  let mouseDX = 0, mouseDY = 0;  // accumulated mouse delta since last update

  // ── pointer lock ─────────────────────────────────────────────────
  function requestLock() {
    canvas.requestPointerLock?.();
  }

  function onMouseMove(e) {
    if (document.pointerLockElement !== canvas) return;
    mouseDX += e.movementX;
    mouseDY += e.movementY;
  }

  // ── keyboard ─────────────────────────────────────────────────────
  function onKeyDown(e) {
    // Don't capture keys when typing in JsCoq or other inputs
    if (e.target.tagName === 'TEXTAREA' || e.target.tagName === 'INPUT') return;
    if (e.target.isContentEditable) return;
    pressed.add(e.code);
    // Prevent default for game keys to avoid page scroll
    if (KEY_FORWARD.has(e.code) || KEY_BACK.has(e.code) ||
        KEY_LEFT.has(e.code) || KEY_RIGHT.has(e.code) ||
        KEY_UP.has(e.code)) {
      e.preventDefault();
    }
  }

  function onKeyUp(e) {
    pressed.delete(e.code);
  }

  // Clear pressed keys when pointer lock is lost so we don't get
  // stuck-key ghosts (keyup fires on the document, not the canvas,
  // but browser behavior varies on lock exit).
  function onLockChange() {
    if (document.pointerLockElement !== canvas) {
      pressed.clear();
    }
  }

  // ── bind events ──────────────────────────────────────────────────
  canvas.addEventListener('click', requestLock);
  document.addEventListener('mousemove', onMouseMove);
  document.addEventListener('keydown', onKeyDown);
  document.addEventListener('keyup', onKeyUp);
  document.addEventListener('pointerlockchange', onLockChange);

  // ── helpers ──────────────────────────────────────────────────────
  function isPressed(keySet) {
    for (const k of keySet) if (pressed.has(k)) return true;
    return false;
  }

  // ── per-frame update ─────────────────────────────────────────────
  function update(dt) {
    // Apply mouse look
    if (mouseDX !== 0 || mouseDY !== 0) {
      yaw   -= mouseDX * MOUSE_SENSITIVITY;
      pitch -= mouseDY * MOUSE_SENSITIVITY;
      // Normalize yaw to [0, 360)
      yaw = ((yaw % 360) + 360) % 360;
      // Clamp pitch
      pitch = Math.max(-PITCH_LIMIT, Math.min(PITCH_LIMIT, pitch));
      mouseDX = 0;
      mouseDY = 0;
    }

    // Movement — relative to current yaw (pitch does not affect move direction,
    // only the look direction; this feels natural for noclip inspection)
    const speed = isPressed(KEY_FAST)
      ? DEFAULT_SPEED * DEFAULT_FAST_MULT
      : DEFAULT_SPEED;
    const dist = speed * dt;

    const yawRad = yaw * DEG_TO_RAD;
    const cosYaw = Math.cos(yawRad);
    const sinYaw = Math.sin(yawRad);

    // Forward/back along the yaw direction (XY plane)
    if (isPressed(KEY_FORWARD)) { posX += cosYaw * dist; posY += sinYaw * dist; }
    if (isPressed(KEY_BACK))    { posX -= cosYaw * dist; posY -= sinYaw * dist; }

    // Strafe left/right (perpendicular to yaw in XY plane)
    if (isPressed(KEY_LEFT))  { posX += sinYaw * dist; posY -= cosYaw * dist; }
    if (isPressed(KEY_RIGHT)) { posX -= sinYaw * dist; posY += cosYaw * dist; }

    // Vertical movement (Z axis, always world-aligned)
    if (isPressed(KEY_UP))   posZ += dist;
    if (isPressed(KEY_DOWN)) posZ -= dist;

    // Build view matrix
    const pitchRad = pitch * DEG_TO_RAD;
    const cosPitch = Math.cos(pitchRad);
    const lookX = posX + cosYaw * cosPitch;
    const lookY = posY + sinYaw * cosPitch;
    const lookZ = posZ + Math.sin(pitchRad);

    mat4LookAt(viewMatrix,
               [posX, posY, posZ],
               [lookX, lookY, lookZ],
               [0, 0, 1]);
  }

  // Build initial view matrix
  update(0);

  // ── cleanup ──────────────────────────────────────────────────────
  function destroy() {
    canvas.removeEventListener('click', requestLock);
    document.removeEventListener('mousemove', onMouseMove);
    document.removeEventListener('keydown', onKeyDown);
    document.removeEventListener('keyup', onKeyUp);
    document.removeEventListener('pointerlockchange', onLockChange);
    if (document.pointerLockElement === canvas) {
      document.exitPointerLock?.();
    }
  }

  return { viewMatrix, update, destroy };
}
