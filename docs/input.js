const MOUSE_SENSITIVITY = 0.15; // degrees per pixel of pointer-lock motion

const KEY_FORWARD = new Set(['KeyW', 'ArrowUp']);
const KEY_BACK = new Set(['KeyS', 'ArrowDown']);
const KEY_LEFT = new Set(['KeyA', 'ArrowLeft']);
const KEY_RIGHT = new Set(['KeyD', 'ArrowRight']);
const KEY_JUMP = new Set(['Space']);

function isEditableTarget(target) {
  return target instanceof HTMLElement &&
    (target.tagName === 'TEXTAREA' ||
     target.tagName === 'INPUT' ||
     target.isContentEditable);
}

export function createDesktopInput(canvas) {
  const pressed = new Set();
  let mouseDX = 0;
  let mouseDY = 0;

  function requestPointerLock() {
    canvas.requestPointerLock?.();
  }

  function onMouseMove(event) {
    if (document.pointerLockElement !== canvas) return;
    mouseDX += event.movementX;
    mouseDY += event.movementY;
  }

  function onKeyDown(event) {
    if (isEditableTarget(event.target)) return;
    pressed.add(event.code);
    if (KEY_FORWARD.has(event.code) || KEY_BACK.has(event.code) ||
        KEY_LEFT.has(event.code) || KEY_RIGHT.has(event.code) ||
        KEY_JUMP.has(event.code)) {
      event.preventDefault();
    }
  }

  function onKeyUp(event) {
    pressed.delete(event.code);
  }

  function clearTransientState() {
    mouseDX = 0;
    mouseDY = 0;
  }

  function clearAllState() {
    pressed.clear();
    clearTransientState();
  }

  function isPressed(keySet) {
    for (const code of keySet) {
      if (pressed.has(code)) return true;
    }
    return false;
  }

  canvas.addEventListener('click', requestPointerLock);
  document.addEventListener('mousemove', onMouseMove);
  document.addEventListener('keydown', onKeyDown);
  document.addEventListener('keyup', onKeyUp);
  document.addEventListener('pointerlockchange', clearAllState);
  window.addEventListener('blur', clearAllState);

  return {
    sample(dtMs) {
      const snapshot = {
        forward: isPressed(KEY_FORWARD),
        back: isPressed(KEY_BACK),
        left: isPressed(KEY_LEFT),
        right: isPressed(KEY_RIGHT),
        jump: isPressed(KEY_JUMP),
        yawDelta: -mouseDX * MOUSE_SENSITIVITY,
        pitchDelta: -mouseDY * MOUSE_SENSITIVITY,
        dtMs: Math.max(0, Math.round(dtMs)),
      };
      clearTransientState();
      return snapshot;
    },

    destroy() {
      canvas.removeEventListener('click', requestPointerLock);
      document.removeEventListener('mousemove', onMouseMove);
      document.removeEventListener('keydown', onKeyDown);
      document.removeEventListener('keyup', onKeyUp);
      document.removeEventListener('pointerlockchange', clearAllState);
      window.removeEventListener('blur', clearAllState);
      if (document.pointerLockElement === canvas) {
        document.exitPointerLock?.();
      }
    },
  };
}
