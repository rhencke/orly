const MOUSE_SENSITIVITY = 0.15; // degrees per pixel of look motion
const TOUCH_AXIS_THRESHOLD = 0.35;

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

function clamp(value, min, max) {
  return Math.min(max, Math.max(min, value));
}

function setKnobOffset(knob, dx, dy) {
  knob.style.transform = `translate(${dx}px, ${dy}px)`;
}

function createTouchPad(pad, knob, { accumulateLook = false, onPressChange = null } = {}) {
  let pointerId = null;
  let axisX = 0;
  let axisY = 0;
  let lookDX = 0;
  let lookDY = 0;
  let lastX = 0;
  let lastY = 0;

  function reset() {
    pointerId = null;
    axisX = 0;
    axisY = 0;
    lookDX = 0;
    lookDY = 0;
    setKnobOffset(knob, 0, 0);
    onPressChange?.(false);
  }

  function updateAxisFromEvent(event) {
    const rect = pad.getBoundingClientRect();
    const centerX = rect.left + rect.width / 2;
    const centerY = rect.top + rect.height / 2;
    const radius = Math.max(1, Math.min(rect.width, rect.height) * 0.35);
    const rawX = event.clientX - centerX;
    const rawY = event.clientY - centerY;
    const distance = Math.hypot(rawX, rawY);
    const scale = distance > radius ? radius / distance : 1;
    const clampedX = rawX * scale;
    const clampedY = rawY * scale;
    axisX = clampedX / radius;
    axisY = clampedY / radius;
    setKnobOffset(knob, clampedX, clampedY);
  }

  function onPointerDown(event) {
    if (event.pointerType === 'mouse') return;
    if (pointerId !== null) return;
    pointerId = event.pointerId;
    lastX = event.clientX;
    lastY = event.clientY;
    pad.setPointerCapture?.(event.pointerId);
    if (!accumulateLook) {
      updateAxisFromEvent(event);
    }
    onPressChange?.(true);
    event.preventDefault();
  }

  function onPointerMove(event) {
    if (event.pointerId !== pointerId) return;
    if (accumulateLook) {
      lookDX += event.clientX - lastX;
      lookDY += event.clientY - lastY;
      lastX = event.clientX;
      lastY = event.clientY;
      updateAxisFromEvent(event);
    } else {
      updateAxisFromEvent(event);
    }
    event.preventDefault();
  }

  function onPointerEnd(event) {
    if (event.pointerId !== pointerId) return;
    reset();
    event.preventDefault();
  }

  pad.addEventListener('pointerdown', onPointerDown);
  pad.addEventListener('pointermove', onPointerMove);
  pad.addEventListener('pointerup', onPointerEnd);
  pad.addEventListener('pointercancel', onPointerEnd);
  pad.addEventListener('lostpointercapture', reset);

  return {
    sample() {
      const snapshot = {
        axisX,
        axisY,
        yawDelta: -lookDX * MOUSE_SENSITIVITY,
        pitchDelta: -lookDY * MOUSE_SENSITIVITY,
      };
      lookDX = 0;
      lookDY = 0;
      return snapshot;
    },

    destroy() {
      reset();
      pad.removeEventListener('pointerdown', onPointerDown);
      pad.removeEventListener('pointermove', onPointerMove);
      pad.removeEventListener('pointerup', onPointerEnd);
      pad.removeEventListener('pointercancel', onPointerEnd);
      pad.removeEventListener('lostpointercapture', reset);
    },
  };
}

export function createTouchInput(overlay) {
  const coarsePointerQuery = window.matchMedia('(pointer: coarse)');
  const movePad = overlay.querySelector('[data-touch-control="move-pad"]');
  const moveKnob = overlay.querySelector('[data-touch-control="move-knob"]');
  const lookPad = overlay.querySelector('[data-touch-control="look-pad"]');
  const lookKnob = overlay.querySelector('[data-touch-control="look-knob"]');
  const jumpButton = overlay.querySelector('[data-touch-control="jump"]');
  let jumpPressed = false;

  function setActiveClass(element, active) {
    element.classList.toggle('is-active', active);
  }

  function setJumpPressed(active) {
    jumpPressed = active;
    setActiveClass(jumpButton, active);
  }

  const moveControl = createTouchPad(movePad, moveKnob, {
    onPressChange(active) {
      setActiveClass(movePad, active);
    },
  });
  const lookControl = createTouchPad(lookPad, lookKnob, {
    accumulateLook: true,
    onPressChange(active) {
      setActiveClass(lookPad, active);
    },
  });

  function syncVisibility() {
    overlay.hidden = !coarsePointerQuery.matches;
  }

  function onJumpDown(event) {
    if (event.pointerType === 'mouse') return;
    setJumpPressed(true);
    jumpButton.setPointerCapture?.(event.pointerId);
    event.preventDefault();
  }

  function onJumpEnd(event) {
    setJumpPressed(false);
    event.preventDefault();
  }

  function onJumpLostPointerCapture() {
    setJumpPressed(false);
  }

  syncVisibility();
  coarsePointerQuery.addEventListener('change', syncVisibility);
  jumpButton.addEventListener('pointerdown', onJumpDown);
  jumpButton.addEventListener('pointerup', onJumpEnd);
  jumpButton.addEventListener('pointercancel', onJumpEnd);
  jumpButton.addEventListener('lostpointercapture', onJumpLostPointerCapture);
  window.addEventListener('blur', onJumpEnd);

  return {
    sample() {
      const move = moveControl.sample();
      const look = lookControl.sample();
      const axisX = clamp(move.axisX, -1, 1);
      const axisY = clamp(move.axisY, -1, 1);
      return {
        forward: axisY < -TOUCH_AXIS_THRESHOLD,
        back: axisY > TOUCH_AXIS_THRESHOLD,
        left: axisX < -TOUCH_AXIS_THRESHOLD,
        right: axisX > TOUCH_AXIS_THRESHOLD,
        jump: jumpPressed,
        yawDelta: look.yawDelta,
        pitchDelta: look.pitchDelta,
      };
    },

    destroy() {
      moveControl.destroy();
      lookControl.destroy();
      setJumpPressed(false);
      coarsePointerQuery.removeEventListener('change', syncVisibility);
      jumpButton.removeEventListener('pointerdown', onJumpDown);
      jumpButton.removeEventListener('pointerup', onJumpEnd);
      jumpButton.removeEventListener('pointercancel', onJumpEnd);
      jumpButton.removeEventListener('lostpointercapture', onJumpLostPointerCapture);
      window.removeEventListener('blur', onJumpEnd);
    },
  };
}

export function createPlayerInput(canvas, overlay) {
  const desktop = createDesktopInput(canvas);
  const touch = createTouchInput(overlay);

  return {
    sample(dtMs) {
      const desktopSnapshot = desktop.sample(dtMs);
      const touchSnapshot = touch.sample();
      return {
        forward: desktopSnapshot.forward || touchSnapshot.forward,
        back: desktopSnapshot.back || touchSnapshot.back,
        left: desktopSnapshot.left || touchSnapshot.left,
        right: desktopSnapshot.right || touchSnapshot.right,
        jump: desktopSnapshot.jump || touchSnapshot.jump,
        yawDelta: desktopSnapshot.yawDelta + touchSnapshot.yawDelta,
        pitchDelta: desktopSnapshot.pitchDelta + touchSnapshot.pitchDelta,
        dtMs: desktopSnapshot.dtMs,
      };
    },

    destroy() {
      desktop.destroy();
      touch.destroy();
    },
  };
}
