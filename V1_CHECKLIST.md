# V1 feature checklist: demo-level playability

This document defines the exact acceptance target for
[issue #12](https://github.com/rhencke/orly/issues/12).  Everything on this
list must be true before v1 ships.  Anything not on this list is either
explicitly deferred to [issue #18](https://github.com/rhencke/orly/issues/18)
or out of scope entirely.  The Rocq/JS boundary that governs which items
belong in Rocq versus JavaScript is defined in
[ARCHITECTURE.md](ARCHITECTURE.md).

## Chosen level: q3dm1 — Arena Gate

The v1 demo level is **q3dm1** ("Arena Gate", also known as "The Place of
Many Deaths").  Reasons:

- Small footprint — a tight multi-level arena with corridors, ramps, and open
  platforms.  Enough geometry to exercise collision and rendering without the
  complexity of a large map.
- No scripted entities required beyond spawn points and a jump pad — keeps the
  minimum gameplay logic tractable for a first port.
- Immediately recognizable — anyone who has touched Quake 3 knows this room,
  which makes the "it runs" moment legible to an outside observer.
- Freely available in the Quake 3 Arena demo distribution under id Software's
  demo license; asset packaging is tracked separately in
  [issue #14](https://github.com/rhencke/orly/issues/14).

## Acceptance checklist

### Load and deployment

- [ ] The GitHub Pages URL opens in a desktop browser (Chrome, Firefox,
      Safari) without errors.
- [ ] The GitHub Pages URL opens in a mobile browser (Safari on iOS, Chrome
      on Android) without errors.
- [ ] JsCoq boots, the Rocq kernel starts, and the IDE panel shows the
      game-core theories loading.
- [ ] The BSP and texture assets for q3dm1 load from the site build
      reproducibly — no manual file-copy steps, no ad hoc paths.
- [ ] A local reproduction works by following the repo docs alone
      (`make serve` or equivalent) on both desktop and mobile via local
      network.

### Spawn

- [ ] The player spawns at a valid q3dm1 spawn point rather than at the world
      origin.
- [ ] Spawn position and orientation are computed by Rocq from the BSP entity
      data, not hard-coded in JavaScript.

### Camera and look

- [ ] On desktop, pointer lock engages on click and mouse movement rotates the
      camera (yaw and pitch).
- [ ] On mobile, dragging the right-side look area rotates the camera (yaw and
      pitch).
- [ ] Pitch is clamped to prevent flipping upside-down (±89° or equivalent).
- [ ] Camera state (position, orientation) is owned by Rocq; JavaScript reads
      the camera matrix from the render snapshot each frame.

### Movement

- [ ] On desktop, WASD (or arrow keys) moves the player in the expected
      directions relative to the current yaw.
- [ ] On mobile, the left virtual joystick translates touch position to a
      movement vector passed to Rocq each tick.
- [ ] The player does not fall through the floor in the spawn area and can
      traverse the main floor of q3dm1 on foot.
- [ ] Movement physics (velocity, acceleration, friction) are implemented in
      Rocq, not duplicated in JavaScript.

### Collision

- [ ] The player cannot walk through solid brushes (walls, floors, ceilings).
- [ ] Collision is tested against the q3dm1 BSP brush data owned by Rocq, not
      a JavaScript-side approximation.
- [ ] The player can navigate the main corridors and open area of q3dm1 without
      clipping through geometry.
- [ ] Falling off a ledge applies gravity; the player lands on the floor below
      rather than continuing to fall forever.

### Minimum gameplay logic

- [ ] The jump pad in q3dm1 launches the player upward when walked over
      (trigger_push entity).  This is the one non-trivial entity type required
      by the chosen level; if q3dm1 is loaded without it, the jump pad area
      is simply a dead zone, which is acceptable for v1 **only if** spawn and
      traversal of the rest of the level work correctly.
- [ ] Rocq evaluates the trigger_push impulse; JavaScript does not compute the
      launch vector independently.
- [ ] The frame/tick loop is stable enough that gameplay behavior is
      reproducible across page reloads — not chaotic or sensitive to startup
      timing.

### Mobile controls and layout

- [ ] Control overlays (virtual joystick, look area) are visible and usable in
      portrait orientation on a phone-sized screen (360 × 780 logical pixels
      or similar).
- [ ] Control overlays adapt to landscape orientation; both sticks remain
      reachable with thumbs.
- [ ] Touch targets are large enough for reliable use (minimum 44 × 44 CSS px
      per overlay button/joystick zone).
- [ ] The game canvas and JsCoq IDE panel coexist without the canvas being too
      small to see what is happening.  The drag-to-resize handle works on touch.
- [ ] The safe-area insets (`env(safe-area-inset-*)`) keep controls off the
      notch and home-bar area on notched iOS devices.

### Rocq-powered core

- [ ] All game state (player position, orientation, velocity, entity state)
      lives in Rocq.  JavaScript reads render snapshots; it never independently
      tracks or recomputes game state.
- [ ] `theories/GameState.v` includes executable proofs/examples for the control
      contract: pitch clamping, yaw-relative movement, conflicting-axis
      cancellation, grounded jumping, and airborne gravity.
- [ ] The Rocq theories that power the running game are visible and
      step-through-able in the JsCoq IDE panel on the same page.
- [ ] `make test` (CI: `rocq compile`) passes with the game-core theories in
      `theories/`.

## Mobile browser and device assumptions

These are the v1 supported targets.  Anything outside this list is untested and
explicitly not a blocking v1 requirement.

| Target | Minimum version |
|---|---|
| Safari on iOS | iOS 16 |
| Chrome on Android | Chrome 110 |

**Acceptable constraints for v1 mobile:**

- Portrait and landscape orientations are both supported, but split-screen /
  picture-in-picture modes on iPad are not tested.
- Physical keyboard and mouse connected to a tablet are not tested (treat as
  desktop if they work; do not break if they do not).
- Pointer-lock API is not available on mobile; look input is touch-only.
- Performance does not need to hit 60 fps on low-end devices — 30 fps on a
  2020-era mid-range phone (e.g. iPhone SE 2nd gen, Pixel 4a) is acceptable.
- No gamepad API support required.
- Screen reader / accessibility support is not in scope for v1.

## Explicitly deferred to issue #18

The following are **not** v1 requirements.  Do not add them to this checklist
or implement them in the v1 milestone.

- Audio (Web Audio API, Quake 3 sound effects or music)
- Multiple levels or a level-selection UI
- HUD elements beyond a minimal "press to start / controls" overlay
- Multiplayer or network play
- Mod support (custom content, `pak` file loading beyond the demo assets)
- Rocq extraction to OCaml/JavaScript as a performance path
- Weapon pickup, firing, and hit detection
- Bot AI
- Player animations and model rendering (a simple bounding-box
  first-person view is sufficient for v1)
- Leaderboards, scoring, or any persistent state
