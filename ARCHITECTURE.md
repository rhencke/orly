# Architecture: Rocq/JsCoq vs JavaScript boundary

This document defines which responsibilities live in Rocq (executed via
JsCoq in the browser) and which stay in the JavaScript/browser shell.
Later issues should be judged against these decisions to determine whether
they are on-architecture or off-architecture.  The concrete v1 acceptance
criteria that this boundary governs are in
[V1_CHECKLIST.md](V1_CHECKLIST.md).

## Execution path

The shipped experience uses **JsCoq interpreted execution**.  Rocq source
files in `theories/` are loaded by JsCoq in the browser and interpreted
directly — there is no Rocq extraction step to OCaml or JavaScript.

Why interpreted:

- The JsCoq IDE panel is a visible, interactive part of the shipped page.
  Users see Rocq code running, step through proofs, and watch the kernel
  check definitions.  This is the point of the project — a formally
  verified game core that the user can inspect live.
- Extraction to OCaml/JS would produce opaque compiled output, removing
  the connection between the proofs and the running game.
- JsCoq 0.17.1 is already integrated (loaded from jsDelivr CDN) and
  handles the Rocq kernel, package management, and editor integration.

CI continues to compile `theories/` with `rocq compile` to catch errors
before they reach the browser.

## What lives in Rocq/JsCoq

These responsibilities must be implemented in Rocq so the playable core
is genuinely powered by Rocq/JsCoq, not only by JavaScript.

### Game state

All authoritative game state lives in Rocq: player position, orientation,
velocity, and any entity or trigger state needed for the v1 demo level.
JavaScript never independently tracks or modifies game state — it reads
snapshots produced by Rocq for rendering.

### Gameplay logic

Movement, camera control, collision detection against world geometry, and
entity/trigger evaluation are Rocq responsibilities.  The game rules are
defined as Rocq functions so they are available for inspection and proof.

### World representation

The parsed BSP level structure — nodes, leaves, planes, brushes,
surfaces — is owned by Rocq.  JavaScript sends raw asset bytes to Rocq;
Rocq parses and owns the resulting data structures.

### Frame step

Each frame, JavaScript sends a tick message containing elapsed time and
the current input snapshot.  Rocq runs one game step: applies input to
player state, advances physics, evaluates triggers, and produces a
**render snapshot** (camera transform, visible surface list, entity
positions) that JavaScript consumes for drawing.

For player controls, the frame-step contract is intentionally specific:

- JavaScript normalizes desktop keyboard/mouse and mobile touch controls
  into the same `input_snapshot` shape before crossing the bridge.
- Rocq applies yaw deltas before deriving planar movement, so "forward"
  and "strafe" always mean relative to the updated facing angle.
- Rocq clamps pitch to the gameplay-safe range and wraps yaw into the
  usual turn-around interval rather than leaving angle drift to JS.
- World stepping owns jump, gravity, and collision response: jumping is
  grounded-only, gravity applies when airborne, and blocked motion zeroes
  the corresponding velocity component in the authoritative state.

These rules are documented as executable lemmas and examples in
`theories/GameState.v`, so the shipped controls have a proof-backed
behavior story instead of only an informal browser implementation.

## What stays in JavaScript

These responsibilities stay in the browser shell because they require
DOM/Web APIs that Rocq cannot access, or because they are pure
presentation concerns that do not affect the game's logical correctness.

### Rendering (WebGL)

All GPU interaction is JavaScript.  The JS shell takes the render
snapshot from Rocq (camera matrix, surface list, entity positions) and
issues WebGL draw calls.  Shader programs, texture uploads, and draw-call
batching are JS concerns.  Rocq decides **what** to draw; JavaScript
decides **how** to draw it.

### Asset fetching and binary loading

HTTP fetches (`fetch()`), response handling, and delivery of raw byte
arrays to Rocq are JavaScript's job.  Rocq does not initiate network
requests.  JavaScript fetches BSP files, texture data, and any other
assets, then passes the raw bytes into Rocq for parsing.

### Frame timing

The `requestAnimationFrame` loop lives in JavaScript.  JS measures delta
time, bundles it with the current input state, sends the tick to Rocq,
receives the render snapshot, and draws.  Rocq is a pure function of
(previous state, tick) — it does not own the clock.

### Desktop input capture

Keyboard and mouse event listeners are JavaScript.  JS captures
`keydown`/`keyup`, `mousemove`, `click`, and pointer-lock state, then
packs them into an input snapshot struct sent to Rocq each tick.

### Mobile input capture and control surfaces

Touch event listeners (`touchstart`, `touchmove`, `touchend`) are
JavaScript.  On-screen control UI — virtual joystick, fire button, look
area — is rendered as HTML/CSS overlays by JavaScript and is purely a
presentation concern.

JavaScript translates touch gestures into the same input snapshot format
used by desktop controls: movement vector, look delta, action flags.
Rocq receives identical input snapshots regardless of whether they came
from keyboard/mouse or touch.  This means:

- **In JavaScript (browser glue):** touch hit-testing, gesture
  recognition (drag vs tap), virtual joystick position tracking,
  on-screen button layout, and the responsive sizing/placement of
  control overlays across portrait, landscape, and desktop viewports.
- **In Rocq (game core):** interpreting the input snapshot — applying
  movement vectors, look deltas, and action flags to game state.  Rocq
  does not know or care whether the input originated from a physical
  keyboard or a virtual joystick.

This split keeps mobile UX iteration fast (HTML/CSS/JS changes, no Rocq
recompilation) while ensuring gameplay semantics are identical across
platforms.

### Layout and shell UI

The responsive layout (portrait/landscape/desktop media queries), the
drag-to-resize handle, the status bar, error display, and the JsCoq IDE
panel chrome are all JavaScript/CSS.  These are outside the game's
logical boundary entirely.

## The JS-to-Rocq bridge

The bridge must stay **sqlite-small**: one versioned struct of functions,
plain data records, and one implementation module that hides the
JsCoq-specific eval plumbing from the rest of the browser code.

The browser shell should depend on a bridge shaped like this:

```text
bridge_v1 =
  { version    : 1
  ; load_world : bsp_bytes -> render_snapshot
  ; step       : input_snapshot -> render_snapshot
  ; reset      : unit -> render_snapshot
  }
```

Where:

- [load_world] is called once after JavaScript fetches the BSP bytes.
  Rocq parses the BSP, selects the spawn point, builds the authoritative
  world/game state, and returns the first [render_snapshot].
- [step] is called once per animation-frame tick.  JavaScript passes the
  current [input_snapshot]; Rocq advances the authoritative state and
  returns the next [render_snapshot].
- [reset] restores the initial state for the currently loaded world and
  returns its initial [render_snapshot].  This keeps restart logic out of
  JavaScript and avoids reparsing when only the dynamic state should be
  rewound.

The payload types are the Rocq records in [theories/GameState.v]:
[input_snapshot] for JS -> Rocq and [render_snapshot] for Rocq -> JS.
They should stay boring: flat numbers, booleans, and lists that can be
serialized without a generic RPC layer.

This is intentionally **not** a general foreign-function interface.  In
particular, the bridge must not grow:

- a JS callback registry that Rocq can invoke arbitrarily;
- per-feature "helper" methods for camera math, collision probes, or
  renderer decisions that duplicate Rocq-owned logic;
- raw access to Rocq internals from random browser modules;
- texture, shader, or WebGL resources crossing the boundary unless they
  become logically necessary for Rocq itself.

Implementation rule: all stringly-typed interaction with the JsCoq eval
API lives in one JavaScript bridge module.  The rest of `docs/` should
see only the struct-of-functions above.  If a new gameplay need appears,
prefer extending the Rocq data model behind [load_world]/[step]/[reset]
before adding another bridge entry point.

The core architectural constraint remains: **all game-logic-relevant data
flows through Rocq, and JavaScript only reads render output — it never
computes game state independently.**

## JsCoq as part of the shipped experience

JsCoq is not just a build tool — it is part of what the user sees.  The
GitHub Pages deployment includes the JsCoq IDE panel where users can read
and interact with the Rocq source that powers the game running next to
it.  The JsCoq kernel boots on page load, interprets the Rocq theories,
and stays resident to run the game loop.

This means JsCoq availability and load performance directly affect the
user experience.  The current CDN-based approach (jsDelivr, v0.17.1)
keeps deployment simple.  If CDN reliability becomes a problem, vendoring
JsCoq into `docs/` is an option but not required for v1.

## Out of scope for v1

The following are explicitly deferred to issue #18 (v2 and beyond):

- Audio (Web Audio API integration)
- Multiple levels / level selection
- HUD beyond minimal controls
- Multiplayer or network play
- Mod support
- Rocq extraction as an optimization path
