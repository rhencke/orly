(** * Game-state and render-snapshot types for the Rocq game core.

    Defines the per-tick data types that flow between the JavaScript
    browser shell and the Rocq game core, as specified in
    ARCHITECTURE.md.  These records are the data payloads carried by the
    minimal JS-to-Rocq struct-of-functions bridge:

    - [input_snapshot]: packed input state sent from JS each tick
      (key/button flags, mouse/touch deltas, delta time).

    - [game_state]: the authoritative game state owned by Rocq —
      player position, orientation, velocity, and entity state.
      JavaScript never independently tracks or modifies this.

    - [render_snapshot]: the per-frame output Rocq sends to JS —
      camera transform, visible surface list, entity positions.
      JavaScript uses this to issue WebGL draw calls.

    The function side of that bridge stays intentionally tiny:
    [load_world], [step], and [reset].  The records in this file are the
    only game-data payloads those functions should exchange.

    All spatial quantities use [Q] rationals, matching the BSP parser
    conventions in [BspPlaneVertex].  Angles are in degrees (Q). *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Bsp Require Import BspEntity.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** 3D vector                                                       *)
(* ------------------------------------------------------------------ *)

(** A 3D vector of rationals, used for positions, velocities, and
    normals throughout the game core. *)
Record vec3 : Type := mk_vec3
  { v3_x : Q
  ; v3_y : Q
  ; v3_z : Q
  }.

(** The zero vector. *)
Definition vec3_zero : vec3 := mk_vec3 0 0 0.

(* ------------------------------------------------------------------ *)
(** ** Input snapshot (JS -> Rocq, per tick)                            *)
(* ------------------------------------------------------------------ *)

(** The input state JavaScript packs and sends to Rocq each frame.
    Desktop keyboard/mouse and mobile virtual-joystick/touch both
    produce the same snapshot format — Rocq does not know the input
    source. *)
Record input_snapshot : Type := mk_input_snapshot
  { is_forward    : bool   (** W / joystick up *)
  ; is_back       : bool   (** S / joystick down *)
  ; is_left       : bool   (** A / joystick left *)
  ; is_right      : bool   (** D / joystick right *)
  ; is_jump       : bool   (** space / jump button *)
  ; is_yaw_delta  : Q      (** horizontal look delta, degrees *)
  ; is_pitch_delta: Q      (** vertical look delta, degrees *)
  ; is_dt_ms      : Z      (** delta time in milliseconds *)
  }.

(** A zero-input snapshot: no keys pressed, no look movement, zero
    delta time.  Useful as the initial "no input yet" state. *)
Definition input_snapshot_zero : input_snapshot :=
  mk_input_snapshot false false false false false 0 0 0.

(* ------------------------------------------------------------------ *)
(** ** Entity state                                                     *)
(* ------------------------------------------------------------------ *)

(** Per-entity runtime state for triggers and interactive objects.
    For v1, the primary entity type is [trigger_push] (jump pads). *)
Record entity_state : Type := mk_entity_state
  { es_entity_index : Z       (** index into [bf_entities] *)
  ; es_origin       : vec3    (** world-space position *)
  ; es_active       : bool    (** whether the trigger is armed *)
  }.

(* ------------------------------------------------------------------ *)
(** ** Render metadata input (JS -> Rocq, at world load)               *)
(* ------------------------------------------------------------------ *)

(** Minimal texture metadata the JS shell sends into Rocq so the
    authoritative render snapshot can decide which faces are drawable. *)
Record render_texture_input : Type := mk_render_texture_input
  { rti_name     : list Z
  ; rti_flags    : Z
  ; rti_contents : Z
  }.

(** Minimal face metadata Rocq needs to decide whether a face belongs in
    the render snapshot. *)
Record render_face_input : Type := mk_render_face_input
  { rfi_texture     : Z
  ; rfi_type        : Z
  ; rfi_n_vertexes  : Z
  ; rfi_n_meshverts : Z
  ; rfi_size_x      : Z
  ; rfi_size_y      : Z
  }.

Definition face_type_polygon : Z := 1.
Definition face_type_patch   : Z := 2.
Definition face_type_mesh    : Z := 3.

Definition contents_playerclip : Z := 65536.
Definition contents_monsterclip : Z := 131072.
Definition surf_nodraw : Z := 128.
Definition surf_sky : Z := 4.

Definition val_noshader : list Z :=
  [110; 111; 115; 104; 97; 100; 101; 114].

Definition bit_setb (bits mask : Z) : bool :=
  negb (Z.land bits mask =? 0).

Definition texture_visibleb (tx : render_texture_input) : bool :=
  if list_Z_eqb (rti_name tx) [] then false else
  if list_Z_eqb (rti_name tx) val_noshader then false else
  if (bit_setb (rti_flags tx) surf_nodraw ||
      bit_setb (rti_flags tx) surf_sky)%bool then false else
  if (bit_setb (rti_contents tx) contents_playerclip ||
      bit_setb (rti_contents tx) contents_monsterclip)%bool then false else
  true.

Definition valid_patch_gridb (f : render_face_input) : bool :=
  negb ((rfi_size_x f <? 3) ||
        (rfi_size_y f <? 3) ||
        Z.even (rfi_size_x f) ||
        Z.even (rfi_size_y f)).

Definition nth_z {A : Type} (ls : list A) (i : Z) : option A :=
  if i <? 0 then None else nth_error ls (Z.to_nat i).

Definition renderable_faceb
    (textures : list render_texture_input) (f : render_face_input) : bool :=
  match nth_z textures (rfi_texture f) with
  | None => false
  | Some tx =>
      if texture_visibleb tx then
        match rfi_type f with
        | 1 => negb (rfi_n_meshverts f =? 0)
        | 2 => negb (rfi_n_vertexes f =? 0) && valid_patch_gridb f
        | 3 => negb (rfi_n_meshverts f =? 0)
        | _ => false
        end
      else false
  end.

Fixpoint visible_face_indices_aux
    (faces : list render_face_input)
    (textures : list render_texture_input)
    (idx : Z) : list Z :=
  match faces with
  | [] => []
  | f :: rest =>
      let rest_indices := visible_face_indices_aux rest textures (idx + 1) in
      if renderable_faceb textures f
      then idx :: rest_indices
      else rest_indices
  end.

Definition visible_face_indices
    (faces : list render_face_input)
    (textures : list render_texture_input) : list Z :=
  visible_face_indices_aux faces textures 0.

(* ------------------------------------------------------------------ *)
(** ** Game state (Rocq-owned, authoritative)                          *)
(* ------------------------------------------------------------------ *)

(** The complete authoritative game state.  JavaScript never
    independently tracks or recomputes any of these fields — it reads
    only the [render_snapshot] produced from this state each tick. *)
Record game_state : Type := mk_game_state
  { gs_position : vec3           (** player world-space position *)
  ; gs_velocity : vec3           (** player velocity *)
  ; gs_yaw      : Q              (** horizontal orientation, degrees *)
  ; gs_pitch    : Q              (** vertical orientation, degrees, ±89 *)
  ; gs_on_ground: bool           (** whether the player is grounded *)
  ; gs_entities : list entity_state (** runtime entity/trigger state *)
  ; gs_tick     : Z              (** cumulative tick count *)
  }.

(** Initial game state at the origin with no velocity.  Real games
    will override position/orientation from spawn-point selection. *)
Definition game_state_init : game_state :=
  mk_game_state vec3_zero vec3_zero 0 0 true [] 0.

(* ------------------------------------------------------------------ *)
(** ** Render snapshot (Rocq -> JS, per tick)                           *)
(* ------------------------------------------------------------------ *)

(** The per-frame output Rocq sends to JavaScript.  JS uses this to
    set up the camera and issue WebGL draw calls.  Rocq decides
    **what** to draw; JavaScript decides **how**. *)
Record render_snapshot : Type := mk_render_snapshot
  { rs_camera_pos   : vec3     (** eye position in world space *)
  ; rs_camera_yaw   : Q        (** horizontal orientation, degrees *)
  ; rs_camera_pitch : Q        (** vertical orientation, degrees *)
  ; rs_visible_faces: list Z   (** face indices to draw *)
  ; rs_entity_positions : list (Z * vec3) (** entity index × position *)
  }.

(** An empty render snapshot at the origin with nothing visible. *)
Definition render_snapshot_empty : render_snapshot :=
  mk_render_snapshot vec3_zero 0 0 [] [].

(* ------------------------------------------------------------------ *)
(** ** Snapshot extraction                                              *)
(* ------------------------------------------------------------------ *)

(** [extract_snapshot gs] produces a render snapshot from the current
    game state.  For now this copies camera state directly; visibility
    determination (PVS/frustum culling) will refine [rs_visible_faces]
    once the BSP traversal logic lands. *)
Definition extract_snapshot (gs : game_state) : render_snapshot :=
  mk_render_snapshot
    (gs_position gs)
    (gs_yaw gs)
    (gs_pitch gs)
    []                (* visible faces — PVS/culling not yet implemented *)
    (map (fun es => (es_entity_index es, es_origin es)) (gs_entities gs)).

Definition extract_snapshot_with_visible_faces
    (gs : game_state) (visible_faces : list Z) : render_snapshot :=
  mk_render_snapshot
    (gs_position gs)
    (gs_yaw gs)
    (gs_pitch gs)
    visible_faces
    (map (fun es => (es_entity_index es, es_origin es)) (gs_entities gs)).

(** Serialize a rational as numerator/denominator [Z] words so the
    JS bridge can decode camera state without parsing Rocq internals. *)
Definition q_words (q : Q) : list Z :=
  [Qnum q; Z.pos (Qden q)].

(** Serialize the camera portion of a render snapshot as five rational
    values: position xyz, yaw, and pitch. *)
Definition render_snapshot_camera_words (rs : render_snapshot) : list Z :=
  let pos := rs_camera_pos rs in
  q_words (v3_x pos) ++
  q_words (v3_y pos) ++
  q_words (v3_z pos) ++
  q_words (rs_camera_yaw rs) ++
  q_words (rs_camera_pitch rs).

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Extracting a snapshot from the initial state yields the empty
    snapshot. *)
Lemma extract_snapshot_init :
  extract_snapshot game_state_init = render_snapshot_empty.
Proof. reflexivity. Qed.

(** The initial game state has tick count 0. *)
Lemma game_state_init_tick :
  gs_tick game_state_init = 0.
Proof. reflexivity. Qed.

(** The initial game state is grounded. *)
Lemma game_state_init_grounded :
  gs_on_ground game_state_init = true.
Proof. reflexivity. Qed.

(** The zero input snapshot has zero delta time. *)
Lemma input_snapshot_zero_dt :
  is_dt_ms input_snapshot_zero = 0.
Proof. reflexivity. Qed.

(** The zero input snapshot has no keys pressed. *)
Lemma input_snapshot_zero_no_keys :
  is_forward input_snapshot_zero = false /\
  is_back    input_snapshot_zero = false /\
  is_left    input_snapshot_zero = false /\
  is_right   input_snapshot_zero = false /\
  is_jump    input_snapshot_zero = false.
Proof. repeat split; reflexivity. Qed.

(** Entity count is preserved through snapshot extraction. *)
Lemma extract_snapshot_entity_count : forall gs,
  length (rs_entity_positions (extract_snapshot gs)) =
  length (gs_entities gs).
Proof.
  intros gs. unfold extract_snapshot. simpl.
  apply length_map.
Qed.

(** The camera position in the snapshot matches the game state. *)
Lemma extract_snapshot_camera_pos : forall gs,
  rs_camera_pos (extract_snapshot gs) = gs_position gs.
Proof. reflexivity. Qed.

(** The camera yaw in the snapshot matches the game state. *)
Lemma extract_snapshot_camera_yaw : forall gs,
  rs_camera_yaw (extract_snapshot gs) = gs_yaw gs.
Proof. reflexivity. Qed.

(** The camera pitch in the snapshot matches the game state. *)
Lemma extract_snapshot_camera_pitch : forall gs,
  rs_camera_pitch (extract_snapshot gs) = gs_pitch gs.
Proof. reflexivity. Qed.

(** Camera-word serialization always yields five rational pairs. *)
Lemma render_snapshot_camera_words_length : forall rs,
  length (render_snapshot_camera_words rs) = 10%nat.
Proof.
  intros rs. unfold render_snapshot_camera_words, q_words.
  simpl. reflexivity.
Qed.

Lemma extract_snapshot_with_visible_faces_camera_pos : forall gs visible_faces,
  rs_camera_pos (extract_snapshot_with_visible_faces gs visible_faces) =
  gs_position gs.
Proof. reflexivity. Qed.

Lemma extract_snapshot_with_visible_faces_visible_faces : forall gs visible_faces,
  rs_visible_faces (extract_snapshot_with_visible_faces gs visible_faces) =
  visible_faces.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Spawn-point extraction from entity data                          *)
(* ------------------------------------------------------------------ *)

(** Parse a "x y z" origin value string (ASCII byte list) into a
    [vec3].  Each component is a signed decimal integer, separated by
    spaces.  Returns [None] if the format does not match. *)
Definition parse_origin_vec3 (cs : list Z) : option vec3 :=
  match parse_int cs with
  | None          => None
  | Some (x, cs1) =>
      match cs1 with
      | 32 :: cs2 =>
          match parse_int cs2 with
          | None          => None
          | Some (y, cs3) =>
              match cs3 with
              | 32 :: cs4 =>
                  match parse_int cs4 with
                  | None        => None
                  | Some (z, _) =>
                      Some (mk_vec3 (inject_Z x) (inject_Z y) (inject_Z z))
                  end
              | _ => None
              end
          end
      | _ => None
      end
  end.

(** True iff entity [e] has classname [info_player_deathmatch]. *)
Definition is_spawn_entity (e : bsp_entity) : bool :=
  match entity_get_val e key_classname with
  | Some v => list_Z_eqb v val_info_player_deathmatch
  | None   => false
  end.

(** Extract the world-space origin from a spawn entity.
    Returns [None] if no [origin] key is present or the value is
    unparseable. *)
Definition spawn_origin_of_entity (e : bsp_entity) : option vec3 :=
  match entity_get_val e key_origin with
  | Some v => parse_origin_vec3 v
  | None   => None
  end.

(** Extract the yaw angle (degrees) from an entity's [angle] key.
    Returns [0] if the key is absent or the value is unparseable. *)
Definition spawn_yaw_of_entity (e : bsp_entity) : Q :=
  match entity_get_val e key_angle with
  | Some v =>
      match parse_int v with
      | Some (a, _) => inject_Z a
      | None        => 0
      end
  | None => 0
  end.

(** [select_spawn_point entities] returns the position and yaw of the
    first [info_player_deathmatch] entity that has a parseable [origin].
    Returns [None] if no such entity exists. *)
Fixpoint select_spawn_point (entities : list bsp_entity)
    : option (vec3 * Q) :=
  match entities with
  | []       => None
  | e :: rest =>
      if is_spawn_entity e then
        match spawn_origin_of_entity e with
        | Some pos => Some (pos, spawn_yaw_of_entity e)
        | None     => select_spawn_point rest
        end
      else select_spawn_point rest
  end.

(** Initialise a [game_state] from parsed entity data.  The player
    starts at the first [info_player_deathmatch] spawn point found in
    [entities]; if none exists, falls back to [game_state_init]. *)
Definition game_state_from_entities (entities : list bsp_entity)
    : game_state :=
  match select_spawn_point entities with
  | Some (pos, yaw) => mk_game_state pos vec3_zero yaw 0 true [] 0
  | None            => game_state_init
  end.

(** End-to-end helper for the browser bridge: derive the initial camera
    words directly from parsed entity data. *)
Definition initial_camera_words_from_entities (entities : list bsp_entity)
    : list Z :=
  render_snapshot_camera_words
    (extract_snapshot (game_state_from_entities entities)).

Definition initial_render_snapshot_from_inputs
    (entities : list bsp_entity)
    (faces : list render_face_input)
    (textures : list render_texture_input)
    : render_snapshot :=
  extract_snapshot_with_visible_faces
    (game_state_from_entities entities)
    (visible_face_indices faces textures).

Definition initial_camera_words_from_inputs
    (entities : list bsp_entity)
    (faces : list render_face_input)
    (textures : list render_texture_input)
    : list Z :=
  render_snapshot_camera_words
    (initial_render_snapshot_from_inputs entities faces textures).

Definition initial_visible_faces_from_inputs
    (entities : list bsp_entity)
    (faces : list render_face_input)
    (textures : list render_texture_input)
    : list Z :=
  rs_visible_faces
    (initial_render_snapshot_from_inputs entities faces textures).

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas for spawn-point selection                     *)
(* ------------------------------------------------------------------ *)

(** Parsing the canonical "0 0 24" spawn height produces the correct
    vec3. *)
Lemma parse_origin_example :
  parse_origin_vec3 [48; 32; 48; 32; 50; 52] =
    Some (mk_vec3 0 0 24).
Proof. vm_compute. reflexivity. Qed.

(** Negative origin components are handled correctly. *)
Lemma parse_origin_neg_example :
  parse_origin_vec3 [45; 52; 56; 32; 49; 50; 56; 32; 45; 56] =
    Some (mk_vec3 (inject_Z (-48)) (inject_Z 128) (inject_Z (-8))).
Proof. vm_compute. reflexivity. Qed.

(** An empty entity list has no spawn points. *)
Lemma select_spawn_point_nil :
  select_spawn_point [] = None.
Proof. reflexivity. Qed.

(** Falling back on an empty entity list gives [game_state_init]. *)
Lemma game_state_from_entities_nil_fallback :
  game_state_from_entities [] = game_state_init.
Proof. reflexivity. Qed.

(** A spawn-derived state has tick count 0. *)
Lemma game_state_from_entities_tick : forall entities,
  gs_tick (game_state_from_entities entities) = 0.
Proof.
  intros entities. unfold game_state_from_entities.
  destruct (select_spawn_point entities) as [[[px py pz] yaw] |];
    reflexivity.
Qed.

(** A spawn-derived state has zero velocity. *)
Lemma game_state_from_entities_velocity : forall entities,
  gs_velocity (game_state_from_entities entities) = vec3_zero.
Proof.
  intros entities. unfold game_state_from_entities.
  destruct (select_spawn_point entities) as [[[px py pz] yaw] |];
    reflexivity.
Qed.

(** A spawn-derived state starts grounded. *)
Lemma game_state_from_entities_grounded : forall entities,
  gs_on_ground (game_state_from_entities entities) = true.
Proof.
  intros entities. unfold game_state_from_entities.
  destruct (select_spawn_point entities) as [[[px py pz] yaw] |];
    reflexivity.
Qed.

(** The bridge helper always yields the five serialized camera values. *)
Lemma initial_camera_words_from_entities_length : forall entities,
  length (initial_camera_words_from_entities entities) = 10%nat.
Proof.
  intros entities. unfold initial_camera_words_from_entities.
  apply render_snapshot_camera_words_length.
Qed.

Lemma texture_visibleb_empty :
  texture_visibleb (mk_render_texture_input [] 0 0) = false.
Proof. reflexivity. Qed.

Lemma texture_visibleb_noshader :
  texture_visibleb (mk_render_texture_input val_noshader 0 0) = false.
Proof. reflexivity. Qed.

Lemma valid_patch_gridb_even_width : forall tex nv nm h,
  valid_patch_gridb (mk_render_face_input tex face_type_patch nv nm 4 h) = false.
Proof.
  intros. unfold valid_patch_gridb. simpl.
  destruct (h <? 3); reflexivity.
Qed.

Lemma visible_face_indices_aux_length_le : forall faces textures start,
  (length (visible_face_indices_aux faces textures start) <= length faces)%nat.
Proof.
  induction faces as [| f rest IH]; intros textures start; simpl.
  - lia.
  - destruct (renderable_faceb textures f); simpl.
    + apply le_n_S. exact (IH textures (start + 1)).
    + apply le_S. exact (IH textures (start + 1)).
Qed.

Lemma visible_face_indices_length_le : forall faces textures,
  (length (visible_face_indices faces textures) <= length faces)%nat.
Proof.
  intros faces textures. unfold visible_face_indices.
  apply visible_face_indices_aux_length_le.
Qed.

Lemma visible_face_indices_aux_bounds :
  forall faces textures start i,
    In i (visible_face_indices_aux faces textures start) ->
    start <= i < start + Z.of_nat (length faces).
Proof.
  induction faces as [| f rest IH]; intros textures start i Hin; simpl in *.
  - contradiction.
  - destruct (renderable_faceb textures f) eqn:Hrender.
    + simpl in Hin. destruct Hin as [-> | Hin].
      * simpl. lia.
      * specialize (IH textures (start + 1) i Hin). simpl in IH. lia.
    + specialize (IH textures (start + 1) i Hin). simpl in IH. lia.
Qed.

Lemma initial_visible_faces_from_inputs_in_bounds :
  forall entities faces textures i,
    In i (initial_visible_faces_from_inputs entities faces textures) ->
    0 <= i < Z.of_nat (length faces).
Proof.
  intros entities faces textures i Hin.
  unfold initial_visible_faces_from_inputs, initial_render_snapshot_from_inputs.
  simpl in Hin.
  apply (visible_face_indices_aux_bounds faces textures 0 i) in Hin.
  simpl in Hin. lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** World-state serialization and frame stepping                    *)
(* ------------------------------------------------------------------ *)

(** Number of [Z] words produced by [game_state_to_words] for a
    game state with an empty entity list. *)
Definition game_state_words_count : nat := 18.

(** Serialize a [game_state] to a flat [list Z] suitable for
    round-tripping through the JS bridge.  The entity list is
    omitted; v1 entities carry no per-step dynamic state that
    needs crossing the bridge boundary.

    Word layout (18 entries):
    <<
       0  px_num   1  px_den
       2  py_num   3  py_den
       4  pz_num   5  pz_den
       6  vx_num   7  vx_den
       8  vy_num   9  vy_den
      10  vz_num  11  vz_den
      12 yaw_num  13 yaw_den
      14 pch_num  15 pch_den
      16 on_ground          (0 = airborne, 1 = grounded)
      17 tick
    >>
*)
Definition game_state_to_words (gs : game_state) : list Z :=
  q_words (v3_x (gs_position gs)) ++
  q_words (v3_y (gs_position gs)) ++
  q_words (v3_z (gs_position gs)) ++
  q_words (v3_x (gs_velocity gs)) ++
  q_words (v3_y (gs_velocity gs)) ++
  q_words (v3_z (gs_velocity gs)) ++
  q_words (gs_yaw gs) ++
  q_words (gs_pitch gs) ++
  [(if gs_on_ground gs then 1 else 0)] ++
  [gs_tick gs].

(** Reconstruct a [game_state] from the word list produced by
    [game_state_to_words].  Returns [None] on a malformed list or
    any zero/negative denominator. *)
Definition game_state_from_words (ws : list Z) : option game_state :=
  match ws with
  | [px_n; px_d; py_n; py_d; pz_n; pz_d;
     vx_n; vx_d; vy_n; vy_d; vz_n; vz_d;
     yaw_n; yaw_d; pitch_n; pitch_d;
     on_ground; tick] =>
      if (px_d <=? 0) || (py_d <=? 0) || (pz_d <=? 0) ||
         (vx_d <=? 0) || (vy_d <=? 0) || (vz_d <=? 0) ||
         (yaw_d <=? 0) || (pitch_d <=? 0)
      then None
      else
        Some (mk_game_state
          (mk_vec3 (Qmake px_n (Z.to_pos px_d))
                   (Qmake py_n (Z.to_pos py_d))
                   (Qmake pz_n (Z.to_pos pz_d)))
          (mk_vec3 (Qmake vx_n (Z.to_pos vx_d))
                   (Qmake vy_n (Z.to_pos vy_d))
                   (Qmake vz_n (Z.to_pos vz_d)))
          (Qmake yaw_n   (Z.to_pos yaw_d))
          (Qmake pitch_n (Z.to_pos pitch_d))
          (negb (on_ground =? 0))
          []
          tick)
  | _ => None
  end.

(** Advance the world by one frame.  For this phase the only change
    is incrementing [gs_tick]; movement, look, and collision logic
    will be added in subsequent tasks. *)
Definition step_world (gs : game_state) (_input : input_snapshot)
    : game_state :=
  mk_game_state
    (gs_position gs)
    (gs_velocity gs)
    (gs_yaw gs)
    (gs_pitch gs)
    (gs_on_ground gs)
    (gs_entities gs)
    (gs_tick gs + 1).

(** Bridge-facing word-level entry point for per-frame stepping.
    Takes the current game state as a word list (from
    [game_state_to_words]) plus the packed input snapshot, and
    returns the updated word list.  A malformed input word list is
    passed through unchanged. *)
Definition step_world_words (ws : list Z) (input : input_snapshot)
    : list Z :=
  match game_state_from_words ws with
  | None    => ws
  | Some gs => game_state_to_words (step_world gs input)
  end.

(** Bridge-facing entry point for [load_world].  Returns the initial
    game-state word list from parsed entity data.  Used alongside
    [initial_visible_faces_from_inputs] to populate the first
    render snapshot. *)
Definition initial_game_state_words_from_entities
    (entities : list bsp_entity) : list Z :=
  game_state_to_words (game_state_from_entities entities).

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas for world stepping                           *)
(* ------------------------------------------------------------------ *)

Lemma game_state_to_words_length : forall gs,
  length (game_state_to_words gs) = game_state_words_count.
Proof.
  intros gs. unfold game_state_to_words, q_words, game_state_words_count.
  repeat rewrite length_app. simpl. reflexivity.
Qed.

(** Stepping preserves position. *)
Lemma step_world_position : forall gs input,
  gs_position (step_world gs input) = gs_position gs.
Proof. reflexivity. Qed.

(** Stepping preserves velocity. *)
Lemma step_world_velocity : forall gs input,
  gs_velocity (step_world gs input) = gs_velocity gs.
Proof. reflexivity. Qed.

(** Stepping preserves orientation. *)
Lemma step_world_yaw : forall gs input,
  gs_yaw (step_world gs input) = gs_yaw gs.
Proof. reflexivity. Qed.

Lemma step_world_pitch : forall gs input,
  gs_pitch (step_world gs input) = gs_pitch gs.
Proof. reflexivity. Qed.

(** Stepping increments the tick counter. *)
Lemma step_world_tick : forall gs input,
  gs_tick (step_world gs input) = gs_tick gs + 1.
Proof. reflexivity. Qed.

(** Helper: [Z.pos p] is never [<=? 0]. *)
Lemma Z_pos_leb_0 : forall p : positive,
  (Z.pos p <=? 0) = false.
Proof.
  intro p. apply Z.leb_gt. apply Pos2Z.is_pos.
Qed.

(** [game_state_to_words] round-trips through [game_state_from_words]
    for states with an empty entity list. *)
Lemma game_state_roundtrip : forall gs,
  gs_entities gs = [] ->
  game_state_from_words (game_state_to_words gs) = Some gs.
Proof.
  intros gs Hnil.
  destruct gs as [[px py pz] [vx vy vz] yaw pitch grounded ents tick].
  simpl in Hnil. subst ents.
  (* Destruct each Q into num/den so Z.to_pos (Z.pos den) = den by reflexivity. *)
  destruct px as [pxn pxd], py as [pyn pyd], pz as [pzn pzd].
  destruct vx as [vxn vxd], vy as [vyn vyd], vz as [vzn vzd].
  destruct yaw as [yn yd], pitch as [pn pd].
  unfold game_state_to_words, game_state_from_words, q_words. simpl.
  repeat rewrite Z_pos_leb_0. simpl.
  destruct grounded; reflexivity.
Qed.

(** Serialized word count matches [game_state_words_count]. *)
Lemma initial_game_state_words_from_entities_length : forall entities,
  length (initial_game_state_words_from_entities entities) =
  game_state_words_count.
Proof.
  intros entities. unfold initial_game_state_words_from_entities.
  apply game_state_to_words_length.
Qed.
