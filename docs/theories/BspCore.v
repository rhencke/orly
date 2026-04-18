(** * Binary parsing primitives for the Q3 BSP loader.

    Little-endian integer and IEEE 754 single-precision float readers
    over a flat byte sequence.  All functions return [option] so callers
    can propagate parse failures without exceptions.

    These primitives are the only code that touches raw bytes; all lump
    parsers call these and never index into [bytes] directly. *)

Require Import List.
Require Import ZArith.
Require Import QArith.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Byte sequences                                                   *)
(* ------------------------------------------------------------------ *)

(** Raw BSP input is a flat [list Z], one element per byte, each in
    [[0, 255]].  [Z] is used so arithmetic never requires numeric coercions. *)
Definition bytes := list Z.

(** [byte_at bs i] retrieves the byte at index [i], or [None]. *)
Definition byte_at (bs : bytes) (i : nat) : option Z :=
  nth_error bs i.

(** [take4 bs i] retrieves four consecutive bytes starting at [i],
    or [None] if the sequence is too short. *)
Definition take4 (bs : bytes) (i : nat) : option (Z * Z * Z * Z) :=
  match byte_at bs i,           byte_at bs (i + 1)%nat,
        byte_at bs (i + 2)%nat, byte_at bs (i + 3)%nat with
  | Some b0, Some b1, Some b2, Some b3 => Some (b0, b1, b2, b3)
  | _, _, _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Unsigned integer readers                                         *)
(* ------------------------------------------------------------------ *)

Definition get_u8 (bs : bytes) (i : nat) : option Z :=
  byte_at bs i.

(** [get_u16_le bs i] reads an unsigned 16-bit little-endian value. *)
Definition get_u16_le (bs : bytes) (i : nat) : option Z :=
  match byte_at bs i, byte_at bs (i + 1)%nat with
  | Some b0, Some b1 => Some (b0 + b1 * 256)
  | _, _ => None
  end.

(** [get_u32_le bs i] reads an unsigned 32-bit little-endian value. *)
Definition get_u32_le (bs : bytes) (i : nat) : option Z :=
  match take4 bs i with
  | None => None
  | Some (b0, b1, b2, b3) => Some (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
  end.

(* ------------------------------------------------------------------ *)
(** ** Signed integer readers                                           *)
(* ------------------------------------------------------------------ *)

(** Two's-complement conversion for 16-bit values: if the unsigned
    value has bit 15 set, subtract [2^16] to recover the signed value. *)
Definition to_i16 (u : Z) : Z :=
  if 32768 <=? u then u - 65536 else u.

(** [get_i16_le bs i] reads a signed 16-bit little-endian value. *)
Definition get_i16_le (bs : bytes) (i : nat) : option Z :=
  match get_u16_le bs i with
  | None   => None
  | Some u => Some (to_i16 u)
  end.

(** Two's-complement: if the unsigned value has bit 31 set,
    subtract [2^32] to recover the signed value. *)
Definition to_i32 (u : Z) : Z :=
  if 2147483648 <=? u then u - 4294967296 else u.

(** [get_i32_le bs i] reads a signed 32-bit little-endian value.
    This is the most common integer type in the Q3 BSP format. *)
Definition get_i32_le (bs : bytes) (i : nat) : option Z :=
  match get_u32_le bs i with
  | None   => None
  | Some u => Some (to_i32 u)
  end.

(* ------------------------------------------------------------------ *)
(** ** IEEE 754 single-precision float reader                           *)
(* ------------------------------------------------------------------ *)

(** [q_pow2 n] returns the rational [2^n].
    For negative [n] this is the fraction [1 / 2^|n|]. *)
Definition q_pow2 (n : Z) : Q :=
  if 0 <=? n
  then inject_Z (2 ^ n)
  else Qmake 1 (Z.to_pos (2 ^ (- n))).

(** [decode_f32_bits u] decodes a raw 32-bit IEEE 754 binary32 bit
    pattern [u] to an exact rational value.

    - Exponent field = 255 (infinities, NaNs): mapped to [0].  Valid
      BSP geometry never contains non-finite coordinate values.
    - Exponent field = 0 (subnormals): handled correctly.
    - All other exponents: normal path. *)
Definition decode_f32_bits (u : Z) : Q :=
  let sign    := if Z.shiftr u 31 =? 0 then inject_Z 1 else inject_Z (-1) in
  let exp_raw := Z.land (Z.shiftr u 23) 0xFF in
  let mant    := Z.land u 0x7FFFFF in
  if exp_raw =? 255 then
    inject_Z 0
  else if exp_raw =? 0 then
    (* subnormal: (-1)^s × mant × 2^(−149) *)
    Qmult sign (Qmult (inject_Z mant) (q_pow2 (-149)))
  else
    (* normal: (-1)^s × (2^23 + mant) × 2^(exp_raw − 150) *)
    Qmult sign (Qmult (inject_Z (2 ^ 23 + mant)) (q_pow2 (exp_raw - 150))).

(** [get_f32_le bs i] reads four bytes at offset [i] as a little-endian
    IEEE 754 binary32 float, returned as an exact rational. *)
Definition get_f32_le (bs : bytes) (i : nat) : option Q :=
  match get_u32_le bs i with
  | None   => None
  | Some u => Some (decode_f32_bits u)
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Byte reads from a singleton list succeed. *)

(** Two zero bytes decode as signed 0. *)

(** All-ones bytes are [−1] in 16-bit two's complement. *)

(** Four zero bytes decode as [0]. *)

(** Little-endian byte order: the first byte is least significant. *)

(** All-ones bytes are [−1] in two's complement. *)

(** [0x3F800000] is the IEEE 754 binary32 encoding of [1.0]. *)

(** [0x00000000] encodes [0.0]. *)

(** [0xBF800000] encodes [−1.0]. *)
(** * Q3 BSP entity lump parser -- text to typed key-value structures.

    The entity lump (lump index 0) is the only text-based lump in the
    Q3 BSP format.  It contains a null-terminated string of entity
    definitions in a brace-delimited, quoted key-value syntax.

    Example (using single quotes for illustration):

      [open-brace]
      'classname' 'info_player_deathmatch'
      'origin' '0 0 24'
      [close-brace]

    This module defines:
    - [bsp_entity]: a single entity as a list of (key, value) pairs.
    - A character-level scanner that tokenises the raw byte list into
      quoted strings, open/close braces, and whitespace.
    - [parse_entities]: top-level parser from byte list to entity list.

    All characters are [Z] values representing ASCII code points. *)

Require Import List.
Require Import ZArith.
Require Import Bool.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Entity type                                                      *)
(* ------------------------------------------------------------------ *)

(** A key-value pair in an entity definition. *)
Definition entity_kv : Type := (list Z * list Z)%type.

(** A single entity is an ordered list of key-value pairs. *)
Definition bsp_entity : Type := list entity_kv.

(* ------------------------------------------------------------------ *)
(** ** ASCII helpers                                                     *)
(* ------------------------------------------------------------------ *)

Definition is_whitespace (c : Z) : bool :=
  (c =? 32)  ||  (* space *)
  (c =? 9)   ||  (* tab *)
  (c =? 10)  ||  (* newline *)
  (c =? 13).     (* carriage return *)

Definition ascii_quote     : Z := 34.  (** double quote *)
Definition ascii_open      : Z := 123. (** open brace *)
Definition ascii_close     : Z := 125. (** close brace *)
Definition ascii_null      : Z := 0.

(* ------------------------------------------------------------------ *)
(** ** Scanner: skip whitespace                                         *)
(* ------------------------------------------------------------------ *)

(** [skip_ws cs] drops leading whitespace and null bytes from [cs]. *)
Fixpoint skip_ws (cs : list Z) : list Z :=
  match cs with
  | c :: rest =>
      if is_whitespace c || (c =? ascii_null) then skip_ws rest
      else cs
  | [] => []
  end.

(* ------------------------------------------------------------------ *)
(** ** Scanner: read a quoted string                                    *)
(* ------------------------------------------------------------------ *)

(** [scan_quoted cs acc fuel] collects characters between double
    quotes.  [cs] begins just after the opening quote.  Returns the
    collected characters (reversed) and the remaining input after the
    closing quote, or [None] if no closing quote is found within
    [fuel] characters. *)
Fixpoint scan_quoted (cs : list Z) (acc : list Z) (fuel : nat)
    : option (list Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      match cs with
      | [] => None
      | c :: rest =>
          if c =? ascii_quote then Some (rev acc, rest)
          else scan_quoted rest (c :: acc) fuel'
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Scanner: read one key-value pair                                 *)
(* ------------------------------------------------------------------ *)

(** [scan_kv cs fuel] reads one key-value pair — two consecutive
    quoted strings separated by whitespace.  Returns the pair and
    remaining input, or [None] on parse failure. *)
Definition scan_kv (cs : list Z) (fuel : nat)
    : option (entity_kv * list Z) :=
  let cs1 := skip_ws cs in
  match cs1 with
  | c :: rest =>
      if c =? ascii_quote then
        match scan_quoted rest [] fuel with
        | Some (key, cs2) =>
            let cs3 := skip_ws cs2 in
            match cs3 with
            | c2 :: rest2 =>
                if c2 =? ascii_quote then
                  match scan_quoted rest2 [] fuel with
                  | Some (val, cs4) => Some ((key, val), cs4)
                  | None => None
                  end
                else None
            | [] => None
            end
        | None => None
        end
      else None
  | [] => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Scanner: read key-value pairs until closing brace               *)
(* ------------------------------------------------------------------ *)

(** [scan_kvs cs acc fuel] reads key-value pairs from [cs] until a
    closing brace [}] is found.  Returns the pairs (in order) and the
    remaining input after the brace. *)
Fixpoint scan_kvs (cs : list Z) (acc : list entity_kv) (fuel : nat)
    : option (list entity_kv * list Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let cs1 := skip_ws cs in
      match cs1 with
      | [] => None
      | c :: rest =>
          if c =? ascii_close then Some (rev acc, rest)
          else
            match scan_kv cs1 fuel' with
            | Some (kv, cs2) => scan_kvs cs2 (kv :: acc) fuel'
            | None => None
            end
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Top-level entity parser                                          *)
(* ------------------------------------------------------------------ *)

(** [scan_entities cs acc fuel] reads a sequence of brace-delimited
    entity blocks from [cs].  Returns the list of entities when the
    input is exhausted (modulo trailing whitespace/nulls). *)
Fixpoint scan_entities (cs : list Z) (acc : list bsp_entity) (fuel : nat)
    : option (list bsp_entity) :=
  match fuel with
  | O => None
  | S fuel' =>
      let cs1 := skip_ws cs in
      match cs1 with
      | [] => Some (rev acc)
      | c :: rest =>
          if c =? ascii_open then
            match scan_kvs rest [] fuel' with
            | Some (kvs, cs2) => scan_entities cs2 (kvs :: acc) fuel'
            | None => None
            end
          else None
      end
  end.

(** [parse_entities cs] parses the entity lump byte list [cs] into a
    list of entities.  The fuel parameter is set to the length of the
    input — each scanner step consumes at least one byte, so this is
    always sufficient. *)
Definition parse_entities (cs : list Z) : option (list bsp_entity) :=
  scan_entities cs [] (S (length cs)).

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** An empty input parses to an empty entity list. *)

(** Whitespace-only input parses to an empty entity list. *)

(** A null byte (common trailing byte in BSP entity lumps) parses to
    an empty entity list. *)

(** A single entity with one key-value pair. *)

(** Two entities parse correctly. *)

(** An unclosed brace returns [None]. *)

(** An unclosed quote returns [None]. *)

(* ------------------------------------------------------------------ *)
(** ** Key-value lookup                                                 *)
(* ------------------------------------------------------------------ *)

(** Equality test for [list Z] (byte-string comparison). *)
Fixpoint list_Z_eqb (xs ys : list Z) : bool :=
  match xs, ys with
  | [], []             => true
  | x :: xs', y :: ys' => (x =? y) && list_Z_eqb xs' ys'
  | _, _               => false
  end.

(** [entity_get_val e key] returns the value associated with [key] in
    entity [e], or [None] if the key is absent. *)
Fixpoint entity_get_val (e : bsp_entity) (key : list Z) : option (list Z) :=
  match e with
  | []             => None
  | (k, v) :: rest =>
      if list_Z_eqb k key then Some v
      else entity_get_val rest key
  end.

(* ------------------------------------------------------------------ *)
(** ** Named key and value constants                                    *)
(* ------------------------------------------------------------------ *)

(** ASCII encoding of the string "classname". *)
Definition key_classname : list Z :=
  [99; 108; 97; 115; 115; 110; 97; 109; 101].

(** ASCII encoding of "info_player_deathmatch". *)
Definition val_info_player_deathmatch : list Z :=
  [105; 110; 102; 111; 95; 112; 108; 97; 121; 101; 114; 95;
   100; 101; 97; 116; 104; 109; 97; 116; 99; 104].

(** ASCII encoding of "origin". *)
Definition key_origin : list Z :=
  [111; 114; 105; 103; 105; 110].

(** ASCII encoding of "angle". *)
Definition key_angle : list Z :=
  [97; 110; 103; 108; 101].

(** ASCII encoding of "model". *)
Definition key_model : list Z :=
  [109; 111; 100; 101; 108].

(** ASCII encoding of "target". *)
Definition key_target : list Z :=
  [116; 97; 114; 103; 101; 116].

(** ASCII encoding of "targetname". *)
Definition key_targetname : list Z :=
  [116; 97; 114; 103; 101; 116; 110; 97; 109; 101].

(** ASCII encoding of "trigger_push". *)
Definition val_trigger_push : list Z :=
  [116; 114; 105; 103; 103; 101; 114; 95; 112; 117; 115; 104].

(** ASCII encoding of "target_position". *)
Definition val_target_position : list Z :=
  [116; 97; 114; 103; 101; 116; 95; 112; 111; 115; 105; 116; 105; 111; 110].

(* ------------------------------------------------------------------ *)
(** ** Integer value parser                                             *)
(* ------------------------------------------------------------------ *)

Definition ascii_minus : Z := 45.   (** '-' *)
Definition ascii_space : Z := 32.   (** ' ' *)
Definition ascii_star  : Z := 42.   (** '*' *)

(** True iff [c] is an ASCII decimal digit. *)
Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

(** Scan decimal digits from [cs], accumulating the value in [acc].
    [fuel] bounds recursion; passing [length cs] is always sufficient,
    since each step consumes one byte. *)
Fixpoint scan_digits (cs : list Z) (acc : Z) (fuel : nat)
    : (Z * list Z) :=
  match fuel with
  | O      => (acc, cs)
  | S fuel' =>
      match cs with
      | c :: rest =>
          if is_digit c
          then scan_digits rest (acc * 10 + (c - 48)) fuel'
          else (acc, cs)
      | [] => (acc, [])
      end
  end.

(** Parse a signed decimal integer from the front of [cs].
    Returns [(value, remainder)] or [None] if [cs] does not begin with
    a digit or with '-' followed by a digit. *)
Definition parse_int (cs : list Z) : option (Z * list Z) :=
  match cs with
  | [] => None
  | c :: rest =>
      if c =? ascii_minus then
        match rest with
        | d :: _ =>
            if is_digit d
            then let (n, tail) := scan_digits rest 0 (length rest) in
                 Some (- n, tail)
            else None
        | [] => None
        end
      else if is_digit c
           then let (n, tail) := scan_digits cs 0 (length cs) in
                Some (n, tail)
           else None
  end.

(** Parse an inline BSP submodel reference of the form ["*N"].
    Returns [Some N] iff the string begins with ['*'], the remainder
    parses as a decimal integer, the parse consumes the full string,
    and [N] is non-negative. *)
Definition parse_inline_model_ref (cs : list Z) : option Z :=
  match cs with
  | c :: rest =>
      if c =? ascii_star then
        match parse_int rest with
        | Some (n, []) => if n <? 0 then None else Some n
        | _            => None
        end
      else None
  | [] => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas for lookup and parsing                        *)
(* ------------------------------------------------------------------ *)

(** [list_Z_eqb] is reflexive. *)

(** Matching key at the head of an entity returns that key's value. *)

(** Empty entity list has no keys. *)

(** Empty input gives [None]. *)

(** Bare minus gives [None]. *)

(** Single zero digit parses to 0. *)

(** Two-digit positive integer. *)

(** Negative integer. *)

(** A well-formed inline model reference parses successfully. *)

(** Negative inline model references are rejected. *)

(** Missing the leading ['*'] is not a valid inline model reference. *)
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

Require Import List.
Require Import ZArith.
Require Import QArith.
Require Import Lia.
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

(** Vector addition. *)
Definition vec3_add (a b : vec3) : vec3 :=
  mk_vec3
    (v3_x a + v3_x b)
    (v3_y a + v3_y b)
    (v3_z a + v3_z b).

(** Vector subtraction. *)
Definition vec3_sub (a b : vec3) : vec3 :=
  mk_vec3
    (v3_x a - v3_x b)
    (v3_y a - v3_y b)
    (v3_z a - v3_z b).

(** Scalar multiplication of a vector. *)
Definition vec3_scale (k : Q) (v : vec3) : vec3 :=
  mk_vec3
    (k * v3_x v)
    (k * v3_y v)
    (k * v3_z v).

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
  ; es_model_index  : Z       (** inline BSP submodel index *)
  ; es_origin       : vec3    (** resolved world-space target/origin *)
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

(** Minimal plane data needed for BSP brush collision. *)
Record collision_plane_input : Type := mk_collision_plane_input
  { cpi_normal_x : Q
  ; cpi_normal_y : Q
  ; cpi_normal_z : Q
  ; cpi_dist     : Q
  }.

(** Minimal texture metadata needed to decide whether a brush blocks
    the player. *)
Record collision_texture_input : Type := mk_collision_texture_input
  { cti_contents : Z }.

(** Minimal brush data needed for BSP collision. *)
Record collision_brush_input : Type := mk_collision_brush_input
  { cbi_first_side    : Z
  ; cbi_num_sides     : Z
  ; cbi_texture_index : Z
  }.

(** Minimal brush-side data needed for BSP collision. *)
Record collision_brush_side_input : Type := mk_collision_brush_side_input
  { cbsi_plane_index : Z }.

(** Minimal BSP submodel data needed for trigger volumes. *)
Record collision_model_input : Type := mk_collision_model_input
  { cmi_first_brush : Z
  ; cmi_num_brushes : Z
  }.

(** Static BSP collision data provided by the browser at world load. *)
Record collision_world_input : Type := mk_collision_world_input
  { cwi_planes      : list collision_plane_input
  ; cwi_textures    : list collision_texture_input
  ; cwi_models      : list collision_model_input
  ; cwi_brushes     : list collision_brush_input
  ; cwi_brush_sides : list collision_brush_side_input
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

Definition collision_world_empty : collision_world_input :=
  mk_collision_world_input [] [] [] [] [].

Definition contents_solid : Z := 1.

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

(** The initial game state has tick count 0. *)

(** The initial game state is grounded. *)

(** The zero input snapshot has zero delta time. *)

(** The zero input snapshot has no keys pressed. *)

(** Entity count is preserved through snapshot extraction. *)

(** The camera position in the snapshot matches the game state. *)

(** The camera yaw in the snapshot matches the game state. *)

(** The camera pitch in the snapshot matches the game state. *)

(** Camera-word serialization always yields five rational pairs. *)



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

(** True iff entity [e] has the given classname. *)
Definition entity_classname_eqb (e : bsp_entity) (classname : list Z) : bool :=
  match entity_get_val e key_classname with
  | Some v => list_Z_eqb v classname
  | None   => false
  end.

(** True iff entity [e] has classname [info_player_deathmatch]. *)
Definition is_spawn_entity (e : bsp_entity) : bool :=
  entity_classname_eqb e val_info_player_deathmatch.

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

(* ------------------------------------------------------------------ *)
(** ** Trigger metadata extraction from entity data                     *)
(* ------------------------------------------------------------------ *)

Record trigger_push_metadata : Type := mk_trigger_push_metadata
  { tpm_model_index : Z
  ; tpm_target_name : list Z
  }.

Record target_position_metadata : Type := mk_target_position_metadata
  { tpos_target_name : list Z
  ; tpos_origin      : vec3
  }.

Definition target_position_name_eqb
    (target : target_position_metadata) (name : list Z) : bool :=
  list_Z_eqb (tpos_target_name target) name.

(** True iff entity [e] has classname [trigger_push]. *)
Definition is_trigger_push_entity (e : bsp_entity) : bool :=
  entity_classname_eqb e val_trigger_push.

(** True iff entity [e] has classname [target_position]. *)
Definition is_target_position_entity (e : bsp_entity) : bool :=
  entity_classname_eqb e val_target_position.

(** Extract the inline BSP submodel index from an entity's [model] key. *)
Definition entity_model_index (e : bsp_entity) : option Z :=
  match entity_get_val e key_model with
  | Some v => parse_inline_model_ref v
  | None   => None
  end.

(** Extract the target name an entity points at via its [target] key. *)
Definition entity_target_name (e : bsp_entity) : option (list Z) :=
  entity_get_val e key_target.

(** Extract the name by which another entity can target this one. *)
Definition entity_targetname (e : bsp_entity) : option (list Z) :=
  entity_get_val e key_targetname.

(** Extract a [target_position] origin from entity data. *)
Definition target_position_origin_of_entity (e : bsp_entity) : option vec3 :=
  match entity_get_val e key_origin with
  | Some v => parse_origin_vec3 v
  | None   => None
  end.

(** Parse the metadata v1 needs from a [trigger_push] entity.
    The trigger must carry both an inline [model] reference and a
    [target] name so later world-building code can resolve it. *)
Definition parse_trigger_push_metadata (e : bsp_entity)
    : option trigger_push_metadata :=
  if is_trigger_push_entity e then
    match entity_model_index e, entity_target_name e with
    | Some model_index, Some target_name =>
        Some (mk_trigger_push_metadata model_index target_name)
    | _, _ => None
    end
  else None.

(** Parse the metadata v1 needs from a [target_position] entity. *)
Definition parse_target_position_metadata (e : bsp_entity)
    : option target_position_metadata :=
  if is_target_position_entity e then
    match entity_targetname e, target_position_origin_of_entity e with
    | Some target_name, Some origin =>
        Some (mk_target_position_metadata target_name origin)
    | _, _ => None
    end
  else None.

Fixpoint collect_target_positions
    (entities : list bsp_entity) : list target_position_metadata :=
  match entities with
  | [] => []
  | e :: rest =>
      match parse_target_position_metadata e with
      | Some target => target :: collect_target_positions rest
      | None        => collect_target_positions rest
      end
  end.

Fixpoint find_target_position_origin
    (targets : list target_position_metadata) (name : list Z) : option vec3 :=
  match targets with
  | [] => None
  | target :: rest =>
      if target_position_name_eqb target name
      then Some (tpos_origin target)
      else find_target_position_origin rest name
  end.

Fixpoint initial_trigger_states_from_entities_aux
    (entities : list bsp_entity)
    (targets : list target_position_metadata)
    (entity_index : Z) : list entity_state :=
  match entities with
  | [] => []
  | e :: rest =>
      let rest_states :=
        initial_trigger_states_from_entities_aux rest targets (entity_index + 1) in
      match parse_trigger_push_metadata e with
      | Some trigger =>
          match find_target_position_origin targets (tpm_target_name trigger) with
          | Some origin =>
              mk_entity_state
                entity_index
                (tpm_model_index trigger)
                origin
                true :: rest_states
          | None => rest_states
          end
      | None => rest_states
      end
  end.

(** Resolve the initial trigger/jump-pad state directly from the BSP
    entity list by pairing [trigger_push] entities with the
    [target_position] entities they reference. *)
Definition initial_trigger_states_from_entities
    (entities : list bsp_entity) : list entity_state :=
  initial_trigger_states_from_entities_aux
    entities
    (collect_target_positions entities)
    0.

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
  let trigger_states := initial_trigger_states_from_entities entities in
  match select_spawn_point entities with
  | Some (pos, yaw) => mk_game_state pos vec3_zero yaw 0 true trigger_states 0
  | None            => mk_game_state vec3_zero vec3_zero 0 0 true trigger_states 0
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
(** ** BSP collision helpers                                            *)
(* ------------------------------------------------------------------ *)

Definition qleb (a b : Q) : bool :=
  if Qlt_le_dec b a then false else true.

Definition vec3_dot (a b : vec3) : Q :=
  (v3_x a * v3_x b + v3_y a * v3_y b + v3_z a * v3_z b)%Q.

Definition vec3_midpoint (a b : vec3) : vec3 :=
  mk_vec3
    ((v3_x a + v3_x b) / 2)%Q
    ((v3_y a + v3_y b) / 2)%Q
    ((v3_z a + v3_z b) / 2)%Q.

Definition plane_normal (pl : collision_plane_input) : vec3 :=
  mk_vec3 (cpi_normal_x pl) (cpi_normal_y pl) (cpi_normal_z pl).

Definition brush_blocks_playerb
    (textures : list collision_texture_input) (br : collision_brush_input) : bool :=
  match nth_z textures (cbi_texture_index br) with
  | Some tx =>
      bit_setb (cti_contents tx) contents_solid ||
      bit_setb (cti_contents tx) contents_playerclip
  | None => false
  end.

Definition plane_signed_distance
    (pl : collision_plane_input) (pos : vec3) : Q :=
  (vec3_dot (plane_normal pl) pos - cpi_dist pl)%Q.

Definition player_radius : Q := 16.
Definition ground_probe_distance : Q := 1.
Definition gravity_accel : Q := 800.
Definition jump_speed : Q := 270.
Definition trigger_push_travel_time : Q := 1.
Definition collision_sweep_iterations : nat := 8%nat.
Definition collision_motion_substeps : nat := 16%nat.
Definition collision_motion_substep_scale : Q := (1 # 16)%Q.

Fixpoint point_collides_brush_aux
    (planes : list collision_plane_input)
    (brush_sides : list collision_brush_side_input)
    (pos : vec3)
    (side_index : Z)
    (fuel : nat) : bool :=
  match fuel with
  | O => true
  | S fuel' =>
      match nth_z brush_sides side_index with
      | None => false
      | Some side =>
          match nth_z planes (cbsi_plane_index side) with
          | None => false
          | Some plane =>
              if qleb (plane_signed_distance plane pos) player_radius
              then point_collides_brush_aux planes brush_sides pos (side_index + 1) fuel'
              else false
          end
      end
  end.

Definition point_collides_brushb
    (world : collision_world_input) (pos : vec3) (br : collision_brush_input) : bool :=
  if brush_blocks_playerb (cwi_textures world) br then
    match Z.max 0 (cbi_num_sides br) with
    | 0 => false
    | n =>
        point_collides_brush_aux
          (cwi_planes world)
          (cwi_brush_sides world)
          pos
          (cbi_first_side br)
          (Z.to_nat n)
    end
  else false.

Definition point_collides_brush_geometryb
    (world : collision_world_input) (pos : vec3) (br : collision_brush_input) : bool :=
  match Z.max 0 (cbi_num_sides br) with
  | 0 => false
  | n =>
      point_collides_brush_aux
        (cwi_planes world)
        (cwi_brush_sides world)
        pos
        (cbi_first_side br)
        (Z.to_nat n)
  end.

Fixpoint point_collides_world_aux
    (world : collision_world_input) (pos : vec3)
    (brushes : list collision_brush_input) : bool :=
  match brushes with
  | [] => false
  | br :: rest =>
      if point_collides_brushb world pos br then true
      else point_collides_world_aux world pos rest
  end.

Definition point_collides_worldb
    (world : collision_world_input) (pos : vec3) : bool :=
  point_collides_world_aux world pos (cwi_brushes world).

Fixpoint point_collides_model_brushes_aux
    (world : collision_world_input) (pos : vec3)
    (brush_index : Z) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
      match nth_z (cwi_brushes world) brush_index with
      | None => false
      | Some br =>
          if point_collides_brush_geometryb world pos br
          then true
          else point_collides_model_brushes_aux world pos (brush_index + 1) fuel'
      end
  end.

Definition point_collides_modelb
    (world : collision_world_input) (pos : vec3) (model : collision_model_input) : bool :=
  match Z.max 0 (cmi_num_brushes model) with
  | 0 => false
  | n =>
      point_collides_model_brushes_aux
        world pos (cmi_first_brush model) (Z.to_nat n)
  end.

Definition entity_inside_trigger_modelb
    (world : collision_world_input) (pos : vec3) (es : entity_state) : bool :=
  match nth_z (cwi_models world) (es_model_index es) with
  | Some model => point_collides_modelb world pos model
  | None => false
  end.

Definition trigger_push_velocity
    (pos target_origin : vec3) : vec3 :=
  let delta := vec3_sub target_origin pos in
  let t := trigger_push_travel_time in
  mk_vec3
    (v3_x delta / t)
    (v3_y delta / t)
    ((v3_z delta / t) + gravity_accel * t / 2)%Q.

Fixpoint apply_trigger_pushes
    (world : collision_world_input) (pos : vec3)
    (entities : list entity_state)
    : option vec3 * list entity_state :=
  match entities with
  | [] => (None, [])
  | es :: rest =>
      let inside := entity_inside_trigger_modelb world pos es in
      let fired := es_active es && inside in
      let updated :=
        mk_entity_state
          (es_entity_index es)
          (es_model_index es)
          (es_origin es)
          (negb inside) in
      let '(rest_impulse, rest_entities) := apply_trigger_pushes world pos rest in
      let impulse :=
        if fired
        then Some (trigger_push_velocity pos (es_origin es))
        else rest_impulse in
      (impulse, updated :: rest_entities)
  end.

Fixpoint sweep_to_contact
    (world : collision_world_input) (lo hi : vec3) (fuel : nat) : vec3 :=
  match fuel with
  | O => lo
  | S fuel' =>
      let mid := vec3_midpoint lo hi in
      if point_collides_worldb world mid
      then sweep_to_contact world lo mid fuel'
      else sweep_to_contact world mid hi fuel'
  end.

Definition resolve_motion
    (world : collision_world_input) (start delta : vec3) : vec3 * bool :=
  let target := vec3_add start delta in
  if point_collides_worldb world start then (start, true) else
  if point_collides_worldb world target
  then (sweep_to_contact world start target collision_sweep_iterations, true)
  else (target, false).

Fixpoint resolve_motion_substeps_aux
    (world : collision_world_input) (pos step_delta : vec3) (fuel : nat)
    : vec3 * bool :=
  match fuel with
  | O => (pos, false)
  | S fuel' =>
      let '(next_pos, blocked_now) := resolve_motion world pos step_delta in
      if blocked_now then (next_pos, true)
      else resolve_motion_substeps_aux world next_pos step_delta fuel'
  end.

Definition resolve_motion_substeps
    (world : collision_world_input) (start delta : vec3) : vec3 * bool :=
  resolve_motion_substeps_aux
    world
    start
    (vec3_scale collision_motion_substep_scale delta)
    collision_motion_substeps.

Definition grounded_by_worldb
    (world : collision_world_input) (pos : vec3) : bool :=
  point_collides_worldb world
    (mk_vec3 (v3_x pos) (v3_y pos) (v3_z pos - ground_probe_distance)).

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas for spawn-point selection                     *)
(* ------------------------------------------------------------------ *)

(** Parsing the canonical "0 0 24" spawn height produces the correct
    vec3. *)

(** Negative origin components are handled correctly. *)






(** An empty entity list has no spawn points. *)

(** Falling back on an empty entity list gives [game_state_init]. *)

(** A spawn-derived state has tick count 0. *)

(** A spawn-derived state has zero velocity. *)

(** A spawn-derived state starts grounded. *)


(** When a spawn point is found, the initial position comes from it. *)

(** When a spawn point is found, the initial yaw comes from it. *)

(** The bridge helper always yields the five serialized camera values. *)








(* ------------------------------------------------------------------ *)
(** ** World-state serialization and frame stepping                    *)
(* ------------------------------------------------------------------ *)

(** Number of [Z] words produced per serialized [entity_state]. *)
Definition entity_state_words_count : nat := 9.

(** Number of [Z] words produced by [game_state_to_words] for a
    game state with an empty entity list. *)
Definition game_state_words_count : nat := 19.

Definition entity_state_to_words (es : entity_state) : list Z :=
  [es_entity_index es; es_model_index es] ++
  q_words (v3_x (es_origin es)) ++
  q_words (v3_y (es_origin es)) ++
  q_words (v3_z (es_origin es)) ++
  [if es_active es then 1 else 0].

Fixpoint entity_states_to_words (entities : list entity_state) : list Z :=
  match entities with
  | [] => []
  | es :: rest => entity_state_to_words es ++ entity_states_to_words rest
  end.

(** Serialize a [game_state] to a flat [list Z] suitable for
    round-tripping through the JS bridge.

    Word layout (19 + 9 * entity_count entries):
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
      18 entity_count
      19... serialized entity states
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
  [gs_tick gs] ++
  [Z.of_nat (length (gs_entities gs))] ++
  entity_states_to_words (gs_entities gs).

Definition entity_state_from_words (ws : list Z)
    : option (entity_state * list Z) :=
  match ws with
  | [entity_index; model_index;
     ox_n; ox_d; oy_n; oy_d; oz_n; oz_d;
     active] =>
      if (ox_d <=? 0) || (oy_d <=? 0) || (oz_d <=? 0)
      then None
      else
        Some
          ( mk_entity_state
              entity_index
              model_index
              (mk_vec3 (Qmake ox_n (Z.to_pos ox_d))
                       (Qmake oy_n (Z.to_pos oy_d))
                       (Qmake oz_n (Z.to_pos oz_d)))
              (negb (active =? 0))
          , []
          )
  | entity_index :: model_index ::
    ox_n :: ox_d :: oy_n :: oy_d :: oz_n :: oz_d :: active :: rest =>
      if (ox_d <=? 0) || (oy_d <=? 0) || (oz_d <=? 0)
      then None
      else
        Some
          ( mk_entity_state
              entity_index
              model_index
              (mk_vec3 (Qmake ox_n (Z.to_pos ox_d))
                       (Qmake oy_n (Z.to_pos oy_d))
                       (Qmake oz_n (Z.to_pos oz_d)))
              (negb (active =? 0))
          , rest
          )
  | _ => None
  end.

Fixpoint entity_states_from_words_aux (count : nat) (ws : list Z)
    : option (list entity_state * list Z) :=
  match count with
  | O => Some ([], ws)
  | S count' =>
      match entity_state_from_words ws with
      | Some (es, rest) =>
          match entity_states_from_words_aux count' rest with
          | Some (entities, tail) => Some (es :: entities, tail)
          | None => None
          end
      | None => None
      end
  end.

(** Reconstruct a [game_state] from the word list produced by
    [game_state_to_words].  Returns [None] on a malformed list or
    any zero/negative denominator. *)
Definition game_state_from_words (ws : list Z) : option game_state :=
  match ws with
  | px_n :: px_d :: py_n :: py_d :: pz_n :: pz_d ::
    vx_n :: vx_d :: vy_n :: vy_d :: vz_n :: vz_d ::
    yaw_n :: yaw_d :: pitch_n :: pitch_d ::
    on_ground :: tick :: entity_count :: entity_words =>
      if (px_d <=? 0) || (py_d <=? 0) || (pz_d <=? 0) ||
          (vx_d <=? 0) || (vy_d <=? 0) || (vz_d <=? 0) ||
          (yaw_d <=? 0) || (pitch_d <=? 0) || (entity_count <? 0)
      then None
      else
        match entity_states_from_words_aux (Z.to_nat entity_count) entity_words with
        | Some (entities, []) =>
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
              entities
              tick)
        | _ => None
        end
  | _ => None
  end.

(** Movement/look constants for free movement stepping. *)
Definition yaw_full_turn : Q := 360.
Definition pitch_limit : Q := 89.
Definition move_speed : Q := 320.
Definition pi_approx : Q := (355 # 113)%Q.

(** Convert elapsed milliseconds to seconds as a rational. *)
Definition millis_to_seconds (dt_ms : Z) : Q :=
  (inject_Z dt_ms * (1 # 1000))%Q.

(** Wrap a degree angle into the half-open interval [0, 360). *)
Definition normalize_degrees_360 (angle : Q) : Q :=
  Qmake
    (Z.modulo (Qnum angle) (360 * Z.pos (Qden angle)))
    (Qden angle).

(** Clamp pitch so the camera never flips upside-down. *)
Definition clamp_pitch (pitch : Q) : Q :=
  if Qlt_le_dec pitch (- pitch_limit) then - pitch_limit else
  if Qlt_le_dec pitch_limit pitch then pitch_limit else
  pitch.

Definition bool_to_Z (b : bool) : Z :=
  if b then 1 else 0.

Definition input_axis (positive negative : bool) : Z :=
  bool_to_Z positive - bool_to_Z negative.

(** Bhaskara I's sine approximation gives smooth rational movement
    directions without requiring transcendental functions in Rocq. *)
Definition bhaskara_sine_0_180 (deg : Q) : Q :=
  let x := (deg * pi_approx / 180)%Q in
  let prod := (x * (pi_approx - x))%Q in
  ((16 * prod) / (5 * pi_approx * pi_approx - 4 * prod))%Q.

Definition approx_sin_degrees (angle : Q) : Q :=
  let wrapped := normalize_degrees_360 angle in
  if Qlt_le_dec wrapped 180
  then bhaskara_sine_0_180 wrapped
  else (- bhaskara_sine_0_180 (wrapped - 180))%Q.

Definition approx_cos_degrees (angle : Q) : Q :=
  approx_sin_degrees (angle + 90)%Q.

Definition step_yaw (yaw yaw_delta : Q) : Q :=
  normalize_degrees_360 (yaw + yaw_delta)%Q.

Definition step_pitch (pitch pitch_delta : Q) : Q :=
  clamp_pitch (pitch + pitch_delta)%Q.

Definition movement_velocity (yaw vel_z : Q) (input : input_snapshot) : vec3 :=
  let forward_axis := inject_Z (input_axis (is_forward input) (is_back input)) in
  let strafe_axis := inject_Z (input_axis (is_right input) (is_left input)) in
  let cos_yaw := approx_cos_degrees yaw in
  let sin_yaw := approx_sin_degrees yaw in
  mk_vec3
    (move_speed * (forward_axis * cos_yaw - strafe_axis * sin_yaw))%Q
    (move_speed * (forward_axis * sin_yaw + strafe_axis * cos_yaw))%Q
    vel_z.

Definition advance_position (pos velocity : vec3) (dt_ms : Z) : vec3 :=
  vec3_add pos (vec3_scale (millis_to_seconds dt_ms) velocity).

(** Advance the world by one frame: apply look deltas, derive planar
    movement from the updated yaw, and integrate position using the
    per-tick delta time. *)
Definition step_world (gs : game_state) (input : input_snapshot)
    : game_state :=
  let yaw := step_yaw (gs_yaw gs) (is_yaw_delta input) in
  let pitch := step_pitch (gs_pitch gs) (is_pitch_delta input) in
  let velocity := movement_velocity yaw (v3_z (gs_velocity gs)) input in
  let position := advance_position (gs_position gs) velocity (is_dt_ms input) in
  mk_game_state
    position
    velocity
    yaw
    pitch
    (gs_on_ground gs)
    (gs_entities gs)
    (gs_tick gs + 1).

Definition step_world_in_world
    (world : collision_world_input) (gs : game_state) (input : input_snapshot)
    : game_state :=
  let yaw := step_yaw (gs_yaw gs) (is_yaw_delta input) in
  let pitch := step_pitch (gs_pitch gs) (is_pitch_delta input) in
  let dt_s := millis_to_seconds (is_dt_ms input) in
  let grounded_start :=
    gs_on_ground gs || grounded_by_worldb world (gs_position gs) in
  let prior_vel_z := if grounded_start then 0%Q else v3_z (gs_velocity gs) in
  let desired_vel_z :=
    if grounded_start && is_jump input
    then jump_speed
    else (prior_vel_z - gravity_accel * dt_s)%Q in
  let desired_planar := movement_velocity yaw 0%Q input in
  let horizontal_delta :=
    vec3_scale dt_s (mk_vec3 (v3_x desired_planar) (v3_y desired_planar) 0) in
  let '(horizontal_pos, horizontal_blocked) :=
    resolve_motion_substeps world (gs_position gs) horizontal_delta in
  let vertical_delta := mk_vec3 0 0 (dt_s * desired_vel_z)%Q in
  let '(position, vertical_blocked) :=
    resolve_motion_substeps world horizontal_pos vertical_delta in
  let landed := vertical_blocked && qleb desired_vel_z 0 in
  let base_on_ground := landed || grounded_by_worldb world position in
  let base_velocity :=
    mk_vec3
      (if horizontal_blocked then 0 else v3_x desired_planar)
      (if horizontal_blocked then 0 else v3_y desired_planar)
      (if vertical_blocked then 0 else desired_vel_z) in
  let '(trigger_impulse, entities) :=
    apply_trigger_pushes world position (gs_entities gs) in
  let velocity :=
    match trigger_impulse with
    | Some impulse => impulse
    | None => base_velocity
    end in
  let on_ground :=
    match trigger_impulse with
    | Some _ => false
    | None => base_on_ground
    end in
  mk_game_state
    position
    velocity
    yaw
    pitch
    on_ground
    entities
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

Definition step_world_words_in_world
    (world : collision_world_input)
    (ws : list Z) (input : input_snapshot) : list Z :=
  match game_state_from_words ws with
  | None    => ws
  | Some gs => game_state_to_words (step_world_in_world world gs input)
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




(** Stepping integrates position from the per-frame velocity. *)

(** Stepping derives movement velocity from the updated yaw. *)

(** Stepping applies look input to orientation. *)




(** Stepping increments the tick counter. *)









(** Helper: [Z.pos p] is never [<=? 0]. *)

(** [entity_state_to_words] round-trips through [entity_state_from_words]
    with any trailing payload preserved. *)


(** [game_state_to_words] round-trips through [game_state_from_words]. *)

(** Serialized word count includes the per-entity payload. *)


Definition sample_solid_texture : collision_texture_input :=
  mk_collision_texture_input contents_solid.

Definition sample_floor_world : collision_world_input :=
  mk_collision_world_input
    [ mk_collision_plane_input   1    0    0 1024
    ; mk_collision_plane_input (-1)   0    0 1024
    ; mk_collision_plane_input   0    1    0 1024
    ; mk_collision_plane_input   0  (-1)   0 1024
     ; mk_collision_plane_input   0    0    1    0
     ; mk_collision_plane_input   0    0  (-1)  64
     ]
    [sample_solid_texture]
    []
    [mk_collision_brush_input 0 6 0]
    [ mk_collision_brush_side_input 0
    ; mk_collision_brush_side_input 1
    ; mk_collision_brush_side_input 2
    ; mk_collision_brush_side_input 3
    ; mk_collision_brush_side_input 4
    ; mk_collision_brush_side_input 5
    ].

Definition sample_wall_world : collision_world_input :=
  mk_collision_world_input
    [ mk_collision_plane_input   1    0    0   96
    ; mk_collision_plane_input (-1)   0    0  (-32)
    ; mk_collision_plane_input   0    1    0 1024
    ; mk_collision_plane_input   0  (-1)   0 1024
     ; mk_collision_plane_input   0    0    1 1024
     ; mk_collision_plane_input   0    0  (-1) 1024
     ]
    [sample_solid_texture]
    []
    [mk_collision_brush_input 0 6 0]
    [ mk_collision_brush_side_input 0
    ; mk_collision_brush_side_input 1
    ; mk_collision_brush_side_input 2
    ; mk_collision_brush_side_input 3
    ; mk_collision_brush_side_input 4
    ; mk_collision_brush_side_input 5
    ].

Definition sample_trigger_world : collision_world_input :=
  mk_collision_world_input
    [ mk_collision_plane_input   1    0    0   32
    ; mk_collision_plane_input (-1)   0    0   32
    ; mk_collision_plane_input   0    1    0   32
    ; mk_collision_plane_input   0  (-1)   0   32
    ; mk_collision_plane_input   0    0    1    0
    ; mk_collision_plane_input   0    0  (-1)  64
    ]
    []
    [mk_collision_model_input 0 1]
    [mk_collision_brush_input 0 6 0]
    [ mk_collision_brush_side_input 0
    ; mk_collision_brush_side_input 1
    ; mk_collision_brush_side_input 2
    ; mk_collision_brush_side_input 3
    ; mk_collision_brush_side_input 4
    ; mk_collision_brush_side_input 5
    ].











