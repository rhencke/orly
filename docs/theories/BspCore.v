(** * Binary parsing primitives for the Q3 BSP loader.

    Little-endian integer and IEEE 754 single-precision float readers
    over a flat byte sequence.  All functions return [option] so callers
    can propagate parse failures without exceptions.

    These primitives are the only code that touches raw bytes; all lump
    parsers call these and never index into [bytes] directly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
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
Lemma get_u8_singleton : forall b,
  get_u8 [b] 0 = Some b.
Proof. reflexivity. Qed.

(** Two zero bytes decode as signed 0. *)
Lemma get_i16_le_zero :
  get_i16_le [0; 0] 0 = Some 0.
Proof. reflexivity. Qed.

(** All-ones bytes are [−1] in 16-bit two's complement. *)
Lemma get_i16_le_minus_one :
  get_i16_le [255; 255] 0 = Some (-1).
Proof. reflexivity. Qed.

(** Four zero bytes decode as [0]. *)
Lemma get_i32_le_zero :
  get_i32_le [0; 0; 0; 0] 0 = Some 0.
Proof. reflexivity. Qed.

(** Little-endian byte order: the first byte is least significant. *)
Lemma get_i32_le_one :
  get_i32_le [1; 0; 0; 0] 0 = Some 1.
Proof. reflexivity. Qed.

(** All-ones bytes are [−1] in two's complement. *)
Lemma get_i32_le_minus_one :
  get_i32_le [255; 255; 255; 255] 0 = Some (-1).
Proof. reflexivity. Qed.

(** [0x3F800000] is the IEEE 754 binary32 encoding of [1.0]. *)
Lemma decode_f32_one :
  (decode_f32_bits 0x3F800000 == 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(** [0x00000000] encodes [0.0]. *)
Lemma decode_f32_zero :
  (decode_f32_bits 0 == 0)%Q.
Proof. vm_compute. reflexivity. Qed.

(** [0xBF800000] encodes [−1.0]. *)
Lemma decode_f32_neg_one :
  (decode_f32_bits 0xBF800000 == -1)%Q.
Proof. vm_compute. reflexivity. Qed.
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

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
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
Lemma parse_entities_empty :
  parse_entities [] = Some [].
Proof. reflexivity. Qed.

(** Whitespace-only input parses to an empty entity list. *)
Lemma parse_entities_whitespace :
  parse_entities [32; 10; 13; 9] = Some [].
Proof. reflexivity. Qed.

(** A null byte (common trailing byte in BSP entity lumps) parses to
    an empty entity list. *)
Lemma parse_entities_null :
  parse_entities [0] = Some [].
Proof. reflexivity. Qed.

(** A single entity with one key-value pair. *)
Lemma parse_entities_single :
  parse_entities
    [123; 10;                        (* { \n *)
     34; 107; 34; 32; 34; 118; 34;  (* "k" "v" *)
     10; 125; 10]                    (* \n } \n *)
  = Some [[(  [107], [118]  )]].
Proof. vm_compute. reflexivity. Qed.

(** Two entities parse correctly. *)
Lemma parse_entities_two :
  parse_entities
    [123; 10; 34; 97; 34; 32; 34; 98; 34; 10; 125; 10;   (* { "a" "b" } *)
     123; 10; 34; 99; 34; 32; 34; 100; 34; 10; 125; 10]  (* { "c" "d" } *)
  = Some [  [([97], [98])]  ;  [([99], [100])]  ].
Proof. vm_compute. reflexivity. Qed.

(** An unclosed brace returns [None]. *)
Lemma parse_entities_unclosed :
  parse_entities [123; 10] = None.
Proof. vm_compute. reflexivity. Qed.

(** An unclosed quote returns [None]. *)
Lemma parse_entities_unclosed_quote :
  parse_entities [123; 10; 34; 97; 10; 125] = None.
Proof. vm_compute. reflexivity. Qed.

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

(* ------------------------------------------------------------------ *)
(** ** Integer value parser                                             *)
(* ------------------------------------------------------------------ *)

Definition ascii_minus : Z := 45.   (** '-' *)
Definition ascii_space : Z := 32.   (** ' ' *)

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

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas for lookup and parsing                        *)
(* ------------------------------------------------------------------ *)

(** [list_Z_eqb] is reflexive. *)
Lemma list_Z_eqb_refl : forall xs, list_Z_eqb xs xs = true.
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - rewrite Z.eqb_refl. simpl. exact IH.
Qed.

(** Matching key at the head of an entity returns that key's value. *)
Lemma entity_get_val_head : forall k v rest,
  entity_get_val ((k, v) :: rest) k = Some v.
Proof.
  intros k v rest. simpl. rewrite list_Z_eqb_refl. reflexivity.
Qed.

(** Empty entity list has no keys. *)
Lemma entity_get_val_nil : forall key,
  entity_get_val [] key = None.
Proof. reflexivity. Qed.

(** Empty input gives [None]. *)
Lemma parse_int_none_empty : parse_int [] = None.
Proof. reflexivity. Qed.

(** Bare minus gives [None]. *)
Lemma parse_int_none_minus_only : parse_int [45] = None.
Proof. vm_compute. reflexivity. Qed.

(** Single zero digit parses to 0. *)
Lemma parse_int_zero : parse_int [48] = Some (0, []).
Proof. vm_compute. reflexivity. Qed.

(** Two-digit positive integer. *)
Lemma parse_int_pos_42 : parse_int [52; 50] = Some (42, []).
Proof. vm_compute. reflexivity. Qed.

(** Negative integer. *)
Lemma parse_int_neg_1 : parse_int [45; 49] = Some (-1, []).
Proof. vm_compute. reflexivity. Qed.
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
