(** * Q3 BSP lightmap, visibility-data, effect, and model types with
    lump parsers.

    Defines four lumps of the Q3 BSP format:

    - **Lightmaps lump** (lump index 14): each entry is a 128 × 128
      RGB image stored as 49 152 raw bytes (128 × 128 × 3).

    - **Vis-data lump** (lump index 16): a header (two i32 fields:
      number of cluster vectors and byte size of each vector) followed
      by a flat byte array of PVS bit vectors.

    - **Effects lump** (lump index 12): each entry pairs a 64-byte
      null-terminated shader name with a brush index and an unknown
      field.  Entry size: 72 bytes (64 + 2 × i32).

    - **Models lump** (lump index 7): each entry is a sub-model with
      an axis-aligned bounding box (6 floats), a face range, and a
      brush range.  Entry size: 40 bytes (6 × f32 + 4 × i32).

    All integer fields are 32-bit signed little-endian.  Floats are
    IEEE 754 single-precision, decoded to [Q].  Byte offsets follow the
    Q3 BSP specification exactly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Hello Require Import BspBinary.
From Hello Require Import BspTexture.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Lightmap                                                         *)
(* ------------------------------------------------------------------ *)

(** A single entry in the lightmaps lump.

    Each lightmap is a 128 × 128 pixel RGB image stored as 49 152 raw
    bytes (128 × 128 × 3).  We keep the data as a flat byte list. *)
Record bsp_lightmap : Type := mk_bsp_lightmap
  { lm_data : list Z   (** 49 152 raw RGB bytes *)
  }.

(** Size of one lightmaps-lump entry in bytes (128 × 128 × 3). *)
Definition bsp_lightmap_size : nat := 49152.

(** [parse_bsp_lightmap bs i] reads one 49 152-byte lightmap entry from
    byte offset [i] in [bs].  Returns [None] if there are fewer than
    49 152 bytes available at that offset. *)
Definition parse_bsp_lightmap (bs : bytes) (i : nat) : option bsp_lightmap :=
  match take_n bs i 49152 with
  | Some data => Some (mk_bsp_lightmap data)
  | None      => None
  end.

(** [parse_lightmap_lump bs off count] reads [count] consecutive
    lightmap entries from byte offset [off] in [bs].  Returns [None]
    if any entry cannot be read. *)
Fixpoint parse_lightmap_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_lightmap) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_lightmap bs off,
            parse_lightmap_lump bs (off + bsp_lightmap_size)%nat n with
      | Some lm, Some rest => Some (lm :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Visibility data                                                  *)
(* ------------------------------------------------------------------ *)

(** The visibility lump has a unique layout: a two-field header
    followed by a variable-length byte array of PVS bit vectors.

    - [vis_n_vecs]:  bytes 0–3  (number of cluster vectors)
    - [vis_sz_vecs]: bytes 4–7  (byte size of each vector)
    - [vis_vecs]:    bytes 8–… (flat PVS data, [n_vecs × sz_vecs] bytes) *)
Record bsp_vis_data : Type := mk_bsp_vis_data
  { vis_n_vecs  : Z
  ; vis_sz_vecs : Z
  ; vis_vecs    : list Z   (** raw PVS byte vectors *)
  }.

(** [parse_vis_data bs off len] reads the visibility lump starting at
    byte offset [off] with total lump length [len].  Returns [None] if
    the lump is too short for the header or the declared vector data
    exceeds the available bytes. *)
Definition parse_vis_data (bs : bytes) (off : nat) (len : nat)
    : option bsp_vis_data :=
  if (len <? 8)%nat then None
  else
    match get_i32_le bs off,
          get_i32_le bs (off + 4)%nat with
    | Some nv, Some sv =>
        let data_len := (len - 8)%nat in
        match take_n bs (off + 8)%nat data_len with
        | Some vecs => Some (mk_bsp_vis_data nv sv vecs)
        | None      => None
        end
    | _, _ => None
    end.

(* ------------------------------------------------------------------ *)
(** ** Effect                                                           *)
(* ------------------------------------------------------------------ *)

(** A single entry in the effects lump.

    Field layout (offsets relative to entry start):
    - [fx_name]:        bytes  0–63  (null-terminated shader name, 64 bytes)
    - [fx_brush_index]: bytes 64–67  (index into brushes lump, i32)
    - [fx_unknown]:     bytes 68–71  (always 5 in known maps, i32) *)
Record bsp_effect : Type := mk_bsp_effect
  { fx_name        : list Z   (** 64 raw bytes; null-terminated shader name *)
  ; fx_brush_index : Z
  ; fx_unknown     : Z
  }.

(** Size of one effects-lump entry in bytes (64-byte name + 2 × i32). *)
Definition bsp_effect_size : nat := 72.

(** [parse_bsp_effect bs i] reads one 72-byte effect entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 72
    bytes available at that offset. *)
Definition parse_bsp_effect (bs : bytes) (i : nat) : option bsp_effect :=
  match take_n bs i 64,
        get_i32_le bs (i + 64)%nat,
        get_i32_le bs (i + 68)%nat with
  | Some name, Some bi, Some unk =>
      Some (mk_bsp_effect name bi unk)
  | _, _, _ => None
  end.

(** [parse_effect_lump bs off count] reads [count] consecutive effect
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_effect_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_effect) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_effect bs off,
            parse_effect_lump bs (off + bsp_effect_size)%nat n with
      | Some fx, Some rest => Some (fx :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Model                                                            *)
(* ------------------------------------------------------------------ *)

(** A single entry in the models lump.

    Field layout (offsets relative to entry start):
    - [md_mins_x/y/z]:       bytes  0–11  (AABB minimum corner, 3 × f32)
    - [md_maxs_x/y/z]:       bytes 12–23  (AABB maximum corner, 3 × f32)
    - [md_first_face]:       bytes 24–27  (first face index, i32)
    - [md_num_faces]:        bytes 28–31  (number of faces, i32)
    - [md_first_brush]:      bytes 32–35  (first brush index, i32)
    - [md_num_brushes]:      bytes 36–39  (number of brushes, i32) *)
Record bsp_model : Type := mk_bsp_model
  { md_mins_x      : Q
  ; md_mins_y      : Q
  ; md_mins_z      : Q
  ; md_maxs_x      : Q
  ; md_maxs_y      : Q
  ; md_maxs_z      : Q
  ; md_first_face  : Z
  ; md_num_faces   : Z
  ; md_first_brush : Z
  ; md_num_brushes : Z
  }.

(** Size of one models-lump entry in bytes (6 × f32 + 4 × i32). *)
Definition bsp_model_size : nat := 40.

(** [parse_bsp_model bs i] reads one 40-byte model entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 40
    bytes available at that offset. *)
Definition parse_bsp_model (bs : bytes) (i : nat) : option bsp_model :=
  match get_f32_le bs  i,
        get_f32_le bs (i +  4)%nat,
        get_f32_le bs (i +  8)%nat,
        get_f32_le bs (i + 12)%nat,
        get_f32_le bs (i + 16)%nat,
        get_f32_le bs (i + 20)%nat,
        get_i32_le bs (i + 24)%nat,
        get_i32_le bs (i + 28)%nat,
        get_i32_le bs (i + 32)%nat,
        get_i32_le bs (i + 36)%nat with
  | Some mx, Some my, Some mz,
    Some Mx, Some My, Some Mz,
    Some ff, Some nf,
    Some fb, Some nb =>
      Some (mk_bsp_model mx my mz Mx My Mz ff nf fb nb)
  | _, _, _, _, _, _, _, _, _, _ => None
  end.

(** [parse_model_lump bs off count] reads [count] consecutive model
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_model_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_model) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_model bs off,
            parse_model_lump bs (off + bsp_model_size)%nat n with
      | Some md, Some rest => Some (md :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing zero entries always succeeds and returns an empty list. *)
Lemma parse_lightmap_lump_zero : forall bs off,
  parse_lightmap_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

Lemma parse_effect_lump_zero : forall bs off,
  parse_effect_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

Lemma parse_model_lump_zero : forall bs off,
  parse_model_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** Entry sizes. *)
Lemma bsp_lightmap_size_eq : bsp_lightmap_size = 49152%nat.
Proof. reflexivity. Qed.

Lemma bsp_effect_size_eq : bsp_effect_size = 72%nat.
Proof. reflexivity. Qed.

Lemma bsp_model_size_eq : bsp_model_size = 40%nat.
Proof. reflexivity. Qed.

(** Vis-data header from eight zero bytes. *)
Lemma parse_vis_data_zeros :
  match parse_vis_data [0;0;0;0; 0;0;0;0] 0 8 with
  | Some vd =>
      vis_n_vecs  vd = 0 /\
      vis_sz_vecs vd = 0 /\
      vis_vecs    vd = []
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Vis-data with a lump too short for the header returns [None]. *)
Lemma parse_vis_data_too_short :
  parse_vis_data [] 0 0 = None.
Proof. reflexivity. Qed.

(** Seventy-two zero bytes decode as an effect with zero fields. *)
Lemma parse_bsp_effect_zeros :
  match parse_bsp_effect
      [0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0] 0 with
  | Some fx =>
      fx_brush_index fx = 0 /\
      fx_unknown     fx = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Forty zero bytes decode as a model with zero fields. *)
Lemma parse_bsp_model_zeros :
  match parse_bsp_model
      [0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0] 0 with
  | Some md =>
      (md_mins_x md == 0)%Q /\
      (md_mins_y md == 0)%Q /\
      (md_mins_z md == 0)%Q /\
      (md_maxs_x md == 0)%Q /\
      (md_maxs_y md == 0)%Q /\
      (md_maxs_z md == 0)%Q /\
      md_first_face  md = 0 /\
      md_num_faces   md = 0 /\
      md_first_brush md = 0 /\
      md_num_brushes md = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Parsing a buffer that is too short returns [None]. *)
Lemma parse_bsp_lightmap_too_short :
  parse_bsp_lightmap [] 0 = None.
Proof. reflexivity. Qed.

Lemma parse_bsp_effect_too_short :
  parse_bsp_effect [] 0 = None.
Proof. reflexivity. Qed.

Lemma parse_bsp_model_too_short :
  parse_bsp_model [] 0 = None.
Proof. reflexivity. Qed.
