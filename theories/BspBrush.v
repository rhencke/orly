(** * Q3 BSP brush and brush-side types with lump parsers.

    Defines two collision-geometry lumps of the Q3 BSP format:

    - **Brushes lump** (lump index 8): each entry is a convex brush
      volume described by a range of brush sides and a texture
      reference.  Entry size: 12 bytes (3 x i32).

    - **Brush sides lump** (lump index 9): each entry is a single
      bounding half-space — a plane reference and a texture reference.
      Entry size: 8 bytes (2 x i32).

    All integer fields are 32-bit signed little-endian.  Byte offsets
    follow the Q3 BSP specification exactly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Hello Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Brush                                                            *)
(* ------------------------------------------------------------------ *)

(** A single entry in the brushes lump.

    Field layout (offsets relative to entry start):
    - [br_first_side]:    bytes 0– 3  (index of first brush side)
    - [br_num_sides]:     bytes 4– 7  (number of brush sides)
    - [br_texture_index]: bytes 8–11  (index into textures lump) *)
Record bsp_brush : Type := mk_bsp_brush
  { br_first_side    : Z
  ; br_num_sides     : Z
  ; br_texture_index : Z
  }.

(** Size of one brushes-lump entry in bytes (3 x i32). *)
Definition bsp_brush_size : nat := 12.

(** [parse_bsp_brush bs i] reads one 12-byte brush entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 12
    bytes available at that offset. *)
Definition parse_bsp_brush (bs : bytes) (i : nat) : option bsp_brush :=
  match get_i32_le bs  i,
        get_i32_le bs (i + 4)%nat,
        get_i32_le bs (i + 8)%nat with
  | Some fs, Some ns, Some tx =>
      Some (mk_bsp_brush fs ns tx)
  | _, _, _ => None
  end.

(** [parse_brush_lump bs off count] reads [count] consecutive brush
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_brush_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_brush) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_brush bs off,
            parse_brush_lump bs (off + bsp_brush_size)%nat n with
      | Some br, Some rest => Some (br :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Brush side                                                       *)
(* ------------------------------------------------------------------ *)

(** A single entry in the brush-sides lump.

    Field layout (offsets relative to entry start):
    - [bs_plane_index]:   bytes 0–3  (index into planes lump)
    - [bs_texture_index]: bytes 4–7  (index into textures lump) *)
Record bsp_brush_side : Type := mk_bsp_brush_side
  { bs_plane_index   : Z
  ; bs_texture_index : Z
  }.

(** Size of one brush-sides-lump entry in bytes (2 x i32). *)
Definition bsp_brush_side_size : nat := 8.

(** [parse_bsp_brush_side bs i] reads one 8-byte brush-side entry from
    byte offset [i] in [bs].  Returns [None] if there are fewer than 8
    bytes available at that offset. *)
Definition parse_bsp_brush_side (bs : bytes) (i : nat) : option bsp_brush_side :=
  match get_i32_le bs  i,
        get_i32_le bs (i + 4)%nat with
  | Some pl, Some tx =>
      Some (mk_bsp_brush_side pl tx)
  | _, _ => None
  end.

(** [parse_brush_side_lump bs off count] reads [count] consecutive
    brush-side entries from byte offset [off] in [bs].  Returns [None]
    if any entry cannot be read. *)
Fixpoint parse_brush_side_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_brush_side) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_brush_side bs off,
            parse_brush_side_lump bs (off + bsp_brush_side_size)%nat n with
      | Some s, Some rest => Some (s :: rest)
      | _, _              => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing zero entries always succeeds and returns an empty list. *)
Lemma parse_brush_lump_zero : forall bs off,
  parse_brush_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

Lemma parse_brush_side_lump_zero : forall bs off,
  parse_brush_side_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** [bsp_brush_size] is 12. *)
Lemma bsp_brush_size_eq : bsp_brush_size = 12%nat.
Proof. reflexivity. Qed.

(** [bsp_brush_side_size] is 8. *)
Lemma bsp_brush_side_size_eq : bsp_brush_side_size = 8%nat.
Proof. reflexivity. Qed.

(** Twelve zero bytes decode as a brush whose fields are all zero. *)
Lemma parse_bsp_brush_zeros :
  match parse_bsp_brush
      [0;0;0;0; 0;0;0;0; 0;0;0;0] 0 with
  | Some br =>
      br_first_side    br = 0 /\
      br_num_sides     br = 0 /\
      br_texture_index br = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Eight zero bytes decode as a brush side whose fields are all zero. *)
Lemma parse_bsp_brush_side_zeros :
  match parse_bsp_brush_side
      [0;0;0;0; 0;0;0;0] 0 with
  | Some s =>
      bs_plane_index   s = 0 /\
      bs_texture_index s = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Parsing a buffer that is too short returns [None]. *)
Lemma parse_bsp_brush_too_short :
  parse_bsp_brush [] 0 = None.
Proof. reflexivity. Qed.

Lemma parse_bsp_brush_side_too_short :
  parse_bsp_brush_side [] 0 = None.
Proof. reflexivity. Qed.
