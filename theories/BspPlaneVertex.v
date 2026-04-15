(** * Q3 BSP plane and vertex types with lump parsers.

    Defines the two geometry primitive lumps of the Q3 BSP format:

    - **Planes lump** (lump index 2): each entry is a plane equation
      stored as four IEEE 754 single-precision floats — the outward
      normal [px_normal_x], [px_normal_y], [px_normal_z], and the
      distance from the origin [px_dist].  Entry size: 16 bytes.

    - **Vertexes lump** (lump index 10): each entry is a vertex with
      ten floats (position xyz, surface texture-coordinate st, lightmap
      texture-coordinate st, surface normal xyz) followed by four
      unsigned bytes (RGBA colour).  Entry size: 44 bytes.

    All floats are decoded to exact [Q] rationals via [decode_f32_bits]
    from [BspBinary].  Byte offsets follow the Q3 BSP specification
    exactly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Hello Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Plane                                                            *)
(* ------------------------------------------------------------------ *)

(** A single entry in the planes lump.  The normal vector
    [(px_normal_x, px_normal_y, px_normal_z)] is unit-length in valid
    BSP files; [px_dist] is the signed distance from the origin along
    that normal. *)
Record bsp_plane : Type := mk_bsp_plane
  { px_normal_x : Q
  ; px_normal_y : Q
  ; px_normal_z : Q
  ; px_dist     : Q
  }.

(** Size of one planes-lump entry in bytes (4 floats × 4 bytes). *)
Definition bsp_plane_size : nat := 16.

(** [parse_bsp_plane bs i] reads one 16-byte plane entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 16
    bytes available at that offset. *)
Definition parse_bsp_plane (bs : bytes) (i : nat) : option bsp_plane :=
  match get_f32_le bs  i,
        get_f32_le bs (i +  4)%nat,
        get_f32_le bs (i +  8)%nat,
        get_f32_le bs (i + 12)%nat with
  | Some nx, Some ny, Some nz, Some d =>
      Some (mk_bsp_plane nx ny nz d)
  | _, _, _, _ => None
  end.

(** [parse_plane_lump bs off count] reads [count] consecutive plane
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_plane_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_plane) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_plane bs off,
            parse_plane_lump bs (off + bsp_plane_size)%nat n with
      | Some p, Some rest => Some (p :: rest)
      | _, _              => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Vertex                                                           *)
(* ------------------------------------------------------------------ *)

(** A single entry in the vertexes lump.

    Field layout (offsets relative to entry start):
    - [vx_pos_x / _y / _z]:          bytes  0– 11  (position)
    - [vx_tex_s / _t]:                bytes 12– 19  (surface texcoord)
    - [vx_lm_s  / _t]:                bytes 20– 27  (lightmap texcoord)
    - [vx_norm_x / _y / _z]:          bytes 28– 39  (surface normal)
    - [vx_color_r / _g / _b / _a]:    bytes 40– 43  (RGBA colour, 0–255) *)
Record bsp_vertex : Type := mk_bsp_vertex
  { vx_pos_x   : Q
  ; vx_pos_y   : Q
  ; vx_pos_z   : Q
  ; vx_tex_s   : Q
  ; vx_tex_t   : Q
  ; vx_lm_s    : Q
  ; vx_lm_t    : Q
  ; vx_norm_x  : Q
  ; vx_norm_y  : Q
  ; vx_norm_z  : Q
  ; vx_color_r : Z
  ; vx_color_g : Z
  ; vx_color_b : Z
  ; vx_color_a : Z
  }.

(** Size of one vertexes-lump entry in bytes (10 floats × 4 bytes + 4 colour bytes). *)
Definition bsp_vertex_size : nat := 44.

(** [parse_bsp_vertex bs i] reads one 44-byte vertex entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 44
    bytes available at that offset. *)
Definition parse_bsp_vertex (bs : bytes) (i : nat) : option bsp_vertex :=
  match get_f32_le bs  i,
        get_f32_le bs (i +  4)%nat,
        get_f32_le bs (i +  8)%nat,
        get_f32_le bs (i + 12)%nat,
        get_f32_le bs (i + 16)%nat,
        get_f32_le bs (i + 20)%nat,
        get_f32_le bs (i + 24)%nat,
        get_f32_le bs (i + 28)%nat,
        get_f32_le bs (i + 32)%nat,
        get_f32_le bs (i + 36)%nat,
        get_u8     bs (i + 40)%nat,
        get_u8     bs (i + 41)%nat,
        get_u8     bs (i + 42)%nat,
        get_u8     bs (i + 43)%nat with
  | Some px, Some py, Some pz,
    Some ts, Some tv,
    Some ls, Some lv,
    Some nx, Some ny, Some nz,
    Some r,  Some g,  Some b,  Some a =>
      Some (mk_bsp_vertex px py pz ts tv ls lv nx ny nz r g b a)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.

(** [parse_vertex_lump bs off count] reads [count] consecutive vertex
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_vertex_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_vertex) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_vertex bs off,
            parse_vertex_lump bs (off + bsp_vertex_size)%nat n with
      | Some v, Some rest => Some (v :: rest)
      | _, _              => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing zero entries always succeeds and returns an empty list. *)
Lemma parse_plane_lump_zero : forall bs off,
  parse_plane_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

Lemma parse_vertex_lump_zero : forall bs off,
  parse_vertex_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** Sixteen zero bytes decode as a plane whose fields are all Qeq to zero. *)
Lemma parse_bsp_plane_zeros :
  match parse_bsp_plane [0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0] 0 with
  | Some p =>
      (px_normal_x p == 0)%Q /\
      (px_normal_y p == 0)%Q /\
      (px_normal_z p == 0)%Q /\
      (px_dist     p == 0)%Q
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** [bsp_plane_size] is 16. *)
Lemma bsp_plane_size_eq : bsp_plane_size = 16%nat.
Proof. reflexivity. Qed.

(** [bsp_vertex_size] is 44. *)
Lemma bsp_vertex_size_eq : bsp_vertex_size = 44%nat.
Proof. reflexivity. Qed.

(** Parsing a buffer that is too short returns [None]. *)
Lemma parse_bsp_plane_too_short :
  parse_bsp_plane [] 0 = None.
Proof. reflexivity. Qed.

Lemma parse_bsp_vertex_too_short :
  parse_bsp_vertex [] 0 = None.
Proof. reflexivity. Qed.
