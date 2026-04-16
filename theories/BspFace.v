(** * Q3 BSP face/surface type with lump parser.

    Defines the face/surface lump of the Q3 BSP format:

    - **Faces lump** (lump index 13): each entry is a surface record
      describing a renderable face.  It references texture, effect,
      vertex, and mesh-vertex indices, lightmap placement, surface
      normal, and (for patches) the control-point grid dimensions.
      Entry size: 104 bytes (26 × 4 bytes: a mix of i32 and f32).

    The [fc_type] field distinguishes four surface types:
    - 1 = polygon
    - 2 = Bézier patch
    - 3 = triangle mesh
    - 4 = billboard (axis-aligned sprite)

    All integer fields are 32-bit signed little-endian.  All float
    fields are IEEE 754 single-precision little-endian, decoded to
    exact [Q] rationals.  Byte offsets follow the Q3 BSP specification
    exactly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Bsp Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Face / surface                                                   *)
(* ------------------------------------------------------------------ *)

(** A single entry in the faces lump.

    Field layout (offsets relative to entry start):
    - [fc_texture]:     bytes   0–  3  (texture index)
    - [fc_effect]:      bytes   4–  7  (effect index; -1 = none)
    - [fc_type]:        bytes   8– 11  (face type: 1–4)
    - [fc_vertex]:      bytes  12– 15  (first vertex index)
    - [fc_n_vertexes]:  bytes  16– 19  (number of vertices)
    - [fc_meshvert]:    bytes  20– 23  (first mesh-vertex index)
    - [fc_n_meshverts]: bytes  24– 27  (number of mesh-vertices)
    - [fc_lm_index]:    bytes  28– 31  (lightmap index; -1 = none)
    - [fc_lm_start_x]:  bytes  32– 35  (lightmap corner X in atlas)
    - [fc_lm_start_y]:  bytes  36– 39  (lightmap corner Y in atlas)
    - [fc_lm_size_x]:   bytes  40– 43  (lightmap width in texels)
    - [fc_lm_size_y]:   bytes  44– 47  (lightmap height in texels)
    - [fc_lm_origin_x]: bytes  48– 51  (world-space lightmap origin X, f32)
    - [fc_lm_origin_y]: bytes  52– 55  (world-space lightmap origin Y, f32)
    - [fc_lm_origin_z]: bytes  56– 59  (world-space lightmap origin Z, f32)
    - [fc_lm_vecs_s_x]: bytes  60– 63  (lightmap S-axis X, f32)
    - [fc_lm_vecs_s_y]: bytes  64– 67  (lightmap S-axis Y, f32)
    - [fc_lm_vecs_s_z]: bytes  68– 71  (lightmap S-axis Z, f32)
    - [fc_lm_vecs_t_x]: bytes  72– 75  (lightmap T-axis X, f32)
    - [fc_lm_vecs_t_y]: bytes  76– 79  (lightmap T-axis Y, f32)
    - [fc_lm_vecs_t_z]: bytes  80– 83  (lightmap T-axis Z, f32)
    - [fc_normal_x]:    bytes  84– 87  (surface normal X, f32)
    - [fc_normal_y]:    bytes  88– 91  (surface normal Y, f32)
    - [fc_normal_z]:    bytes  92– 95  (surface normal Z, f32)
    - [fc_size_x]:      bytes  96– 99  (patch grid width, i32)
    - [fc_size_y]:      bytes 100–103  (patch grid height, i32) *)
Record bsp_face : Type := mk_bsp_face
  { fc_texture     : Z
  ; fc_effect      : Z
  ; fc_type        : Z
  ; fc_vertex      : Z
  ; fc_n_vertexes  : Z
  ; fc_meshvert    : Z
  ; fc_n_meshverts : Z
  ; fc_lm_index    : Z
  ; fc_lm_start_x  : Z
  ; fc_lm_start_y  : Z
  ; fc_lm_size_x   : Z
  ; fc_lm_size_y   : Z
  ; fc_lm_origin_x : Q
  ; fc_lm_origin_y : Q
  ; fc_lm_origin_z : Q
  ; fc_lm_vecs_s_x : Q
  ; fc_lm_vecs_s_y : Q
  ; fc_lm_vecs_s_z : Q
  ; fc_lm_vecs_t_x : Q
  ; fc_lm_vecs_t_y : Q
  ; fc_lm_vecs_t_z : Q
  ; fc_normal_x    : Q
  ; fc_normal_y    : Q
  ; fc_normal_z    : Q
  ; fc_size_x      : Z
  ; fc_size_y      : Z
  }.

(** Size of one faces-lump entry in bytes (26 × 4). *)
Definition bsp_face_size : nat := 104.

(** [parse_bsp_face bs i] reads one 104-byte face entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 104
    bytes available at that offset. *)
Definition parse_bsp_face (bs : bytes) (i : nat) : option bsp_face :=
  match get_i32_le bs  i,
        get_i32_le bs (i +   4)%nat,
        get_i32_le bs (i +   8)%nat,
        get_i32_le bs (i +  12)%nat,
        get_i32_le bs (i +  16)%nat,
        get_i32_le bs (i +  20)%nat,
        get_i32_le bs (i +  24)%nat,
        get_i32_le bs (i +  28)%nat,
        get_i32_le bs (i +  32)%nat,
        get_i32_le bs (i +  36)%nat,
        get_i32_le bs (i +  40)%nat,
        get_i32_le bs (i +  44)%nat,
        get_f32_le bs (i +  48)%nat,
        get_f32_le bs (i +  52)%nat,
        get_f32_le bs (i +  56)%nat,
        get_f32_le bs (i +  60)%nat,
        get_f32_le bs (i +  64)%nat,
        get_f32_le bs (i +  68)%nat,
        get_f32_le bs (i +  72)%nat,
        get_f32_le bs (i +  76)%nat,
        get_f32_le bs (i +  80)%nat,
        get_f32_le bs (i +  84)%nat,
        get_f32_le bs (i +  88)%nat,
        get_f32_le bs (i +  92)%nat,
        get_i32_le bs (i +  96)%nat,
        get_i32_le bs (i + 100)%nat with
  | Some tex,  Some eff,  Some typ,
    Some vtx,  Some nvtx, Some mvt,  Some nmvt,
    Some lmi,  Some lsx,  Some lsy,  Some lwx,  Some lwy,
    Some lox,  Some loy,  Some loz,
    Some lssx, Some lssy, Some lssz,
    Some lstx, Some lsty, Some lstz,
    Some nx,   Some ny,   Some nz,
    Some sx,   Some sy =>
      Some (mk_bsp_face tex eff typ vtx nvtx mvt nmvt
                         lmi lsx lsy lwx lwy
                         lox loy loz
                         lssx lssy lssz
                         lstx lsty lstz
                         nx ny nz sx sy)
  | _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.

(** [parse_face_lump bs off count] reads [count] consecutive face
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_face_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_face) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_face bs off,
            parse_face_lump bs (off + bsp_face_size)%nat n with
      | Some fc, Some rest => Some (fc :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing zero entries always succeeds and returns an empty list. *)
Lemma parse_face_lump_zero : forall bs off,
  parse_face_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** [bsp_face_size] is 104. *)
Lemma bsp_face_size_eq : bsp_face_size = 104%nat.
Proof. reflexivity. Qed.

(** Parsing a buffer that is too short returns [None]. *)
Lemma parse_bsp_face_too_short :
  parse_bsp_face [] 0 = None.
Proof. reflexivity. Qed.

(** 104 zero bytes decode as a face whose integer fields are all zero
    and whose float fields are all Qeq to zero. *)
Lemma parse_bsp_face_zeros :
  match parse_bsp_face
    [0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
     0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
     0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
     0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
     0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
     0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
     0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0] 0 with
  | Some fc =>
      fc_texture     fc = 0 /\
      fc_effect      fc = 0 /\
      fc_type        fc = 0 /\
      fc_vertex      fc = 0 /\
      fc_n_vertexes  fc = 0 /\
      fc_meshvert    fc = 0 /\
      fc_n_meshverts fc = 0 /\
      fc_lm_index    fc = 0 /\
      fc_lm_start_x  fc = 0 /\
      fc_lm_start_y  fc = 0 /\
      fc_lm_size_x   fc = 0 /\
      fc_lm_size_y   fc = 0 /\
      (fc_lm_origin_x fc == 0)%Q /\
      (fc_lm_origin_y fc == 0)%Q /\
      (fc_lm_origin_z fc == 0)%Q /\
      (fc_lm_vecs_s_x fc == 0)%Q /\
      (fc_lm_vecs_s_y fc == 0)%Q /\
      (fc_lm_vecs_s_z fc == 0)%Q /\
      (fc_lm_vecs_t_x fc == 0)%Q /\
      (fc_lm_vecs_t_y fc == 0)%Q /\
      (fc_lm_vecs_t_z fc == 0)%Q /\
      (fc_normal_x    fc == 0)%Q /\
      (fc_normal_y    fc == 0)%Q /\
      (fc_normal_z    fc == 0)%Q /\
      fc_size_x      fc = 0 /\
      fc_size_y      fc = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.
