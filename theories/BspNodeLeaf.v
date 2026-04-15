(** * Q3 BSP node, leaf, and leaf-face-index types with lump parsers.

    Defines three spatial-tree lumps of the Q3 BSP format:

    - **Nodes lump** (lump index 3): each entry is an interior BSP tree
      node with a splitting plane, two child references, and a bounding
      box.  Entry size: 36 bytes (9 × i32).

    - **Leaves lump** (lump index 4): each entry is a BSP leaf with a
      cluster and area index, a bounding box, and face/brush ranges.
      Entry size: 48 bytes (12 × i32).

    - **Leaf-faces lump** (lump index 5): each entry is a single signed
      32-bit integer — a face index.  Entry size: 4 bytes.

    All integer fields are 32-bit signed little-endian.  Byte offsets
    follow the Q3 BSP specification exactly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Hello Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** BSP node                                                         *)
(* ------------------------------------------------------------------ *)

(** A single entry in the nodes lump.

    Field layout (offsets relative to entry start):
    - [nd_plane]:       bytes  0–  3  (index into planes lump)
    - [nd_child_front]: bytes  4–  7  (positive = node index, negative = ~leaf index)
    - [nd_child_back]:  bytes  8– 11  (same encoding as [nd_child_front])
    - [nd_mins_x/y/z]:  bytes 12– 23  (AABB minimum corner, i32 each)
    - [nd_maxs_x/y/z]:  bytes 24– 35  (AABB maximum corner, i32 each) *)
Record bsp_node : Type := mk_bsp_node
  { nd_plane       : Z
  ; nd_child_front : Z
  ; nd_child_back  : Z
  ; nd_mins_x      : Z
  ; nd_mins_y      : Z
  ; nd_mins_z      : Z
  ; nd_maxs_x      : Z
  ; nd_maxs_y      : Z
  ; nd_maxs_z      : Z
  }.

(** Size of one nodes-lump entry in bytes (9 × i32). *)
Definition bsp_node_size : nat := 36.

(** [parse_bsp_node bs i] reads one 36-byte node entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 36
    bytes available at that offset. *)
Definition parse_bsp_node (bs : bytes) (i : nat) : option bsp_node :=
  match get_i32_le bs  i,
        get_i32_le bs (i +  4)%nat,
        get_i32_le bs (i +  8)%nat,
        get_i32_le bs (i + 12)%nat,
        get_i32_le bs (i + 16)%nat,
        get_i32_le bs (i + 20)%nat,
        get_i32_le bs (i + 24)%nat,
        get_i32_le bs (i + 28)%nat,
        get_i32_le bs (i + 32)%nat with
  | Some pl, Some cf, Some cb,
    Some mx, Some my, Some mz,
    Some Mx, Some My, Some Mz =>
      Some (mk_bsp_node pl cf cb mx my mz Mx My Mz)
  | _, _, _, _, _, _, _, _, _ => None
  end.

(** [parse_node_lump bs off count] reads [count] consecutive node
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_node_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_node) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_node bs off,
            parse_node_lump bs (off + bsp_node_size)%nat n with
      | Some nd, Some rest => Some (nd :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** BSP leaf                                                         *)
(* ------------------------------------------------------------------ *)

(** A single entry in the leaves lump.

    Field layout (offsets relative to entry start):
    - [lf_cluster]:           bytes  0–  3  (visibility cluster index; -1 = outside)
    - [lf_area]:              bytes  4–  7  (area portal index)
    - [lf_mins_x/y/z]:        bytes  8– 19  (AABB minimum corner, i32 each)
    - [lf_maxs_x/y/z]:        bytes 20– 31  (AABB maximum corner, i32 each)
    - [lf_first_leaf_face]:   bytes 32– 35  (first index into leaf-faces lump)
    - [lf_num_leaf_faces]:    bytes 36– 39  (number of leaf-face entries)
    - [lf_first_leaf_brush]:  bytes 40– 43  (first index into leaf-brushes lump)
    - [lf_num_leaf_brushes]:  bytes 44– 47  (number of leaf-brush entries) *)
Record bsp_leaf : Type := mk_bsp_leaf
  { lf_cluster           : Z
  ; lf_area              : Z
  ; lf_mins_x            : Z
  ; lf_mins_y            : Z
  ; lf_mins_z            : Z
  ; lf_maxs_x            : Z
  ; lf_maxs_y            : Z
  ; lf_maxs_z            : Z
  ; lf_first_leaf_face   : Z
  ; lf_num_leaf_faces    : Z
  ; lf_first_leaf_brush  : Z
  ; lf_num_leaf_brushes  : Z
  }.

(** Size of one leaves-lump entry in bytes (12 × i32). *)
Definition bsp_leaf_size : nat := 48.

(** [parse_bsp_leaf bs i] reads one 48-byte leaf entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 48
    bytes available at that offset. *)
Definition parse_bsp_leaf (bs : bytes) (i : nat) : option bsp_leaf :=
  match get_i32_le bs  i,
        get_i32_le bs (i +  4)%nat,
        get_i32_le bs (i +  8)%nat,
        get_i32_le bs (i + 12)%nat,
        get_i32_le bs (i + 16)%nat,
        get_i32_le bs (i + 20)%nat,
        get_i32_le bs (i + 24)%nat,
        get_i32_le bs (i + 28)%nat,
        get_i32_le bs (i + 32)%nat,
        get_i32_le bs (i + 36)%nat,
        get_i32_le bs (i + 40)%nat,
        get_i32_le bs (i + 44)%nat with
  | Some cl, Some ar,
    Some mx, Some my, Some mz,
    Some Mx, Some My, Some Mz,
    Some ff, Some nf,
    Some fb, Some nb =>
      Some (mk_bsp_leaf cl ar mx my mz Mx My Mz ff nf fb nb)
  | _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.

(** [parse_leaf_lump bs off count] reads [count] consecutive leaf
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_leaf_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_leaf) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_leaf bs off,
            parse_leaf_lump bs (off + bsp_leaf_size)%nat n with
      | Some lf, Some rest => Some (lf :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Leaf-face index                                                  *)
(* ------------------------------------------------------------------ *)

(** Size of one leaf-faces-lump entry in bytes (one i32). *)
Definition bsp_leaf_face_size : nat := 4.

(** [parse_bsp_leaf_face bs i] reads one 4-byte face index from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 4
    bytes available at that offset. *)
Definition parse_bsp_leaf_face (bs : bytes) (i : nat) : option Z :=
  get_i32_le bs i.

(** [parse_leaf_face_lump bs off count] reads [count] consecutive face
    indices from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_leaf_face_lump (bs : bytes) (off : nat) (count : nat)
    : option (list Z) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_leaf_face bs off,
            parse_leaf_face_lump bs (off + bsp_leaf_face_size)%nat n with
      | Some idx, Some rest => Some (idx :: rest)
      | _, _                => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing zero entries always succeeds and returns an empty list. *)
Lemma parse_node_lump_zero : forall bs off,
  parse_node_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

Lemma parse_leaf_lump_zero : forall bs off,
  parse_leaf_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

Lemma parse_leaf_face_lump_zero : forall bs off,
  parse_leaf_face_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** [bsp_node_size] is 36. *)
Lemma bsp_node_size_eq : bsp_node_size = 36%nat.
Proof. reflexivity. Qed.

(** [bsp_leaf_size] is 48. *)
Lemma bsp_leaf_size_eq : bsp_leaf_size = 48%nat.
Proof. reflexivity. Qed.

(** [bsp_leaf_face_size] is 4. *)
Lemma bsp_leaf_face_size_eq : bsp_leaf_face_size = 4%nat.
Proof. reflexivity. Qed.

(** Thirty-six zero bytes decode as a node whose fields are all zero. *)
Lemma parse_bsp_node_zeros :
  match parse_bsp_node
      [0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0] 0 with
  | Some nd =>
      nd_plane       nd = 0 /\
      nd_child_front nd = 0 /\
      nd_child_back  nd = 0 /\
      nd_mins_x      nd = 0 /\
      nd_mins_y      nd = 0 /\
      nd_mins_z      nd = 0 /\
      nd_maxs_x      nd = 0 /\
      nd_maxs_y      nd = 0 /\
      nd_maxs_z      nd = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Forty-eight zero bytes decode as a leaf whose fields are all zero. *)
Lemma parse_bsp_leaf_zeros :
  match parse_bsp_leaf
      [0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0] 0 with
  | Some lf =>
      lf_cluster          lf = 0 /\
      lf_area             lf = 0 /\
      lf_mins_x           lf = 0 /\
      lf_mins_y           lf = 0 /\
      lf_mins_z           lf = 0 /\
      lf_maxs_x           lf = 0 /\
      lf_maxs_y           lf = 0 /\
      lf_maxs_z           lf = 0 /\
      lf_first_leaf_face  lf = 0 /\
      lf_num_leaf_faces   lf = 0 /\
      lf_first_leaf_brush lf = 0 /\
      lf_num_leaf_brushes lf = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Four zero bytes decode as leaf-face index 0. *)
Lemma parse_bsp_leaf_face_zeros :
  parse_bsp_leaf_face [0;0;0;0] 0 = Some 0.
Proof. reflexivity. Qed.

(** Parsing a buffer that is too short returns [None]. *)
Lemma parse_bsp_node_too_short :
  parse_bsp_node [] 0 = None.
Proof. reflexivity. Qed.

Lemma parse_bsp_leaf_too_short :
  parse_bsp_leaf [] 0 = None.
Proof. reflexivity. Qed.

Lemma parse_bsp_leaf_face_too_short :
  parse_bsp_leaf_face [] 0 = None.
Proof. reflexivity. Qed.
