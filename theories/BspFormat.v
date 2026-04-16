(** * Q3 BSP file header, lump directory, and lump-index enumeration.

    The Quake 3 BSP format begins with a four-byte magic identifier
    [IBSP] followed by a 32-bit version number, then seventeen lump
    directory entries.  Each entry records the file offset and byte
    length of one named lump.

    This module defines:
    - [bsp_magic] and [bsp_version]: the expected header constants.
    - [lump_dir_entry]: a single lump-directory record (offset + length).
    - [lump_directory]: all seventeen lump-directory entries together.
    - [LumpIndex]: an enumeration of the seventeen named lumps.
    - [lump_dir_entry_at]: look up a directory entry by [LumpIndex].
    - [parse_lump_dir_entry] / [parse_lump_directory] / [parse_bsp_header]:
      byte-level parsers that read these structures from a raw [bytes]
      sequence and return [None] on malformed input. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Bsp Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Header constants                                                 *)
(* ------------------------------------------------------------------ *)

(** The four-byte magic string [IBSP], stored as a little-endian 32-bit
    integer: [0x49425350]. *)
Definition bsp_magic : Z := 0x49425350.

(** The BSP format version used by Quake 3 and Quake 3: Team Arena. *)
Definition bsp_version : Z := 46.

(* ------------------------------------------------------------------ *)
(** ** Lump directory entry                                             *)
(* ------------------------------------------------------------------ *)

(** A single entry in the lump directory.  [lde_offset] is the byte
    offset from the start of the file to the lump's data; [lde_length]
    is the number of bytes in the lump. *)
Record lump_dir_entry : Type := mk_lump_dir_entry
  { lde_offset : Z
  ; lde_length : Z
  }.

(** [parse_lump_dir_entry bs i] reads one eight-byte lump directory
    entry from byte offset [i] in [bs].  Returns [None] if there are
    fewer than eight bytes available. *)
Definition parse_lump_dir_entry (bs : bytes) (i : nat) : option lump_dir_entry :=
  match get_i32_le bs i, get_i32_le bs (i + 4)%nat with
  | Some off, Some len => Some (mk_lump_dir_entry off len)
  | _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Lump-index enumeration                                           *)
(* ------------------------------------------------------------------ *)

(** The seventeen lumps defined by the Q3 BSP format, in the order they
    appear in the directory (indices 0–16). *)
Inductive LumpIndex : Type :=
  | LumpEntities        (* 0  — entity description text *)
  | LumpTextures        (* 1  — texture references *)
  | LumpPlanes          (* 2  — plane equations *)
  | LumpNodes           (* 3  — BSP interior nodes *)
  | LumpLeaves          (* 4  — BSP leaves *)
  | LumpLeafFaces       (* 5  — per-leaf face index lists *)
  | LumpLeafBrushes     (* 6  — per-leaf brush index lists *)
  | LumpModels          (* 7  — sub-models *)
  | LumpBrushes         (* 8  — brush records *)
  | LumpBrushSides      (* 9  — brush side records *)
  | LumpVertexes        (* 10 — geometry vertices *)
  | LumpMeshVerts       (* 11 — mesh-vertex offsets *)
  | LumpEffects         (* 12 — fog/effect volumes *)
  | LumpFaces           (* 13 — surface/face records *)
  | LumpLightmaps       (* 14 — lightmap image data *)
  | LumpLightVols       (* 15 — volumetric lighting *)
  | LumpVisData.        (* 16 — PVS visibility data *)

(** Total number of lumps in a Q3 BSP header. *)
Definition num_lumps : nat := 17.

(** Convert a [LumpIndex] to its zero-based ordinal position in the
    directory. *)
Definition lump_index_to_nat (li : LumpIndex) : nat :=
  match li with
  | LumpEntities    =>  0
  | LumpTextures    =>  1
  | LumpPlanes      =>  2
  | LumpNodes       =>  3
  | LumpLeaves      =>  4
  | LumpLeafFaces   =>  5
  | LumpLeafBrushes =>  6
  | LumpModels      =>  7
  | LumpBrushes     =>  8
  | LumpBrushSides  =>  9
  | LumpVertexes    => 10
  | LumpMeshVerts   => 11
  | LumpEffects     => 12
  | LumpFaces       => 13
  | LumpLightmaps   => 14
  | LumpLightVols   => 15
  | LumpVisData     => 16
  end.

(* ------------------------------------------------------------------ *)
(** ** Lump directory                                                   *)
(* ------------------------------------------------------------------ *)

(** All seventeen lump-directory entries, one per named lump.
    Field names mirror the [LumpIndex] constructors. *)
Record lump_directory : Type := mk_lump_directory
  { ldir_entities    : lump_dir_entry
  ; ldir_textures    : lump_dir_entry
  ; ldir_planes      : lump_dir_entry
  ; ldir_nodes       : lump_dir_entry
  ; ldir_leaves      : lump_dir_entry
  ; ldir_leaf_faces  : lump_dir_entry
  ; ldir_leaf_brushes: lump_dir_entry
  ; ldir_models      : lump_dir_entry
  ; ldir_brushes     : lump_dir_entry
  ; ldir_brush_sides : lump_dir_entry
  ; ldir_vertexes    : lump_dir_entry
  ; ldir_mesh_verts  : lump_dir_entry
  ; ldir_effects     : lump_dir_entry
  ; ldir_faces       : lump_dir_entry
  ; ldir_lightmaps   : lump_dir_entry
  ; ldir_light_vols  : lump_dir_entry
  ; ldir_vis_data    : lump_dir_entry
  }.

(** [lump_dir_entry_at dir li] retrieves the directory entry for lump [li]. *)
Definition lump_dir_entry_at (dir : lump_directory) (li : LumpIndex) : lump_dir_entry :=
  match li with
  | LumpEntities    => ldir_entities     dir
  | LumpTextures    => ldir_textures     dir
  | LumpPlanes      => ldir_planes       dir
  | LumpNodes       => ldir_nodes        dir
  | LumpLeaves      => ldir_leaves       dir
  | LumpLeafFaces   => ldir_leaf_faces   dir
  | LumpLeafBrushes => ldir_leaf_brushes dir
  | LumpModels      => ldir_models       dir
  | LumpBrushes     => ldir_brushes      dir
  | LumpBrushSides  => ldir_brush_sides  dir
  | LumpVertexes    => ldir_vertexes     dir
  | LumpMeshVerts   => ldir_mesh_verts   dir
  | LumpEffects     => ldir_effects      dir
  | LumpFaces       => ldir_faces        dir
  | LumpLightmaps   => ldir_lightmaps    dir
  | LumpLightVols   => ldir_light_vols   dir
  | LumpVisData     => ldir_vis_data     dir
  end.

(** [parse_lump_directory bs] reads all seventeen lump-directory entries
    from [bs], beginning at byte offset 8 (immediately after the magic
    and version fields).  Each entry is 8 bytes, so the directory
    occupies bytes 8–143.  Returns [None] if any entry cannot be read. *)
Definition parse_lump_directory (bs : bytes) : option lump_directory :=
  (* Directory starts at offset 8; each entry is 8 bytes. *)
  let at_ (n : nat) := parse_lump_dir_entry bs (8 + n * 8)%nat in
  match at_ 0%nat,  at_ 1%nat,  at_ 2%nat,  at_ 3%nat,
        at_ 4%nat,  at_ 5%nat,  at_ 6%nat,  at_ 7%nat,
        at_ 8%nat,  at_ 9%nat,  at_ 10%nat, at_ 11%nat,
        at_ 12%nat, at_ 13%nat, at_ 14%nat, at_ 15%nat,
        at_ 16%nat with
  | Some e0,  Some e1,  Some e2,  Some e3,
    Some e4,  Some e5,  Some e6,  Some e7,
    Some e8,  Some e9,  Some e10, Some e11,
    Some e12, Some e13, Some e14, Some e15,
    Some e16 =>
      Some (mk_lump_directory e0  e1  e2  e3
                               e4  e5  e6  e7
                               e8  e9  e10 e11
                               e12 e13 e14 e15
                               e16)
  | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** BSP file header                                                  *)
(* ------------------------------------------------------------------ *)

(** The complete BSP file header: verified magic, version, and the full
    lump directory. *)
Record bsp_header : Type := mk_bsp_header
  { hdr_magic     : Z
  ; hdr_version   : Z
  ; hdr_directory : lump_directory
  }.

(** [parse_bsp_header bs] validates the magic and version fields at the
    start of [bs] and then parses the full lump directory.  Returns
    [None] if:
    - the file is too short to contain the magic or version fields, or
    - the magic does not equal [bsp_magic], or
    - the version does not equal [bsp_version], or
    - any lump-directory entry cannot be read. *)
Definition parse_bsp_header (bs : bytes) : option bsp_header :=
  match get_u32_le bs 0, get_i32_le bs 4 with
  | Some magic, Some version =>
      if (magic =? bsp_magic) && (version =? bsp_version) then
        match parse_lump_directory bs with
        | Some dir => Some (mk_bsp_header magic version dir)
        | None     => None
        end
      else
        None
  | _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** The [lump_index_to_nat] function maps each constructor to a value
    strictly less than [num_lumps]. *)
Lemma lump_index_to_nat_bound : forall li,
  (lump_index_to_nat li < num_lumps)%nat.
Proof.
  intro li. destruct li; unfold lump_index_to_nat, num_lumps; lia.
Qed.

(** [lump_dir_entry_at] round-trips: reading the field that corresponds
    to a given index returns the same entry that was stored there. *)
Lemma lump_dir_entry_at_entities : forall e0 e1 e2 e3 e4 e5 e6 e7
                                          e8 e9 e10 e11 e12 e13 e14 e15 e16,
  lump_dir_entry_at
    (mk_lump_directory e0 e1 e2 e3 e4 e5 e6 e7
                       e8 e9 e10 e11 e12 e13 e14 e15 e16)
    LumpEntities = e0.
Proof. reflexivity. Qed.

(** Parsing an eight-byte sequence of zeros yields offset 0, length 0. *)
Lemma parse_lump_dir_entry_zeros :
  parse_lump_dir_entry [0;0;0;0; 0;0;0;0] 0 =
    Some (mk_lump_dir_entry 0 0).
Proof. reflexivity. Qed.

(** [parse_bsp_header] rejects a buffer that is too short. *)
Lemma parse_bsp_header_too_short :
  parse_bsp_header [] = None.
Proof. reflexivity. Qed.
