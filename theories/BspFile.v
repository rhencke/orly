(** * Top-level BSP record and parse-from-bytes entry point.

    Assembles every individual lump parser into a single [bsp_file]
    record and provides [parse_bsp_file] as the one-call entry point
    that takes a raw byte list and returns a fully parsed BSP, or
    [None] on any parse failure.

    Lumps with dedicated typed parsers are stored as typed lists.
    Lumps without a typed parser yet (faces, light-volumes) are stored
    as raw byte slices so no data is lost. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Bsp Require Import BspBinary.
From Bsp Require Import BspFormat.
From Bsp Require Import BspPlaneVertex.
From Bsp Require Import BspNodeLeaf.
From Bsp Require Import BspTexture.
From Bsp Require Import BspBrush.
From Bsp Require Import BspLightmapVisEffect.
From Bsp Require Import BspEntity.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Helpers                                                          *)
(* ------------------------------------------------------------------ *)

(** Convert a non-negative [Z] to [nat], clamping negatives to 0. *)
Definition z_to_nat (z : Z) : nat := Z.to_nat (Z.max 0 z).

(** Compute the entry count for a fixed-size lump. *)
Definition lump_count (entry : lump_dir_entry) (entry_size : nat) : nat :=
  match entry_size with
  | O => O
  | _ => z_to_nat (lde_length entry) / entry_size
  end.

(** [slice bs off len] extracts [len] bytes starting at offset [off]. *)
Definition slice (bs : bytes) (off len : nat) : option (list Z) :=
  take_n bs off len.

(** Parse a lump of i32 indices (used for leaf-brushes and mesh-verts). *)
Fixpoint parse_i32_lump (bs : bytes) (off : nat) (count : nat)
    : option (list Z) :=
  match count with
  | O    => Some []
  | S n  =>
      match get_i32_le bs off,
            parse_i32_lump bs (off + 4)%nat n with
      | Some idx, Some rest => Some (idx :: rest)
      | _, _                => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Top-level BSP record                                             *)
(* ------------------------------------------------------------------ *)

Record bsp_file : Type := mk_bsp_file
  { bf_header      : bsp_header
  ; bf_entities    : list bsp_entity
  ; bf_textures    : list bsp_texture
  ; bf_planes      : list bsp_plane
  ; bf_nodes       : list bsp_node
  ; bf_leaves      : list bsp_leaf
  ; bf_leaf_faces  : list Z
  ; bf_leaf_brushes: list Z
  ; bf_models      : list bsp_model
  ; bf_brushes     : list bsp_brush
  ; bf_brush_sides : list bsp_brush_side
  ; bf_vertexes    : list bsp_vertex
  ; bf_mesh_verts  : list Z
  ; bf_effects     : list bsp_effect
  ; bf_faces       : list Z           (** raw bytes -- typed parser pending *)
  ; bf_lightmaps   : list bsp_lightmap
  ; bf_light_vols  : list Z           (** raw bytes -- typed parser pending *)
  ; bf_vis_data    : option bsp_vis_data
  }.

(* ------------------------------------------------------------------ *)
(** ** Parse-from-bytes entry point                                     *)
(* ------------------------------------------------------------------ *)

(** [parse_bsp_file bs] parses a complete Q3 BSP file from raw bytes.
    Returns [None] if the header is invalid or any lump fails to parse. *)
Definition parse_bsp_file (bs : bytes) : option bsp_file :=
  match parse_bsp_header bs with
  | None => None
  | Some hdr =>
      let dir := hdr_directory hdr in
      let off  (e : lump_dir_entry) := z_to_nat (lde_offset e) in
      let len  (e : lump_dir_entry) := z_to_nat (lde_length e) in
      let cnt  (e : lump_dir_entry) (sz : nat) := lump_count e sz in
      (* entity lump: text-based, variable length *)
      let e_ent := ldir_entities dir in
      match slice bs (off e_ent) (len e_ent) with
      | None => None
      | Some ent_bytes =>
      match parse_entities ent_bytes with
      | None => None
      | Some entities =>
      (* fixed-size lumps *)
      let e_tex := ldir_textures    dir in
      let e_pln := ldir_planes      dir in
      let e_nod := ldir_nodes       dir in
      let e_lef := ldir_leaves      dir in
      let e_lff := ldir_leaf_faces  dir in
      let e_lbr := ldir_leaf_brushes dir in
      let e_mod := ldir_models      dir in
      let e_bru := ldir_brushes     dir in
      let e_brs := ldir_brush_sides dir in
      let e_vtx := ldir_vertexes    dir in
      let e_mvt := ldir_mesh_verts  dir in
      let e_efx := ldir_effects     dir in
      let e_fac := ldir_faces       dir in
      let e_lmp := ldir_lightmaps   dir in
      let e_lvl := ldir_light_vols  dir in
      let e_vis := ldir_vis_data    dir in
      match parse_texture_lump   bs (off e_tex) (cnt e_tex bsp_texture_size),
            parse_plane_lump     bs (off e_pln) (cnt e_pln bsp_plane_size),
            parse_node_lump      bs (off e_nod) (cnt e_nod bsp_node_size),
            parse_leaf_lump      bs (off e_lef) (cnt e_lef bsp_leaf_size),
            parse_leaf_face_lump bs (off e_lff) (cnt e_lff 4%nat),
            parse_i32_lump       bs (off e_lbr) (cnt e_lbr 4%nat),
            parse_model_lump     bs (off e_mod) (cnt e_mod bsp_model_size),
            parse_brush_lump     bs (off e_bru) (cnt e_bru bsp_brush_size),
            parse_brush_side_lump bs (off e_brs) (cnt e_brs bsp_brush_side_size),
            parse_vertex_lump    bs (off e_vtx) (cnt e_vtx bsp_vertex_size),
            parse_i32_lump       bs (off e_mvt) (cnt e_mvt 4%nat),
            parse_effect_lump    bs (off e_efx) (cnt e_efx bsp_effect_size),
            slice                bs (off e_fac) (len e_fac),
            parse_lightmap_lump  bs (off e_lmp) (cnt e_lmp bsp_lightmap_size),
            slice                bs (off e_lvl) (len e_lvl) with
      | Some textures,  Some planes,     Some nodes,
        Some leaves,    Some leaf_faces, Some leaf_brushes,
        Some models,    Some brushes,    Some brush_sides,
        Some vertexes,  Some mesh_verts, Some effects,
        Some faces_raw, Some lightmaps,  Some lvols_raw =>
          (* vis data: optional -- zero-length lump is valid *)
          let vis :=
            if (len e_vis =? 0)%nat then Some None
            else match parse_vis_data bs (off e_vis) (len e_vis) with
                 | Some vd => Some (Some vd)
                 | None    => None
                 end in
          match vis with
          | Some vis_opt =>
              Some (mk_bsp_file hdr entities textures planes nodes
                                leaves leaf_faces leaf_brushes
                                models brushes brush_sides
                                vertexes mesh_verts effects
                                faces_raw lightmaps lvols_raw vis_opt)
          | None => None
          end
      | _, _, _, _, _, _, _, _, _, _, _, _, _, _, _ => None
      end
      end
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing an empty buffer returns [None] (header validation fails). *)
Lemma parse_bsp_file_empty :
  parse_bsp_file [] = None.
Proof. reflexivity. Qed.

(** [lump_count] with entry size 0 returns 0 (avoids division by zero). *)
Lemma lump_count_zero_size : forall e,
  lump_count e 0 = 0%nat.
Proof. reflexivity. Qed.

(** [z_to_nat] clamps negative values to 0. *)
Lemma z_to_nat_neg : z_to_nat (-1) = 0%nat.
Proof. reflexivity. Qed.

(** [z_to_nat] preserves non-negative values. *)
Lemma z_to_nat_pos : z_to_nat 42 = 42%nat.
Proof. reflexivity. Qed.

(** Parsing zero i32 indices always succeeds. *)
Lemma parse_i32_lump_zero : forall bs off,
  parse_i32_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** Four zero bytes decode as i32 index 0. *)
Lemma parse_i32_lump_single_zero :
  parse_i32_lump [0;0;0;0] 0 1 = Some [0].
Proof. reflexivity. Qed.
