(** * OCaml extraction of the verified BSP parser.

    Extracts [parse_bsp_file] and the cross-lump validation predicate
    [bsp_cross_lump_valid] to OCaml.  The extracted code is linked into
    a standalone validator binary that can parse real BSP files and
    check their structural invariants — no external dependencies needed.

    We use [ExtrOcamlBasic] and [ExtrOcamlNatInt] but deliberately
    avoid [ExtrOcamlZInt]: the IEEE 754 decoder ([decode_f32_bits])
    builds Q rationals with numerators up to 2^128, which would
    silently overflow OCaml's 63-bit int. *)

From Bsp Require Import BspBinary.
From Bsp Require Import BspFormat.
From Bsp Require Import BspPlaneVertex.
From Bsp Require Import BspNodeLeaf.
From Bsp Require Import BspTexture.
From Bsp Require Import BspBrush.
From Bsp Require Import BspLightmapVisEffect.
From Bsp Require Import BspEntity.
From Bsp Require Import BspFile.
From Bsp Require Import BspProofs.

Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.

Set Extraction Output Directory "validate_bsp".
Extraction "bsp_core.ml"
  parse_bsp_file
  bsp_cross_lump_valid
  bf_header bf_entities bf_textures bf_planes bf_nodes bf_leaves
  bf_leaf_faces bf_leaf_brushes bf_models bf_brushes bf_brush_sides
  bf_vertexes bf_mesh_verts bf_effects bf_faces bf_lightmaps
  bf_light_vols bf_vis_data.
