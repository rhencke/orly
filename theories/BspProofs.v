(** * Mechanically verified properties of BSP parsers.

    This module is the proof-theory layer of the BSP parser library.
    Every theorem here follows from the parser definitions and
    represents a living theory — proved today, adjusted when
    counterexamples from real BSP data or spec corrections invalidate
    the claim.

    Three categories:

    1. **Lump parser length correctness** — every lump parser returns
       a list whose length equals the requested count.

    2. **Structural invariants from parsing** — properties that hold
       for any successfully parsed structure (name field widths,
       lightmap sizes, two's-complement ranges).

    3. **Cross-lump consistency predicates** — decidable boolean
       functions that validate inter-lump references against actual
       lump sizes.  These define what "well-formed BSP" means. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
From Bsp Require Import BspBinary.
From Bsp Require Import BspFormat.
From Bsp Require Import BspPlaneVertex.
From Bsp Require Import BspNodeLeaf.
From Bsp Require Import BspTexture.
From Bsp Require Import BspBrush.
From Bsp Require Import BspLightmapVisEffect.
From Bsp Require Import BspEntity.
From Bsp Require Import BspFile.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================== *)
(** * Utility lemmas                                                    *)
(* ================================================================== *)

(** [take_n] returns a list whose length matches the requested count. *)
Lemma take_n_length : forall bs off n xs,
  take_n bs off n = Some xs -> length xs = n.
Proof.
  intros bs off n. revert bs off.
  induction n as [| n' IH]; intros bs off xs H.
  - simpl in H. inversion H. reflexivity.
  - simpl in H.
    destruct (byte_at bs off); try discriminate.
    destruct (take_n bs (off + 1)%nat n') eqn:Et; try discriminate.
    inversion H; subst. simpl. f_equal. eapply IH. exact Et.
Qed.

(* ================================================================== *)
(** * Two's-complement round-trip properties                            *)
(* ================================================================== *)

(** [to_i32] maps unsigned 32-bit values into [[-2^31, 2^31)]. *)
Theorem to_i32_range : forall u,
  0 <= u < 4294967296 ->
  -2147483648 <= to_i32 u < 2147483648.
Proof.
  intros u Hu. unfold to_i32.
  destruct (Z.leb_spec 2147483648 u); lia.
Qed.

(** [to_i16] maps unsigned 16-bit values into [[-2^15, 2^15)]. *)
Theorem to_i16_range : forall u,
  0 <= u < 65536 ->
  -32768 <= to_i16 u < 32768.
Proof.
  intros u Hu. unfold to_i16.
  destruct (Z.leb_spec 32768 u); lia.
Qed.

(** [to_i32] composed with unsigned recovery is the identity on
    [[-2^31, 2^31)].  This is the per-parser round-trip theory for
    the 32-bit two's-complement encoding: any signed value that goes
    through the encoding–decoding cycle comes back unchanged. *)
Theorem to_i32_mod_roundtrip : forall v,
  -2147483648 <= v < 2147483648 ->
  to_i32 (v mod 4294967296) = v.
Proof.
  intros v Hv. unfold to_i32.
  destruct (Z.ltb_spec v 0) as [Hneg | Hpos].
  - replace (v mod 4294967296) with (v + 4294967296)
      by (apply Z.mod_unique with (-1); lia).
    destruct (Z.leb_spec 2147483648 (v + 4294967296)); lia.
  - replace (v mod 4294967296) with v
      by (symmetry; apply Z.mod_small; lia).
    destruct (Z.leb_spec 2147483648 v); lia.
Qed.

(** [to_i16] round-trip on [[-2^15, 2^15)]. *)
Theorem to_i16_mod_roundtrip : forall v,
  -32768 <= v < 32768 ->
  to_i16 (v mod 65536) = v.
Proof.
  intros v Hv. unfold to_i16.
  destruct (Z.ltb_spec v 0) as [Hneg | Hpos].
  - replace (v mod 65536) with (v + 65536)
      by (apply Z.mod_unique with (-1); lia).
    destruct (Z.leb_spec 32768 (v + 65536)); lia.
  - replace (v mod 65536) with v
      by (symmetry; apply Z.mod_small; lia).
    destruct (Z.leb_spec 32768 v); lia.
Qed.

(* ================================================================== *)
(** * LumpIndex properties                                              *)
(* ================================================================== *)

(** [lump_index_to_nat] is injective — distinct lumps map to distinct
    directory slots. *)
Theorem lump_index_to_nat_injective : forall li1 li2,
  lump_index_to_nat li1 = lump_index_to_nat li2 -> li1 = li2.
Proof.
  intros li1 li2 H; destruct li1; destruct li2;
    simpl in H; try reflexivity; discriminate.
Qed.

(* ================================================================== *)
(** * Lump parser length correctness                                    *)
(* ================================================================== *)

(** Generic length lemma for the standard lump-parser pattern. *)
Lemma lump_length_generic :
  forall {A : Type}
         (parse_one : bytes -> nat -> option A)
         (entry_size : nat)
         (parse_lump : bytes -> nat -> nat -> option (list A)),
    (forall bs off, parse_lump bs off 0%nat = Some []) ->
    (forall bs off n,
       parse_lump bs off (S n) =
       match parse_one bs off,
             parse_lump bs (off + entry_size)%nat n with
       | Some x, Some rest => Some (x :: rest)
       | _, _ => None
       end) ->
    forall bs off count xs,
      parse_lump bs off count = Some xs -> length xs = count.
Proof.
  intros A parse_one entry_size parse_lump Hbase Hstep.
  intros bs off count. revert bs off.
  induction count as [| n IH]; intros bs off xs H.
  - rewrite Hbase in H. inversion H. reflexivity.
  - rewrite Hstep in H.
    destruct (parse_one bs off); try discriminate.
    destruct (parse_lump bs (off + entry_size)%nat n) eqn:Er;
      try discriminate.
    inversion H; subst. simpl. f_equal. eapply IH. exact Er.
Qed.

(** Every fixed-size lump parser returns a list whose length equals
    the requested count, when parsing succeeds. *)

Theorem parse_plane_lump_length : forall bs off count ps,
  parse_plane_lump bs off count = Some ps -> length ps = count.
Proof.
  apply (lump_length_generic parse_bsp_plane bsp_plane_size);
    intros; reflexivity.
Qed.

Theorem parse_vertex_lump_length : forall bs off count vs,
  parse_vertex_lump bs off count = Some vs -> length vs = count.
Proof.
  apply (lump_length_generic parse_bsp_vertex bsp_vertex_size);
    intros; reflexivity.
Qed.

Theorem parse_texture_lump_length : forall bs off count ts,
  parse_texture_lump bs off count = Some ts -> length ts = count.
Proof.
  apply (lump_length_generic parse_bsp_texture bsp_texture_size);
    intros; reflexivity.
Qed.

Theorem parse_node_lump_length : forall bs off count ns,
  parse_node_lump bs off count = Some ns -> length ns = count.
Proof.
  apply (lump_length_generic parse_bsp_node bsp_node_size);
    intros; reflexivity.
Qed.

Theorem parse_leaf_lump_length : forall bs off count ls,
  parse_leaf_lump bs off count = Some ls -> length ls = count.
Proof.
  apply (lump_length_generic parse_bsp_leaf bsp_leaf_size);
    intros; reflexivity.
Qed.

Theorem parse_leaf_face_lump_length : forall bs off count fs,
  parse_leaf_face_lump bs off count = Some fs -> length fs = count.
Proof.
  apply (lump_length_generic parse_bsp_leaf_face bsp_leaf_face_size);
    intros; reflexivity.
Qed.

Theorem parse_brush_lump_length : forall bs off count brs,
  parse_brush_lump bs off count = Some brs -> length brs = count.
Proof.
  apply (lump_length_generic parse_bsp_brush bsp_brush_size);
    intros; reflexivity.
Qed.

Theorem parse_brush_side_lump_length : forall bs off count ss,
  parse_brush_side_lump bs off count = Some ss -> length ss = count.
Proof.
  apply (lump_length_generic parse_bsp_brush_side bsp_brush_side_size);
    intros; reflexivity.
Qed.

Theorem parse_lightmap_lump_length : forall bs off count lms,
  parse_lightmap_lump bs off count = Some lms -> length lms = count.
Proof.
  apply (lump_length_generic parse_bsp_lightmap bsp_lightmap_size);
    intros; reflexivity.
Qed.

Theorem parse_effect_lump_length : forall bs off count es,
  parse_effect_lump bs off count = Some es -> length es = count.
Proof.
  apply (lump_length_generic parse_bsp_effect bsp_effect_size);
    intros; reflexivity.
Qed.

Theorem parse_model_lump_length : forall bs off count ms,
  parse_model_lump bs off count = Some ms -> length ms = count.
Proof.
  apply (lump_length_generic parse_bsp_model bsp_model_size);
    intros; reflexivity.
Qed.

Theorem parse_i32_lump_length : forall bs off count zs,
  parse_i32_lump bs off count = Some zs -> length zs = count.
Proof.
  apply (lump_length_generic (fun b o => get_i32_le b o) 4%nat);
    intros; reflexivity.
Qed.

(* ================================================================== *)
(** * Structural invariants from parsing                                *)
(* ================================================================== *)

(** ** Single-entry invariants *)

(** Parsed texture names are always exactly 64 bytes. *)
Theorem parse_bsp_texture_name_length : forall bs i tx,
  parse_bsp_texture bs i = Some tx ->
  length (tx_name tx) = 64%nat.
Proof.
  intros bs i tx H. unfold parse_bsp_texture in H.
  destruct (take_n bs i 64) eqn:Et; try discriminate.
  destruct (get_i32_le bs (i + 64)%nat); try discriminate.
  destruct (get_i32_le bs (i + 68)%nat); try discriminate.
  inversion H; subst. simpl.
  eapply take_n_length. exact Et.
Qed.

(** Parsed effect names are always exactly 64 bytes. *)
Theorem parse_bsp_effect_name_length : forall bs i fx,
  parse_bsp_effect bs i = Some fx ->
  length (fx_name fx) = 64%nat.
Proof.
  intros bs i fx H. unfold parse_bsp_effect in H.
  destruct (take_n bs i 64) eqn:Et; try discriminate.
  destruct (get_i32_le bs (i + 64)%nat); try discriminate.
  destruct (get_i32_le bs (i + 68)%nat); try discriminate.
  inversion H; subst. simpl.
  eapply take_n_length. exact Et.
Qed.

(** Parsed lightmap data is always exactly 49 152 bytes. *)
Theorem parse_bsp_lightmap_data_length : forall bs i lm,
  parse_bsp_lightmap bs i = Some lm ->
  length (lm_data lm) = 49152%nat.
Proof.
  intros bs i lm H. unfold parse_bsp_lightmap in H.
  destruct (take_n bs i 49152) eqn:Et; try discriminate.
  inversion H; subst. simpl.
  eapply take_n_length. exact Et.
Qed.

(** Parsed vis-data vectors have length equal to the lump's data
    region (total lump length minus the 8-byte header). *)
Theorem parse_vis_data_vecs_length : forall bs off len vd,
  parse_vis_data bs off len = Some vd ->
  length (vis_vecs vd) = (len - 8)%nat.
Proof.
  intros bs off len vd H. unfold parse_vis_data in H.
  destruct (len <? 8)%nat; try discriminate.
  destruct (get_i32_le bs off); try discriminate.
  destruct (get_i32_le bs (off + 4)%nat); try discriminate.
  destruct (take_n bs (off + 8)%nat (len - 8)) eqn:Et;
    try discriminate.
  inversion H; subst. simpl.
  eapply take_n_length. exact Et.
Qed.

(** ** Lump-level invariants *)

(** Every texture in a successfully parsed texture lump has a name
    field of exactly 64 bytes. *)
Theorem parse_texture_lump_names_64 : forall bs off count txs,
  parse_texture_lump bs off count = Some txs ->
  Forall (fun tx => length (tx_name tx) = 64%nat) txs.
Proof.
  intros bs off count. revert bs off.
  induction count as [| n IH]; intros bs off txs H.
  - simpl in H. inversion H; subst. constructor.
  - simpl in H.
    destruct (parse_bsp_texture bs off) eqn:Ep; try discriminate.
    destruct (parse_texture_lump bs (off + bsp_texture_size)%nat n)
      eqn:Er; try discriminate.
    inversion H; subst. constructor.
    + eapply parse_bsp_texture_name_length. exact Ep.
    + eapply IH. exact Er.
Qed.

(** Every effect in a successfully parsed effect lump has a name
    field of exactly 64 bytes. *)
Theorem parse_effect_lump_names_64 : forall bs off count fxs,
  parse_effect_lump bs off count = Some fxs ->
  Forall (fun fx => length (fx_name fx) = 64%nat) fxs.
Proof.
  intros bs off count. revert bs off.
  induction count as [| n IH]; intros bs off fxs H.
  - simpl in H. inversion H; subst. constructor.
  - simpl in H.
    destruct (parse_bsp_effect bs off) eqn:Ep; try discriminate.
    destruct (parse_effect_lump bs (off + bsp_effect_size)%nat n)
      eqn:Er; try discriminate.
    inversion H; subst. constructor.
    + eapply parse_bsp_effect_name_length. exact Ep.
    + eapply IH. exact Er.
Qed.

(** Every lightmap in a successfully parsed lightmap lump has exactly
    49 152 bytes of image data. *)
Theorem parse_lightmap_lump_data_49152 : forall bs off count lms,
  parse_lightmap_lump bs off count = Some lms ->
  Forall (fun lm => length (lm_data lm) = 49152%nat) lms.
Proof.
  intros bs off count. revert bs off.
  induction count as [| n IH]; intros bs off lms H.
  - simpl in H. inversion H; subst. constructor.
  - simpl in H.
    destruct (parse_bsp_lightmap bs off) eqn:Ep; try discriminate.
    destruct (parse_lightmap_lump bs (off + bsp_lightmap_size)%nat n)
      eqn:Er; try discriminate.
    inversion H; subst. constructor.
    + eapply parse_bsp_lightmap_data_length. exact Ep.
    + eapply IH. exact Er.
Qed.

(* ================================================================== *)
(** * Cross-lump consistency predicates                                 *)
(* ================================================================== *)

(** These decidable boolean predicates define what it means for a BSP
    file's inter-lump references to be well-formed.  They are living
    theories: if a valid real-world BSP violates a predicate, we
    adjust the predicate — not the file. *)

(** All node splitting-plane indices reference valid planes. *)
Definition nodes_planes_valid (f : bsp_file) : bool :=
  let np := Z.of_nat (length (bf_planes f)) in
  forallb (fun n =>
    (0 <=? nd_plane n) && (nd_plane n <? np))
    (bf_nodes f).

(** All brush-side plane indices reference valid planes. *)
Definition brush_sides_planes_valid (f : bsp_file) : bool :=
  let np := Z.of_nat (length (bf_planes f)) in
  forallb (fun s =>
    (0 <=? bs_plane_index s) && (bs_plane_index s <? np))
    (bf_brush_sides f).

(** All brush-side texture indices reference valid textures. *)
Definition brush_sides_textures_valid (f : bsp_file) : bool :=
  let nt := Z.of_nat (length (bf_textures f)) in
  forallb (fun s =>
    (0 <=? bs_texture_index s) && (bs_texture_index s <? nt))
    (bf_brush_sides f).

(** All brush texture indices reference valid textures. *)
Definition brushes_textures_valid (f : bsp_file) : bool :=
  let nt := Z.of_nat (length (bf_textures f)) in
  forallb (fun b =>
    (0 <=? br_texture_index b) && (br_texture_index b <? nt))
    (bf_brushes f).

(** All brush side-ranges stay within the brush-sides lump. *)
Definition brushes_sides_valid (f : bsp_file) : bool :=
  let ns := Z.of_nat (length (bf_brush_sides f)) in
  forallb (fun b =>
    (0 <=? br_first_side b) &&
    (0 <=? br_num_sides b) &&
    (br_first_side b + br_num_sides b <=? ns))
    (bf_brushes f).

(** All effect brush indices reference valid brushes. *)
Definition effects_brushes_valid (f : bsp_file) : bool :=
  let nb := Z.of_nat (length (bf_brushes f)) in
  forallb (fun e =>
    (0 <=? fx_brush_index e) && (fx_brush_index e <? nb))
    (bf_effects f).

(** All leaf face-ranges stay within the leaf-faces lump. *)
Definition leaves_faces_valid (f : bsp_file) : bool :=
  let nf := Z.of_nat (length (bf_leaf_faces f)) in
  forallb (fun l =>
    (0 <=? lf_first_leaf_face l) &&
    (0 <=? lf_num_leaf_faces l) &&
    (lf_first_leaf_face l + lf_num_leaf_faces l <=? nf))
    (bf_leaves f).

(** All leaf brush-ranges stay within the leaf-brushes lump. *)
Definition leaves_brushes_valid (f : bsp_file) : bool :=
  let nb := Z.of_nat (length (bf_leaf_brushes f)) in
  forallb (fun l =>
    (0 <=? lf_first_leaf_brush l) &&
    (0 <=? lf_num_leaf_brushes l) &&
    (lf_first_leaf_brush l + lf_num_leaf_brushes l <=? nb))
    (bf_leaves f).

(** All model face-ranges are non-negative. *)
Definition models_faces_valid (f : bsp_file) : bool :=
  forallb (fun m =>
    (0 <=? md_first_face m) && (0 <=? md_num_faces m))
    (bf_models f).

(** All model brush-ranges stay within the brushes lump. *)
Definition models_brushes_valid (f : bsp_file) : bool :=
  let nb := Z.of_nat (length (bf_brushes f)) in
  forallb (fun m =>
    (0 <=? md_first_brush m) &&
    (0 <=? md_num_brushes m) &&
    (md_first_brush m + md_num_brushes m <=? nb))
    (bf_models f).

(** ** Aggregate well-formedness *)

(** A parsed BSP file has well-formed cross-lump references iff every
    individual consistency predicate holds. *)
Definition bsp_cross_lump_valid (f : bsp_file) : bool :=
  nodes_planes_valid f &&
  brush_sides_planes_valid f &&
  brush_sides_textures_valid f &&
  brushes_textures_valid f &&
  brushes_sides_valid f &&
  effects_brushes_valid f &&
  leaves_faces_valid f &&
  leaves_brushes_valid f &&
  models_faces_valid f &&
  models_brushes_valid f.
