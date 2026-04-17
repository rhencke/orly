(** * Bézier patch tessellation for Q3 BSP type-2 faces.

    Q3 BSP patch faces store a grid of control points for bi-quadratic
    Bézier surfaces (3×3 control points per sub-patch).  This module
    tessellates them into triangle meshes, porting the logic previously
    in [docs/patches.js] to Rocq with proofs.

    Quadratic Bernstein basis:
      B₀(t) = (1−t)²    B₁(t) = 2t(1−t)    B₂(t) = t²

    Surface point at (s,t):
      P(s,t) = Σᵢⱼ Bᵢ(s) · Bⱼ(t) · C[j][i]

    All vertex attributes (position, texture coords, lightmap coords,
    color, normal) are interpolated through the same basis so the
    tessellated mesh carries correct data for rendering. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
From Bsp Require Import BspPlaneVertex.
Import ListNotations.
Open Scope Q_scope.

(* ------------------------------------------------------------------ *)
(** ** Bernstein basis functions                                        *)
(* ------------------------------------------------------------------ *)

(** Quadratic Bernstein polynomials evaluated at [t]. *)
Definition bernstein0 (t : Q) : Q := (1 - t) * (1 - t).
Definition bernstein1 (t : Q) : Q := 2 * t * (1 - t).
Definition bernstein2 (t : Q) : Q := t * t.

(** The three quadratic Bernstein polynomials sum to 1 (partition of
    unity).  This guarantees affine invariance: the tessellated surface
    lies within the convex hull of its control points. *)
Lemma bernstein_sum : forall t : Q,
  bernstein0 t + bernstein1 t + bernstein2 t == 1.
Proof.
  intros t. unfold bernstein0, bernstein1, bernstein2. ring.
Qed.

(** Bernstein basis at endpoints. *)
Lemma bernstein_at_0 :
  bernstein0 0 == 1 /\ bernstein1 0 == 0 /\ bernstein2 0 == 0.
Proof. unfold bernstein0, bernstein1, bernstein2. repeat split; ring. Qed.

Lemma bernstein_at_1 :
  bernstein0 1 == 0 /\ bernstein1 1 == 0 /\ bernstein2 1 == 1.
Proof. unfold bernstein0, bernstein1, bernstein2. repeat split; ring. Qed.

(* ------------------------------------------------------------------ *)
(** ** Vertex interpolation                                             *)
(* ------------------------------------------------------------------ *)

(** Weighted sum of two Q values. *)
Definition q_lerp3 (w0 w1 w2 : Q) (a b c : Q) : Q :=
  w0 * a + w1 * b + w2 * c.

(** Weighted sum of two Z-valued colour channels via Q, clamped to
    [0, 255] and rounded to nearest integer. *)
(** Round a rational to the nearest integer (half-up). *)
Definition q_round (q : Q) : Z :=
  let q' := Qred q in
  Z.div (2 * Qnum q' + Zpos (Qden q')) (2 * Zpos (Qden q')).

Definition z_lerp9_clamp (ws : list Q) (vs : list Z) : Z :=
  let raw := fold_left (fun acc p => acc + fst p * inject_Z (snd p))
               (combine ws vs) 0 in
  let rounded := q_round raw in
  Z.max 0 (Z.min 255 rounded).

(** [eval_patch ctrl s t] evaluates the bi-quadratic Bézier surface
    defined by the 3×3 control-point grid [ctrl] (row-major, 9
    elements) at parameter values [(s, t)].

    Each vertex attribute is interpolated independently through the
    tensor-product Bernstein basis.  Returns [None] if [ctrl] does not
    have exactly 9 elements. *)
Definition eval_patch (ctrl : list bsp_vertex) (s t : Q)
    : option bsp_vertex :=
  match ctrl with
  | [c0; c1; c2; c3; c4; c5; c6; c7; c8] =>
      let s0 := bernstein0 s in
      let s1 := bernstein1 s in
      let s2 := bernstein2 s in
      let t0 := bernstein0 t in
      let t1 := bernstein1 t in
      let t2 := bernstein2 t in
      let w00 := s0*t0 in let w10 := s1*t0 in let w20 := s2*t0 in
      let w01 := s0*t1 in let w11 := s1*t1 in let w21 := s2*t1 in
      let w02 := s0*t2 in let w12 := s1*t2 in let w22 := s2*t2 in
      let ws := [w00; w10; w20; w01; w11; w21; w02; w12; w22] in
      let lerp f := fold_left (fun acc p => acc + fst p * snd p)
                      (combine ws (map f ctrl)) 0 in
      let clerp f := z_lerp9_clamp ws (map f ctrl) in
      Some (mk_bsp_vertex
        (lerp vx_pos_x)  (lerp vx_pos_y)  (lerp vx_pos_z)
        (lerp vx_tex_s)  (lerp vx_tex_t)
        (lerp vx_lm_s)   (lerp vx_lm_t)
        (lerp vx_norm_x) (lerp vx_norm_y) (lerp vx_norm_z)
        (clerp vx_color_r) (clerp vx_color_g)
        (clerp vx_color_b) (clerp vx_color_a))
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Grid generation                                                  *)
(* ------------------------------------------------------------------ *)

(** [seq_q n] generates the list [0/n, 1/n, ..., n/n] — that is,
    [n+1] evenly spaced parameter values from 0 to 1 inclusive. *)
Definition seq_q (n : positive) : list Q :=
  map (fun i => inject_Z (Z.of_nat i) / inject_Z (Zpos n))
      (seq 0 (Pos.to_nat n + 1)).

(** [tess_grid ctrl level] tessellates a single 3×3 sub-patch at the
    given level (subdivisions per edge), producing a list of vertices.
    The grid has [(level+1)²] vertices in row-major order.

    Returns [None] if [ctrl] does not have exactly 9 elements. *)
Definition tess_grid (ctrl : list bsp_vertex) (level : positive)
    : option (list bsp_vertex) :=
  let params := seq_q level in
  let verts := flat_map
    (fun t => map (fun s => eval_patch ctrl s t) params) params in
  (* If any eval fails, the whole grid fails *)
  fold_right (fun ov acc =>
    match ov, acc with
    | Some v, Some vs => Some (v :: vs)
    | _, _ => None
    end) (Some []) verts.

(* ------------------------------------------------------------------ *)
(** ** Index generation                                                 *)
(* ------------------------------------------------------------------ *)

(** [tess_indices level base] generates triangle indices for a
    [(level+1)×(level+1)] vertex grid.  Each grid cell yields two
    triangles (CW winding to match Q3 convention).  [base] is added
    to every index so the caller can offset into a combined vertex
    buffer. *)
Definition tess_indices (level : positive) (base : Z) : list Z :=
  let n := Pos.to_nat level in
  let w := Z.of_nat (n + 1) in
  flat_map (fun row =>
    flat_map (fun col =>
      let r := Z.of_nat row in
      let c := Z.of_nat col in
      let tl := (base + r * w + c)%Z in
      let tr := (tl + 1)%Z in
      let bl := (tl + w)%Z in
      let br := (bl + 1)%Z in
      [tl; bl; tr; tr; bl; br]
    ) (seq 0 n)
  ) (seq 0 n).

(* ------------------------------------------------------------------ *)
(** ** Tessellate one sub-patch                                        *)
(* ------------------------------------------------------------------ *)

(** Result of tessellating a single 3×3 sub-patch. *)
Record patch_mesh : Type := mk_patch_mesh
  { pm_vertices : list bsp_vertex
  ; pm_indices  : list Z
  }.

(** [tessellate_subpatch ctrl level base] tessellates a single 3×3
    sub-patch and returns the vertex grid plus offset indices. *)
Definition tessellate_subpatch
    (ctrl : list bsp_vertex) (level : positive) (base : Z)
    : option patch_mesh :=
  match tess_grid ctrl level with
  | Some vs => Some (mk_patch_mesh vs (tess_indices level base))
  | None    => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Extract sub-patch control points                                *)
(* ------------------------------------------------------------------ *)

(** [nth_z ls i] retrieves the element at Z-index [i] from [ls], or
    [None] if out of bounds. *)
Definition nth_z {A : Type} (ls : list A) (i : Z) : option A :=
  if i <? 0 then None
  else nth_error ls (Z.to_nat i).

(** [extract_ctrl verts face_vertex gw px py] extracts the 3×3 control
    points for sub-patch [(px, py)] from the vertex array.  [gw] is
    the patch grid width. *)
Definition extract_ctrl
    (verts : list bsp_vertex) (face_vertex : Z) (gw : Z)
    (px py : Z) : option (list bsp_vertex) :=
  let get r c := nth_z verts ((face_vertex + (py*2 + r) * gw + (px*2 + c))%Z) in
  match get 0%Z 0%Z, get 0%Z 1%Z, get 0%Z 2%Z,
        get 1%Z 0%Z, get 1%Z 1%Z, get 1%Z 2%Z,
        get 2%Z 0%Z, get 2%Z 1%Z, get 2%Z 2%Z with
  | Some c0, Some c1, Some c2,
    Some c3, Some c4, Some c5,
    Some c6, Some c7, Some c8 =>
      Some [c0; c1; c2; c3; c4; c5; c6; c7; c8]
  | _, _, _, _, _, _, _, _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Tessellate all sub-patches of one face                          *)
(* ------------------------------------------------------------------ *)

(** [tess_face_patches verts face level] tessellates all sub-patches
    of one patch face, producing a combined vertex list and index list.
    Indices are offset by [base] (typically the current combined vertex
    buffer length).

    Returns [None] if the face dimensions are invalid or any control
    point is out of bounds.

    Valid patch grids have odd dimensions ≥ 3, yielding
    [(gw−1)/2 × (gh−1)/2] sub-patches. *)
Fixpoint tess_face_helper
    (verts : list bsp_vertex) (face_vertex : Z) (gw : Z)
    (level : positive) (base : Z)
    (patches : list (Z * Z))
    (acc_v : list bsp_vertex) (acc_i : list Z)
    : option (list bsp_vertex * list Z) :=
  match patches with
  | [] => Some (acc_v, acc_i)
  | (px, py) :: rest =>
      match extract_ctrl verts face_vertex gw px py with
      | None => None
      | Some ctrl =>
          match tessellate_subpatch ctrl level (base + Z.of_nat (length acc_v)) with
          | None => None
          | Some pm =>
              tess_face_helper verts face_vertex gw level base rest
                (acc_v ++ pm_vertices pm)
                (acc_i ++ pm_indices pm)
          end
      end
  end.

(** [z_range n] produces [0, 1, ..., n-1] as a list of Z. *)
Definition z_range (n : Z) : list Z :=
  map Z.of_nat (seq 0 (Z.to_nat n)).

(** [cart_product xs ys] produces all (x, y) pairs in row-major order. *)
Definition cart_product (xs ys : list Z) : list (Z * Z) :=
  flat_map (fun y => map (fun x => (x, y)) xs) ys.

(** [tess_face verts face_vertex gw gh level base] tessellates all
    sub-patches of a face with grid dimensions [gw × gh]. *)
Definition tess_face
    (verts : list bsp_vertex) (face_vertex gw gh : Z)
    (level : positive) (base : Z)
    : option (list bsp_vertex * list Z) :=
  (* Valid patch grids: odd dimensions >= 3 *)
  if ((gw <? 3) || (gh <? 3) ||
     (Z.even gw) || (Z.even gh))%Z then None
  else
    let npx := ((gw - 1) / 2)%Z in
    let npy := ((gh - 1) / 2)%Z in
    let patches := cart_product (z_range npx) (z_range npy) in
    tess_face_helper verts face_vertex gw level base patches [] [].

Close Scope Q_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** [seq_q n] always produces exactly [n+1] parameter values. *)
Lemma seq_q_length : forall n,
  length (seq_q n) = (Pos.to_nat n + 1)%nat.
Proof.
  intros n. unfold seq_q. rewrite length_map, length_seq. reflexivity.
Qed.

(** Concrete test: [seq_q 8] has 9 elements (the default
    tessellation level). *)
Lemma seq_q_length_8 : length (seq_q 8) = 9%nat.
Proof. reflexivity. Qed.

(** Concrete test: tessellating level=1 produces 6 indices
    (two triangles). *)
Lemma tess_indices_length_1 :
  length (tess_indices 1 0) = 6%nat.
Proof. reflexivity. Qed.

(** Concrete test: tessellating level=2 produces 24 indices
    (8 triangles, 4 grid cells × 2). *)
Lemma tess_indices_length_2 :
  length (tess_indices 2 0) = 24%nat.
Proof. reflexivity. Qed.

(** Invalid patch dimensions (even width) return [None]. *)
Lemma tess_face_even_width : forall verts fv gh level base,
  tess_face verts fv 4 gh level base = None.
Proof.
  intros. unfold tess_face. simpl.
  destruct (gh <? 3); reflexivity.
Qed.

(** Invalid patch dimensions (too small) return [None]. *)
Lemma tess_face_small_grid : forall verts fv level base,
  tess_face verts fv 1 1 level base = None.
Proof. intros. reflexivity. Qed.

(** Evaluating at (0,0) returns the first control point's
    position (up to Qeq). *)
Lemma eval_patch_origin : forall c0 c1 c2 c3 c4 c5 c6 c7 c8,
  match eval_patch [c0; c1; c2; c3; c4; c5; c6; c7; c8] 0%Q 0%Q with
  | Some v =>
      (vx_pos_x v == vx_pos_x c0)%Q /\
      (vx_pos_y v == vx_pos_y c0)%Q /\
      (vx_pos_z v == vx_pos_z c0)%Q
  | None => False
  end.
Proof.
  intros. simpl.
  repeat split; unfold bernstein0, bernstein1, bernstein2; ring.
Qed.

(** Evaluating at (1,1) returns the last control point's
    position (up to Qeq). *)
Lemma eval_patch_corner : forall c0 c1 c2 c3 c4 c5 c6 c7 c8,
  match eval_patch [c0; c1; c2; c3; c4; c5; c6; c7; c8] 1%Q 1%Q with
  | Some v =>
      (vx_pos_x v == vx_pos_x c8)%Q /\
      (vx_pos_y v == vx_pos_y c8)%Q /\
      (vx_pos_z v == vx_pos_z c8)%Q
  | None => False
  end.
Proof.
  intros. simpl.
  repeat split; unfold bernstein0, bernstein1, bernstein2; ring.
Qed.
