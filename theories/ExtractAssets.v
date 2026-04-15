(** * Asset extraction logic for q3dm1.

    Pure specification of the manifest, file-matching, path-safety,
    and validation logic.  Extracted to OCaml and linked into the
    native [extract_assets] binary — I/O stays in the OCaml driver. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.
From Stdlib Require Import PeanoNat.
Import ListNotations.
Open Scope string_scope.

(* ------------------------------------------------------------------ *)
(** ** String helpers                                                   *)
(* ------------------------------------------------------------------ *)

(** Case-insensitive comparison needs lowercase conversion. *)
Definition lowercase_ascii (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if (Nat.leb 65 n && Nat.leb n 90)%bool
  then ascii_of_nat (n + 32)
  else c.

Fixpoint lowercase (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c rest => String (lowercase_ascii c) (lowercase rest)
  end.

(** [prefix p s] returns [true] when [p] is a prefix of [s]. *)
Fixpoint prefix (p s : string) : bool :=
  match p with
  | EmptyString => true
  | String cp rest_p =>
    match s with
    | EmptyString => false
    | String cs rest_s =>
      if Ascii.eqb cp cs then prefix rest_p rest_s else false
    end
  end.

(** [contains_substring needle haystack] — naive but correct. *)
Fixpoint contains_substring (needle haystack : string) : bool :=
  if prefix needle haystack then true
  else
    match haystack with
    | EmptyString => false
    | String _ rest => contains_substring needle rest
    end.

(** [ends_with suffix s] — [true] when [s] ends with [suffix]. *)
Definition ends_with (suffix s : string) : bool :=
  let suf_len := String.length suffix in
  let s_len := String.length s in
  if (s_len <? suf_len)%nat then false
  else String.eqb (substring (s_len - suf_len) suf_len s) suffix.

(* ------------------------------------------------------------------ *)
(** ** Manifest                                                        *)
(* ------------------------------------------------------------------ *)

(** Individual files required after extraction. *)
Definition required_files : list string :=
  [ "maps/q3dm1.bsp"
  ; "maps/q3dm1.aas"
  ; "levelshots/q3dm1.jpg"
  ; "scripts/shaderlist.txt"
  ; "scripts/base_floor.shader"
  ; "scripts/base_wall.shader"
  ; "scripts/base_trim.shader"
  ; "scripts/base_support.shader"
  ; "scripts/base_light.shader"
  ; "scripts/base_object.shader"
  ; "scripts/gothic_light.shader"
  ; "scripts/gothic_floor.shader"
  ; "scripts/gothic_wall.shader"
  ; "scripts/gothic_block.shader"
  ; "scripts/common.shader"
  ; "scripts/liquids.shader"
  ; "scripts/skies.shader"
  ].

(** Directory prefixes — every file under each prefix is extracted. *)
Definition required_prefixes : list string :=
  [ "textures/base_floor/"
  ; "textures/base_wall/"
  ; "textures/base_trim/"
  ; "textures/base_support/"
  ; "textures/base_light/"
  ; "textures/base_object/"
  ; "textures/gothic_light/"
  ; "textures/gothic_floor/"
  ; "textures/gothic_wall/"
  ; "textures/gothic_block/"
  ; "textures/skies/"
  ; "textures/liquids/"
  ; "textures/liquids2/"
  ; "models/mapobjects/"
  ].

(* ------------------------------------------------------------------ *)
(** ** Core predicates                                                 *)
(* ------------------------------------------------------------------ *)

(** [wanted name] returns [true] when [name] should be extracted.
    Comparison is case-insensitive (matching the Python original). *)
Definition wanted (name : string) : bool :=
  let low := lowercase name in
  existsb (fun f => String.eqb low (lowercase f)) required_files
  || existsb (fun p => prefix (lowercase p) low) required_prefixes.

(** Path-traversal guard.  Rejects any path containing a [..]
    component (i.e. the substring [/../], or starting with [../],
    or ending with [/..], or being exactly [..]). *)
Definition safe_path (name : string) : bool :=
  negb (  contains_substring "/../" name
       || prefix "../" name
       || ends_with "/.." name
       || String.eqb name ".." ).

(** Manifest validation: every required file appears in the list of
    extracted (lowercased) paths, and every required prefix has at
    least one matching extracted path. *)
Definition validate_manifest (extracted_lc : list string) : bool :=
  forallb (fun f =>
    existsb (String.eqb (lowercase f)) extracted_lc
  ) required_files
  &&
  forallb (fun p =>
    existsb (fun e => prefix (lowercase p) e) extracted_lc
  ) required_prefixes.

(** Which required files are missing? Useful for diagnostics. *)
Definition missing_files (extracted_lc : list string) : list string :=
  filter (fun f =>
    negb (existsb (String.eqb (lowercase f)) extracted_lc)
  ) required_files.

(** Which required prefixes have no coverage? *)
Definition missing_prefixes (extracted_lc : list string) : list string :=
  filter (fun p =>
    negb (existsb (fun e => prefix (lowercase p) e) extracted_lc)
  ) required_prefixes.

(* ------------------------------------------------------------------ *)
(** ** Proofs                                                          *)
(* ------------------------------------------------------------------ *)

(** Every entry in [required_files] is accepted by [wanted]. *)
Theorem wanted_accepts_required_files :
  forallb wanted required_files = true.
Proof. reflexivity. Qed.

(** [safe_path] rejects a classic traversal attack. *)
Theorem safe_path_rejects_traversal :
  safe_path "textures/../../../etc/passwd" = false.
Proof. reflexivity. Qed.

(** [safe_path] accepts a normal manifest entry. *)
Theorem safe_path_accepts_normal :
  safe_path "maps/q3dm1.bsp" = true.
Proof. reflexivity. Qed.

(** The manifest itself is entirely safe paths. *)
Theorem required_files_are_safe :
  forallb safe_path required_files = true.
Proof. reflexivity. Qed.

Theorem required_prefixes_are_safe :
  forallb safe_path required_prefixes = true.
Proof. reflexivity. Qed.

(** [validate_manifest] returns [true] when given the required files
    plus at least one entry per required prefix. *)
Theorem validate_manifest_covers_files :
  validate_manifest
    (map lowercase required_files ++
     [ "textures/base_floor/x.jpg"
     ; "textures/base_wall/x.jpg"
     ; "textures/base_trim/x.jpg"
     ; "textures/base_support/x.jpg"
     ; "textures/base_light/x.jpg"
     ; "textures/base_object/x.jpg"
     ; "textures/gothic_light/x.jpg"
     ; "textures/gothic_floor/x.jpg"
     ; "textures/gothic_wall/x.jpg"
     ; "textures/gothic_block/x.jpg"
     ; "textures/skies/x.jpg"
     ; "textures/liquids/x.jpg"
     ; "textures/liquids2/x.jpg"
     ; "models/mapobjects/x.md3"
     ]) = true.
Proof. reflexivity. Qed.

(** An empty extraction fails validation. *)
Theorem validate_manifest_empty_fails :
  validate_manifest [] = false.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Extraction to OCaml                                             *)
(* ------------------------------------------------------------------ *)

Require Extraction.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.

Set Extraction Output Directory "extract_assets".
Extraction "extract_assets_core.ml"
  wanted safe_path validate_manifest
  missing_files missing_prefixes
  required_files required_prefixes.
