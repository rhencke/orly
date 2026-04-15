(** * Extract Assets — Rocq specification for the pak0.pk3 asset manifest.

    This module defines the manifest of required Quake 3 Arena Demo assets
    and the [wanted_lc] predicate used to select entries from pak0.pk3 during
    extraction.  The predicate is proved correct with respect to the manifest:
    every required file and prefix is recognised by [wanted_lc].

    [wanted_lc] assumes its argument has already been lowercased by the caller.

    The module is extracted to OCaml for use by the build-time asset extraction
    tool ([extract_assets/main.ml]).  Logic changes here flow through to the
    binary automatically — no parallel edits needed. *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ExtrOcamlNativeString.

Import ListNotations.
Open Scope string_scope.

(* ---------------------------------------------------------------------------
   Asset manifest
   --------------------------------------------------------------------------- *)

(** Individual files that must be present after extraction (all lowercase). *)
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

(** Directory prefixes — every file found under each prefix is extracted,
    and at least one file must be present per prefix (all lowercase). *)
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

(* ---------------------------------------------------------------------------
   Wanted predicate
   --------------------------------------------------------------------------- *)

(** Return [true] if a pak0.pk3 entry should be extracted.
    [name] must already be lowercased by the OCaml caller. *)
Definition wanted_lc (name : string) : bool :=
  existsb (String.eqb name) required_files
  || existsb (fun pre => String.prefix pre name) required_prefixes.

(* ---------------------------------------------------------------------------
   Manifest proofs
   --------------------------------------------------------------------------- *)

Theorem required_files_nonempty : required_files <> [].
Proof. discriminate. Qed.

Theorem required_prefixes_nonempty : required_prefixes <> [].
Proof. discriminate. Qed.

(** Every entry in [required_files] is recognised by [wanted_lc]. *)
Theorem required_files_wanted :
  Forall (fun f => wanted_lc f = true) required_files.
Proof.
  unfold wanted_lc, required_files.
  repeat constructor; vm_compute; reflexivity.
Qed.

(** Every required prefix is itself recognised by [wanted_lc] (since a string
    is always a prefix of itself). *)
Theorem required_prefixes_wanted :
  Forall (fun pre => wanted_lc pre = true) required_prefixes.
Proof.
  unfold wanted_lc, required_prefixes.
  repeat constructor; vm_compute; reflexivity.
Qed.

(* ---------------------------------------------------------------------------
   OCaml extraction
   --------------------------------------------------------------------------- *)

Require Extraction.
Extraction Language OCaml.
Set Extraction Output Directory ".".
Extraction "extract_assets/extract_assets_core"
  wanted_lc required_files required_prefixes.
