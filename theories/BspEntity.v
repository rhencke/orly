(** * Q3 BSP entity lump parser -- text to typed key-value structures.

    The entity lump (lump index 0) is the only text-based lump in the
    Q3 BSP format.  It contains a null-terminated string of entity
    definitions in a brace-delimited, quoted key-value syntax.

    Example (using single quotes for illustration):

      [open-brace]
      'classname' 'info_player_deathmatch'
      'origin' '0 0 24'
      [close-brace]

    This module defines:
    - [bsp_entity]: a single entity as a list of (key, value) pairs.
    - A character-level scanner that tokenises the raw byte list into
      quoted strings, open/close braces, and whitespace.
    - [parse_entities]: top-level parser from byte list to entity list.

    All characters are [Z] values representing ASCII code points. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Bsp Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Entity type                                                      *)
(* ------------------------------------------------------------------ *)

(** A key-value pair in an entity definition. *)
Definition entity_kv : Type := (list Z * list Z)%type.

(** A single entity is an ordered list of key-value pairs. *)
Definition bsp_entity : Type := list entity_kv.

(* ------------------------------------------------------------------ *)
(** ** ASCII helpers                                                     *)
(* ------------------------------------------------------------------ *)

Definition is_whitespace (c : Z) : bool :=
  (c =? 32)  ||  (* space *)
  (c =? 9)   ||  (* tab *)
  (c =? 10)  ||  (* newline *)
  (c =? 13).     (* carriage return *)

Definition ascii_quote     : Z := 34.  (** double quote *)
Definition ascii_open      : Z := 123. (** open brace *)
Definition ascii_close     : Z := 125. (** close brace *)
Definition ascii_null      : Z := 0.

(* ------------------------------------------------------------------ *)
(** ** Scanner: skip whitespace                                         *)
(* ------------------------------------------------------------------ *)

(** [skip_ws cs] drops leading whitespace and null bytes from [cs]. *)
Fixpoint skip_ws (cs : list Z) : list Z :=
  match cs with
  | c :: rest =>
      if is_whitespace c || (c =? ascii_null) then skip_ws rest
      else cs
  | [] => []
  end.

(* ------------------------------------------------------------------ *)
(** ** Scanner: read a quoted string                                    *)
(* ------------------------------------------------------------------ *)

(** [scan_quoted cs acc fuel] collects characters between double
    quotes.  [cs] begins just after the opening quote.  Returns the
    collected characters (reversed) and the remaining input after the
    closing quote, or [None] if no closing quote is found within
    [fuel] characters. *)
Fixpoint scan_quoted (cs : list Z) (acc : list Z) (fuel : nat)
    : option (list Z * list Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      match cs with
      | [] => None
      | c :: rest =>
          if c =? ascii_quote then Some (rev acc, rest)
          else scan_quoted rest (c :: acc) fuel'
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Scanner: read one key-value pair                                 *)
(* ------------------------------------------------------------------ *)

(** [scan_kv cs fuel] reads one key-value pair — two consecutive
    quoted strings separated by whitespace.  Returns the pair and
    remaining input, or [None] on parse failure. *)
Definition scan_kv (cs : list Z) (fuel : nat)
    : option (entity_kv * list Z) :=
  let cs1 := skip_ws cs in
  match cs1 with
  | c :: rest =>
      if c =? ascii_quote then
        match scan_quoted rest [] fuel with
        | Some (key, cs2) =>
            let cs3 := skip_ws cs2 in
            match cs3 with
            | c2 :: rest2 =>
                if c2 =? ascii_quote then
                  match scan_quoted rest2 [] fuel with
                  | Some (val, cs4) => Some ((key, val), cs4)
                  | None => None
                  end
                else None
            | [] => None
            end
        | None => None
        end
      else None
  | [] => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Scanner: read key-value pairs until closing brace               *)
(* ------------------------------------------------------------------ *)

(** [scan_kvs cs acc fuel] reads key-value pairs from [cs] until a
    closing brace [}] is found.  Returns the pairs (in order) and the
    remaining input after the brace. *)
Fixpoint scan_kvs (cs : list Z) (acc : list entity_kv) (fuel : nat)
    : option (list entity_kv * list Z) :=
  match fuel with
  | O => None
  | S fuel' =>
      let cs1 := skip_ws cs in
      match cs1 with
      | [] => None
      | c :: rest =>
          if c =? ascii_close then Some (rev acc, rest)
          else
            match scan_kv cs1 fuel' with
            | Some (kv, cs2) => scan_kvs cs2 (kv :: acc) fuel'
            | None => None
            end
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Top-level entity parser                                          *)
(* ------------------------------------------------------------------ *)

(** [scan_entities cs acc fuel] reads a sequence of brace-delimited
    entity blocks from [cs].  Returns the list of entities when the
    input is exhausted (modulo trailing whitespace/nulls). *)
Fixpoint scan_entities (cs : list Z) (acc : list bsp_entity) (fuel : nat)
    : option (list bsp_entity) :=
  match fuel with
  | O => None
  | S fuel' =>
      let cs1 := skip_ws cs in
      match cs1 with
      | [] => Some (rev acc)
      | c :: rest =>
          if c =? ascii_open then
            match scan_kvs rest [] fuel' with
            | Some (kvs, cs2) => scan_entities cs2 (kvs :: acc) fuel'
            | None => None
            end
          else None
      end
  end.

(** [parse_entities cs] parses the entity lump byte list [cs] into a
    list of entities.  The fuel parameter is set to the length of the
    input — each scanner step consumes at least one byte, so this is
    always sufficient. *)
Definition parse_entities (cs : list Z) : option (list bsp_entity) :=
  scan_entities cs [] (S (length cs)).

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** An empty input parses to an empty entity list. *)
Lemma parse_entities_empty :
  parse_entities [] = Some [].
Proof. reflexivity. Qed.

(** Whitespace-only input parses to an empty entity list. *)
Lemma parse_entities_whitespace :
  parse_entities [32; 10; 13; 9] = Some [].
Proof. reflexivity. Qed.

(** A null byte (common trailing byte in BSP entity lumps) parses to
    an empty entity list. *)
Lemma parse_entities_null :
  parse_entities [0] = Some [].
Proof. reflexivity. Qed.

(** A single entity with one key-value pair. *)
Lemma parse_entities_single :
  parse_entities
    [123; 10;                        (* { \n *)
     34; 107; 34; 32; 34; 118; 34;  (* "k" "v" *)
     10; 125; 10]                    (* \n } \n *)
  = Some [[(  [107], [118]  )]].
Proof. vm_compute. reflexivity. Qed.

(** Two entities parse correctly. *)
Lemma parse_entities_two :
  parse_entities
    [123; 10; 34; 97; 34; 32; 34; 98; 34; 10; 125; 10;   (* { "a" "b" } *)
     123; 10; 34; 99; 34; 32; 34; 100; 34; 10; 125; 10]  (* { "c" "d" } *)
  = Some [  [([97], [98])]  ;  [([99], [100])]  ].
Proof. vm_compute. reflexivity. Qed.

(** An unclosed brace returns [None]. *)
Lemma parse_entities_unclosed :
  parse_entities [123; 10] = None.
Proof. vm_compute. reflexivity. Qed.

(** An unclosed quote returns [None]. *)
Lemma parse_entities_unclosed_quote :
  parse_entities [123; 10; 34; 97; 10; 125] = None.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** Key-value lookup                                                 *)
(* ------------------------------------------------------------------ *)

(** Equality test for [list Z] (byte-string comparison). *)
Fixpoint list_Z_eqb (xs ys : list Z) : bool :=
  match xs, ys with
  | [], []             => true
  | x :: xs', y :: ys' => (x =? y) && list_Z_eqb xs' ys'
  | _, _               => false
  end.

(** [entity_get_val e key] returns the value associated with [key] in
    entity [e], or [None] if the key is absent. *)
Fixpoint entity_get_val (e : bsp_entity) (key : list Z) : option (list Z) :=
  match e with
  | []             => None
  | (k, v) :: rest =>
      if list_Z_eqb k key then Some v
      else entity_get_val rest key
  end.

(* ------------------------------------------------------------------ *)
(** ** Named key and value constants                                    *)
(* ------------------------------------------------------------------ *)

(** ASCII encoding of the string "classname". *)
Definition key_classname : list Z :=
  [99; 108; 97; 115; 115; 110; 97; 109; 101].

(** ASCII encoding of "info_player_deathmatch". *)
Definition val_info_player_deathmatch : list Z :=
  [105; 110; 102; 111; 95; 112; 108; 97; 121; 101; 114; 95;
   100; 101; 97; 116; 104; 109; 97; 116; 99; 104].

(** ASCII encoding of "origin". *)
Definition key_origin : list Z :=
  [111; 114; 105; 103; 105; 110].

(** ASCII encoding of "angle". *)
Definition key_angle : list Z :=
  [97; 110; 103; 108; 101].

(** ASCII encoding of "model". *)
Definition key_model : list Z :=
  [109; 111; 100; 101; 108].

(** ASCII encoding of "target". *)
Definition key_target : list Z :=
  [116; 97; 114; 103; 101; 116].

(** ASCII encoding of "targetname". *)
Definition key_targetname : list Z :=
  [116; 97; 114; 103; 101; 116; 110; 97; 109; 101].

(** ASCII encoding of "trigger_push". *)
Definition val_trigger_push : list Z :=
  [116; 114; 105; 103; 103; 101; 114; 95; 112; 117; 115; 104].

(** ASCII encoding of "target_position". *)
Definition val_target_position : list Z :=
  [116; 97; 114; 103; 101; 116; 95; 112; 111; 115; 105; 116; 105; 111; 110].

(* ------------------------------------------------------------------ *)
(** ** Integer value parser                                             *)
(* ------------------------------------------------------------------ *)

Definition ascii_minus : Z := 45.   (** '-' *)
Definition ascii_space : Z := 32.   (** ' ' *)
Definition ascii_star  : Z := 42.   (** '*' *)

(** True iff [c] is an ASCII decimal digit. *)
Definition is_digit (c : Z) : bool := (48 <=? c) && (c <=? 57).

(** Scan decimal digits from [cs], accumulating the value in [acc].
    [fuel] bounds recursion; passing [length cs] is always sufficient,
    since each step consumes one byte. *)
Fixpoint scan_digits (cs : list Z) (acc : Z) (fuel : nat)
    : (Z * list Z) :=
  match fuel with
  | O      => (acc, cs)
  | S fuel' =>
      match cs with
      | c :: rest =>
          if is_digit c
          then scan_digits rest (acc * 10 + (c - 48)) fuel'
          else (acc, cs)
      | [] => (acc, [])
      end
  end.

(** Parse a signed decimal integer from the front of [cs].
    Returns [(value, remainder)] or [None] if [cs] does not begin with
    a digit or with '-' followed by a digit. *)
Definition parse_int (cs : list Z) : option (Z * list Z) :=
  match cs with
  | [] => None
  | c :: rest =>
      if c =? ascii_minus then
        match rest with
        | d :: _ =>
            if is_digit d
            then let (n, tail) := scan_digits rest 0 (length rest) in
                 Some (- n, tail)
            else None
        | [] => None
        end
      else if is_digit c
           then let (n, tail) := scan_digits cs 0 (length cs) in
                Some (n, tail)
           else None
  end.

(** Parse an inline BSP submodel reference of the form ["*N"].
    Returns [Some N] iff the string begins with ['*'], the remainder
    parses as a decimal integer, the parse consumes the full string,
    and [N] is non-negative. *)
Definition parse_inline_model_ref (cs : list Z) : option Z :=
  match cs with
  | c :: rest =>
      if c =? ascii_star then
        match parse_int rest with
        | Some (n, []) => if n <? 0 then None else Some n
        | _            => None
        end
      else None
  | [] => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas for lookup and parsing                        *)
(* ------------------------------------------------------------------ *)

(** [list_Z_eqb] is reflexive. *)
Lemma list_Z_eqb_refl : forall xs, list_Z_eqb xs xs = true.
Proof.
  induction xs as [| x xs' IH]; simpl.
  - reflexivity.
  - rewrite Z.eqb_refl. simpl. exact IH.
Qed.

(** Matching key at the head of an entity returns that key's value. *)
Lemma entity_get_val_head : forall k v rest,
  entity_get_val ((k, v) :: rest) k = Some v.
Proof.
  intros k v rest. simpl. rewrite list_Z_eqb_refl. reflexivity.
Qed.

(** Empty entity list has no keys. *)
Lemma entity_get_val_nil : forall key,
  entity_get_val [] key = None.
Proof. reflexivity. Qed.

(** Empty input gives [None]. *)
Lemma parse_int_none_empty : parse_int [] = None.
Proof. reflexivity. Qed.

(** Bare minus gives [None]. *)
Lemma parse_int_none_minus_only : parse_int [45] = None.
Proof. vm_compute. reflexivity. Qed.

(** Single zero digit parses to 0. *)
Lemma parse_int_zero : parse_int [48] = Some (0, []).
Proof. vm_compute. reflexivity. Qed.

(** Two-digit positive integer. *)
Lemma parse_int_pos_42 : parse_int [52; 50] = Some (42, []).
Proof. vm_compute. reflexivity. Qed.

(** Negative integer. *)
Lemma parse_int_neg_1 : parse_int [45; 49] = Some (-1, []).
Proof. vm_compute. reflexivity. Qed.

(** A well-formed inline model reference parses successfully. *)
Lemma parse_inline_model_ref_pos :
  parse_inline_model_ref [42; 49; 50] = Some 12.
Proof. vm_compute. reflexivity. Qed.

(** Negative inline model references are rejected. *)
Lemma parse_inline_model_ref_neg :
  parse_inline_model_ref [42; 45; 49] = None.
Proof. vm_compute. reflexivity. Qed.

(** Missing the leading ['*'] is not a valid inline model reference. *)
Lemma parse_inline_model_ref_missing_star :
  parse_inline_model_ref [49; 50] = None.
Proof. vm_compute. reflexivity. Qed.
