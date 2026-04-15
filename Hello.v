(** * Hello, Coq!

    A minimal Coq program with proof-based verification. *)

Require Import Strings.String.
Open Scope string_scope.

(** A greeting function. *)
Definition hello (name : string) : string :=
  "Hello, " ++ name ++ "!".

(** [hello "world"] produces ["Hello, world!"]. *)
Theorem hello_world : hello "world" = "Hello, world!".
Proof.
  reflexivity.
Qed.
