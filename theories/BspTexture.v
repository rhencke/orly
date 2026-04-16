(** * Q3 BSP texture reference type with lump parser.

    Defines the texture-reference lump of the Q3 BSP format:

    - **Textures lump** (lump index 1): each entry is a texture
      reference with a 64-byte null-terminated name string, a 4-byte
      surface flags field, and a 4-byte contents flags field.
      Entry size: 72 bytes.

    The name field is stored as a fixed-width 64-byte field; unused
    trailing bytes are zero-padded.  Both flags fields are 32-bit
    signed little-endian integers.  Byte offsets follow the Q3 BSP
    specification exactly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Bsp Require Import BspBinary.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Texture reference                                                *)
(* ------------------------------------------------------------------ *)

(** A single entry in the textures lump.

    Field layout (offsets relative to entry start):
    - [tx_name]:     bytes  0– 63  (null-terminated texture path, 64 bytes)
    - [tx_flags]:    bytes 64– 67  (surface flags, i32)
    - [tx_contents]: bytes 68– 71  (content flags, i32) *)
Record bsp_texture : Type := mk_bsp_texture
  { tx_name     : list Z   (** 64 raw bytes; null-terminated texture path *)
  ; tx_flags    : Z        (** surface flags *)
  ; tx_contents : Z        (** content flags *)
  }.

(** Size of one textures-lump entry in bytes (64-byte name + 2 × i32). *)
Definition bsp_texture_size : nat := 72.

(** [take_n bs i n] reads [n] consecutive bytes starting at offset [i],
    returning [None] if the buffer is too short. *)
Fixpoint take_n (bs : bytes) (i : nat) (n : nat) : option (list Z) :=
  match n with
  | O    => Some []
  | S n' =>
      match byte_at bs i, take_n bs (i + 1)%nat n' with
      | Some b, Some rest => Some (b :: rest)
      | _, _              => None
      end
  end.

(** [parse_bsp_texture bs i] reads one 72-byte texture entry from byte
    offset [i] in [bs].  Returns [None] if there are fewer than 72
    bytes available at that offset. *)
Definition parse_bsp_texture (bs : bytes) (i : nat) : option bsp_texture :=
  match take_n bs i 64,
        get_i32_le bs (i + 64)%nat,
        get_i32_le bs (i + 68)%nat with
  | Some name, Some flags, Some contents =>
      Some (mk_bsp_texture name flags contents)
  | _, _, _ => None
  end.

(** [parse_texture_lump bs off count] reads [count] consecutive texture
    entries from byte offset [off] in [bs].  Returns [None] if any
    entry cannot be read. *)
Fixpoint parse_texture_lump (bs : bytes) (off : nat) (count : nat)
    : option (list bsp_texture) :=
  match count with
  | O    => Some []
  | S n  =>
      match parse_bsp_texture bs off,
            parse_texture_lump bs (off + bsp_texture_size)%nat n with
      | Some tx, Some rest => Some (tx :: rest)
      | _, _               => None
      end
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Parsing zero entries always succeeds and returns an empty list. *)
Lemma parse_texture_lump_zero : forall bs off,
  parse_texture_lump bs off 0 = Some [].
Proof. reflexivity. Qed.

(** [bsp_texture_size] is 72. *)
Lemma bsp_texture_size_eq : bsp_texture_size = 72%nat.
Proof. reflexivity. Qed.

(** Seventy-two zero bytes decode as a texture with a zero-filled name
    and flags of 0. *)
Lemma parse_bsp_texture_zeros :
  match parse_bsp_texture
      [0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0; 0;0;0;0; 0;0;0;0;
       0;0;0;0; 0;0;0;0] 0 with
  | Some tx =>
      tx_flags    tx = 0 /\
      tx_contents tx = 0
  | None => False
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** Parsing a buffer that is too short returns [None]. *)
Lemma parse_bsp_texture_too_short :
  parse_bsp_texture [] 0 = None.
Proof. reflexivity. Qed.
