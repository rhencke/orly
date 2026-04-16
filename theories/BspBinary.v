(** * Binary parsing primitives for the Q3 BSP loader.

    Little-endian integer and IEEE 754 single-precision float readers
    over a flat byte sequence.  All functions return [option] so callers
    can propagate parse failures without exceptions.

    These primitives are the only code that touches raw bytes; all lump
    parsers call these and never index into [bytes] directly. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import QArith.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Byte sequences                                                   *)
(* ------------------------------------------------------------------ *)

(** Raw BSP input is a flat [list Z], one element per byte, each in
    [[0, 255]].  [Z] is used so arithmetic never requires numeric coercions. *)
Definition bytes := list Z.

(** [byte_at bs i] retrieves the byte at index [i], or [None]. *)
Definition byte_at (bs : bytes) (i : nat) : option Z :=
  nth_error bs i.

(** [take4 bs i] retrieves four consecutive bytes starting at [i],
    or [None] if the sequence is too short. *)
Definition take4 (bs : bytes) (i : nat) : option (Z * Z * Z * Z) :=
  match byte_at bs i,           byte_at bs (i + 1)%nat,
        byte_at bs (i + 2)%nat, byte_at bs (i + 3)%nat with
  | Some b0, Some b1, Some b2, Some b3 => Some (b0, b1, b2, b3)
  | _, _, _, _ => None
  end.

(* ------------------------------------------------------------------ *)
(** ** Unsigned integer readers                                         *)
(* ------------------------------------------------------------------ *)

Definition get_u8 (bs : bytes) (i : nat) : option Z :=
  byte_at bs i.

(** [get_u16_le bs i] reads an unsigned 16-bit little-endian value. *)
Definition get_u16_le (bs : bytes) (i : nat) : option Z :=
  match byte_at bs i, byte_at bs (i + 1)%nat with
  | Some b0, Some b1 => Some (b0 + b1 * 256)
  | _, _ => None
  end.

(** [get_u32_le bs i] reads an unsigned 32-bit little-endian value. *)
Definition get_u32_le (bs : bytes) (i : nat) : option Z :=
  match take4 bs i with
  | None => None
  | Some (b0, b1, b2, b3) => Some (b0 + b1 * 256 + b2 * 65536 + b3 * 16777216)
  end.

(* ------------------------------------------------------------------ *)
(** ** Signed integer readers                                           *)
(* ------------------------------------------------------------------ *)

(** Two's-complement conversion for 16-bit values: if the unsigned
    value has bit 15 set, subtract [2^16] to recover the signed value. *)
Definition to_i16 (u : Z) : Z :=
  if 32768 <=? u then u - 65536 else u.

(** [get_i16_le bs i] reads a signed 16-bit little-endian value. *)
Definition get_i16_le (bs : bytes) (i : nat) : option Z :=
  match get_u16_le bs i with
  | None   => None
  | Some u => Some (to_i16 u)
  end.

(** Two's-complement: if the unsigned value has bit 31 set,
    subtract [2^32] to recover the signed value. *)
Definition to_i32 (u : Z) : Z :=
  if 2147483648 <=? u then u - 4294967296 else u.

(** [get_i32_le bs i] reads a signed 32-bit little-endian value.
    This is the most common integer type in the Q3 BSP format. *)
Definition get_i32_le (bs : bytes) (i : nat) : option Z :=
  match get_u32_le bs i with
  | None   => None
  | Some u => Some (to_i32 u)
  end.

(* ------------------------------------------------------------------ *)
(** ** IEEE 754 single-precision float reader                           *)
(* ------------------------------------------------------------------ *)

(** [q_pow2 n] returns the rational [2^n].
    For negative [n] this is the fraction [1 / 2^|n|]. *)
Definition q_pow2 (n : Z) : Q :=
  if 0 <=? n
  then inject_Z (2 ^ n)
  else Qmake 1 (Z.to_pos (2 ^ (- n))).

(** [decode_f32_bits u] decodes a raw 32-bit IEEE 754 binary32 bit
    pattern [u] to an exact rational value.

    - Exponent field = 255 (infinities, NaNs): mapped to [0].  Valid
      BSP geometry never contains non-finite coordinate values.
    - Exponent field = 0 (subnormals): handled correctly.
    - All other exponents: normal path. *)
Definition decode_f32_bits (u : Z) : Q :=
  let sign    := if Z.shiftr u 31 =? 0 then inject_Z 1 else inject_Z (-1) in
  let exp_raw := Z.land (Z.shiftr u 23) 0xFF in
  let mant    := Z.land u 0x7FFFFF in
  if exp_raw =? 255 then
    inject_Z 0
  else if exp_raw =? 0 then
    (* subnormal: (-1)^s × mant × 2^(−149) *)
    Qmult sign (Qmult (inject_Z mant) (q_pow2 (-149)))
  else
    (* normal: (-1)^s × (2^23 + mant) × 2^(exp_raw − 150) *)
    Qmult sign (Qmult (inject_Z (2 ^ 23 + mant)) (q_pow2 (exp_raw - 150))).

(** [get_f32_le bs i] reads four bytes at offset [i] as a little-endian
    IEEE 754 binary32 float, returned as an exact rational. *)
Definition get_f32_le (bs : bytes) (i : nat) : option Q :=
  match get_u32_le bs i with
  | None   => None
  | Some u => Some (decode_f32_bits u)
  end.

(* ------------------------------------------------------------------ *)
(** ** Correctness lemmas                                               *)
(* ------------------------------------------------------------------ *)

(** Byte reads from a singleton list succeed. *)
Lemma get_u8_singleton : forall b,
  get_u8 [b] 0 = Some b.
Proof. reflexivity. Qed.

(** Two zero bytes decode as signed 0. *)
Lemma get_i16_le_zero :
  get_i16_le [0; 0] 0 = Some 0.
Proof. reflexivity. Qed.

(** All-ones bytes are [−1] in 16-bit two's complement. *)
Lemma get_i16_le_minus_one :
  get_i16_le [255; 255] 0 = Some (-1).
Proof. reflexivity. Qed.

(** Four zero bytes decode as [0]. *)
Lemma get_i32_le_zero :
  get_i32_le [0; 0; 0; 0] 0 = Some 0.
Proof. reflexivity. Qed.

(** Little-endian byte order: the first byte is least significant. *)
Lemma get_i32_le_one :
  get_i32_le [1; 0; 0; 0] 0 = Some 1.
Proof. reflexivity. Qed.

(** All-ones bytes are [−1] in two's complement. *)
Lemma get_i32_le_minus_one :
  get_i32_le [255; 255; 255; 255] 0 = Some (-1).
Proof. reflexivity. Qed.

(** [0x3F800000] is the IEEE 754 binary32 encoding of [1.0]. *)
Lemma decode_f32_one :
  (decode_f32_bits 0x3F800000 == 1)%Q.
Proof. vm_compute. reflexivity. Qed.

(** [0x00000000] encodes [0.0]. *)
Lemma decode_f32_zero :
  (decode_f32_bits 0 == 0)%Q.
Proof. vm_compute. reflexivity. Qed.

(** [0xBF800000] encodes [−1.0]. *)
Lemma decode_f32_neg_one :
  (decode_f32_bits 0xBF800000 == -1)%Q.
Proof. vm_compute. reflexivity. Qed.
