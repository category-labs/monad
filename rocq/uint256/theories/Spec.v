(** * High-Level Specifications for uint256 Operations

    This file defines the mathematical specifications for 256-bit unsigned
    integer operations. All operations are defined over Z (arbitrary-precision
    integers) with modular arithmetic mod 2^256.

    The goal is to prove that the low-level implementation in uint256.hpp
    correctly implements these specifications.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

(** ** Constants *)

(** The modulus for 256-bit arithmetic *)
Definition modulus : Z := 2^256.

(** Maximum value representable in 256 bits *)
Definition max_uint256 : Z := modulus - 1.

(** ** Type Definitions *)

(** Abstract our representation of 256-bit integers.  We avoid
    complications with sigma types by just using integers directly. *)
Definition uint256 : Type := Z.

(** Extract the Z value from a uint256 *)
Definition to_Z (x : uint256) : Z := x.

(** Convert a Z to uint256 *)
Definition from_Z (z : Z) : uint256 := z.

(** Normalization: ensure a Z is in the uint256 range *)
Definition normalize256 (z : Z) : Z := z mod modulus.

(** ** Result Types *)

(** Result of an operation that can produce a carry/borrow bit *)
Record result_with_carry := {
  value : uint256;
  carry : bool
}.

(** Result of division: quotient and remainder *)
Record div_result := {
  quot : uint256;
  rem : uint256
}.

(** ** Arithmetic Specifications *)

(** Addition modulo 2^256 *)
Definition add_spec (x y : uint256) : uint256 := normalize256 (x + y).

(** Addition with carry output *)
Definition addc_spec (x y : uint256) : result_with_carry := {|
  value := normalize256 (x + y);
  carry := (x + y >=? modulus)
|}.
(** NB: Update these specifications...
    ***********************************

(** Subtraction modulo 2^256 *)
Definition sub_spec (x y : uint256) : uint256 :=
  from_Z (to_Z x - to_Z y).

(** Subtraction with borrow output *)
Definition subb_spec (x y : uint256) : result_with_carry := {|
  value := from_Z (to_Z x - to_Z y);
  carry := (to_Z x <? to_Z y)  (* borrow *)
|}.

(** Multiplication modulo 2^256 *)
Definition mul_spec (x y : uint256) : uint256 :=
  from_Z (to_Z x * to_Z y).

(** Division with remainder *)
Definition udivrem_spec (x y : uint256) : div_result := {|
  quot := from_Z (to_Z x / to_Z y);
  rem := from_Z (to_Z x mod to_Z y)
|}.

(** Division *)
Definition div_spec (x y : uint256) : uint256 :=
  from_Z (to_Z x / to_Z y).

(** Modulo *)
Definition mod_spec (x y : uint256) : uint256 :=
  from_Z (to_Z x mod to_Z y).

(** Negation modulo 2^256 *)
Definition neg_spec (x : uint256) : uint256 :=
  from_Z (- to_Z x).

(** ** Modular Arithmetic Specifications *)

(** Addition modulo m *)
Definition addmod_spec (x y m : uint256) : uint256 :=
  if (to_Z m =? 0) then from_Z 0
  else from_Z ((to_Z x + to_Z y) mod to_Z m).

(** Multiplication modulo m *)
Definition mulmod_spec (x y m : uint256) : uint256 :=
  if (to_Z m =? 0) then from_Z 0
  else from_Z ((to_Z x * to_Z y) mod to_Z m).

(** ** Comparison Specifications *)

(** Unsigned less than *)
Definition lt_spec (x y : uint256) : bool :=
  (to_Z x <? to_Z y).

(** Unsigned less than or equal *)
Definition le_spec (x y : uint256) : bool :=
  (to_Z x <=? to_Z y).

(** Unsigned greater than *)
Definition gt_spec (x y : uint256) : bool :=
  (to_Z x >? to_Z y).

(** Unsigned greater than or equal *)
Definition ge_spec (x y : uint256) : bool :=
  (to_Z x >=? to_Z y).

(** Equality *)
Definition eq_spec (x y : uint256) : bool :=
  (to_Z x =? to_Z y).

(** Signed less than (interprets values as two's complement) *)
Definition slt_spec (x y : uint256) : bool :=
  let x_signed := if (to_Z x <? 2^255) then to_Z x else to_Z x - modulus in
  let y_signed := if (to_Z y <? 2^255) then to_Z y else to_Z y - modulus in
  (x_signed <? y_signed).

(** ** Bitwise Operation Specifications *)

(** Bitwise AND *)
Definition and_spec (x y : uint256) : uint256 :=
  from_Z (Z.land (to_Z x) (to_Z y)).

(** Bitwise OR *)
Definition or_spec (x y : uint256) : uint256 :=
  from_Z (Z.lor (to_Z x) (to_Z y)).

(** Bitwise XOR *)
Definition xor_spec (x y : uint256) : uint256 :=
  from_Z (Z.lxor (to_Z x) (to_Z y)).

(** Bitwise NOT *)
Definition not_spec (x : uint256) : uint256 :=
  from_Z (Z.lnot (to_Z x)).

(** ** Shift Operation Specifications *)

(** Left shift *)
Definition shl_spec (x shift : uint256) : uint256 :=
  if (to_Z shift >=? 256) then from_Z 0
  else from_Z (Z.shiftl (to_Z x) (to_Z shift)).

(** Logical right shift *)
Definition shr_spec (x shift : uint256) : uint256 :=
  if (to_Z shift >=? 256) then from_Z 0
  else from_Z (Z.shiftr (to_Z x) (to_Z shift)).

(** Arithmetic right shift (sign-extending) *)
Definition sar_spec (x shift : uint256) : uint256 :=
  let x_signed := if (to_Z x <? 2^255) then to_Z x else to_Z x - modulus in
  let shift_amt := if (to_Z shift >=? 256) then 256 else to_Z shift in
  let result := x_signed / (2^shift_amt) in
  from_Z result.

(** ** Special Operation Specifications *)

(** Exponentiation modulo 2^256 *)
Fixpoint exp_spec_aux (base : uint256) (exp : nat) : uint256 :=
  match exp with
  | O => from_Z 1
  | S n => mul_spec base (exp_spec_aux base n)
  end.

Definition exp_spec (base exp : uint256) : uint256 :=
  (* Convert exponent to nat - this is safe since exp < 2^256 *)
  exp_spec_aux base (Z.to_nat (to_Z exp)).

(** Extract byte at position i (EVM BYTE opcode semantics) *)
Definition byte_spec (i x : uint256) : uint256 :=
  if (to_Z i >=? 32) then from_Z 0
  else
    let byte_pos := 31 - to_Z i in
    let bit_pos := byte_pos * 8 in
    from_Z ((Z.shiftr (to_Z x) bit_pos) mod 256).

(** Sign extend from byte position *)
Definition signextend_spec (byte_idx x : uint256) : uint256 :=
  if (to_Z byte_idx >=? 32) then x
  else
    let bit_pos := (to_Z byte_idx + 1) * 8 - 1 in
    let sign_bit := Z.testbit (to_Z x) bit_pos in
    if sign_bit
    then (* Extend with 1s *)
      let mask := Z.ones (Z.of_nat 256) - Z.ones (bit_pos + 1) in
      from_Z (Z.lor (to_Z x) mask)
    else (* Extend with 0s *)
      let mask := Z.ones (bit_pos + 1) in
      from_Z (Z.land (to_Z x) mask).

(** Byte swap (endianness conversion) *)
Definition byteswap_spec (x : uint256) : uint256 :=
  from_Z (
    let b0 := Z.land (Z.shiftr (to_Z x) 0) 255 in
    let b1 := Z.land (Z.shiftr (to_Z x) 8) 255 in
    let b2 := Z.land (Z.shiftr (to_Z x) 16) 255 in
    let b3 := Z.land (Z.shiftr (to_Z x) 24) 255 in
    (* ... and so on for all 32 bytes *)
    (* This is a simplified version - full version would handle all 32 bytes *)
    Z.shiftl b3 0 + Z.shiftl b2 8 + Z.shiftl b1 16 + Z.shiftl b0 24
  ).

(** ** Bit Manipulation Specifications *)

(** Count leading zeros *)
Definition countl_zero_spec (x : uint256) : nat :=
  if (to_Z x =? 0) then 256
  else 256 - Z.to_nat (Z.log2 (to_Z x)) - 1.

(** Count trailing zeros *)
Definition countr_zero_spec (x : uint256) : nat :=
  if (to_Z x =? 0) then 256
  else Z.to_nat (Z.log2 (Z.land (to_Z x) (-(to_Z x)))).

(** Population count (number of 1 bits) *)
Fixpoint popcount_aux (z : Z) (fuel : nat) : nat :=
  match fuel with
  | O => O
  | S n => if (z =? 0) then O
           else (if Z.testbit z 0 then 1 else 0) + popcount_aux (Z.shiftr z 1) n
  end.

Definition popcount_spec (x : uint256) : nat :=
  popcount_aux (to_Z x) 256.

(** ** Basic Lemmas *)

(** Normalization is idempotent *)
Lemma normalize_idem : forall z,
  normalize (normalize z) = normalize z.
Proof.
  intros. unfold normalize.
  rewrite Z.mod_mod; try reflexivity.
  unfold modulus. lia.
Qed.

(** to_Z o from_Z is normalize *)
Lemma to_from_Z : forall z,
  to_Z (from_Z z) = normalize z.
Proof.
  intros. unfold to_Z, from_Z. simpl. reflexivity.
Qed.

(** from_Z o to_Z is identity *)
Lemma from_to_Z : forall x,
  from_Z (to_Z x) = x.
Proof.
  intros [z [Hz_lo Hz_hi]]. unfold from_Z, to_Z. simpl.
  apply subset_eq_compat. simpl.
  rewrite Z.mod_small; auto.
Qed.

************************************************************
**)

(** Addition is commutative *)
Lemma add_comm : forall x y,
  add_spec x y = add_spec y x.
Proof.
  intros. unfold add_spec. rewrite Z.add_comm. reflexivity.
Qed.

(** Addition is associative *)
Lemma add_assoc : forall x y z,
  add_spec (add_spec x y) z = add_spec x (add_spec y z).
Proof.
  intros. unfold add_spec, normalize256.
  rewrite !Z.add_mod_idemp_l; try (unfold modulus; lia).
  rewrite !Z.add_mod_idemp_r; try (unfold modulus; lia).
  rewrite Z.add_assoc. reflexivity.
Qed.
