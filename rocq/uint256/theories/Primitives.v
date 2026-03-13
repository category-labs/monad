(** * Primitive 64-bit Operations

    This file defines the specifications and implementations for 64-bit
    primitive operations that form the building blocks of uint256 operations.

    These correspond to the primitive operations in uint256.hpp:
    - addc: addition with carry
    - subb: subtraction with borrow
    - mulx: extended multiplication
    - div: extended division
    - shld/shrd: double-precision shifts
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Uint256 Require Import Uint Spec.

(** ** Constants for 64-bit arithmetic *)

Definition modulus64 : Z := 2^64.
Definition max_uint64 : Z := modulus64 - 1.

(** ** Type Definitions *)

(** A uint64 is modelled as Z for simplicity. *)
Definition uint64 : Type := Z.

(** Extract Z value *)
Definition to_Z64 (x : uint64) : Z := x.

(** Convert Z to uint64 *)
Definition from_Z64 (z : Z) : uint64 := z.

(* Ensure an integer is within the [0, 2^64) range. *)
Definition normalize64 (z : Z) : Z := z mod modulus64.

(** 256-bit as a vector of 4 64-bit unsigned integers *)
(** Little-endian: v0 is the least significant *)
Record uint256 := mk_uint256 {
  v0 : uint64;
  v1 : uint64;
  v2 : uint64;
  v3 : uint64
}.

(** Convert to mathematical integer *)
Definition to_Z256 (x : uint256) : Z :=
  to_Z64 x.(v0) +
  to_Z64 x.(v1) * 2^64 +
  to_Z64 x.(v2) * 2^128 +
  to_Z64 x.(v3) * 2^192.

Definition from_Z256 (z : Z) : uint256 :=
  let z' := normalize256 z in
  mk_uint256
    (from_Z64 (z' mod 2^64))
    (from_Z64 (z' mod 2^128))
    (from_Z64 (z' mod 2^192))
    (from_Z64 (z' / 2^192)).

(* 256-bit result with carry/borrow *)
Record result256_with_carry := {
    value256 : uint256;
    carry256 : bool
}.

(** 64-bit result with carry/borrow (legacy, for concrete Z code) *)
Record result64_with_carry := {
  value64 : uint64;
  carry64 : bool
}.

(** Result type for extended multiplication (64x64 -> 128) *)
Record mulx_result := {
  hi : uint64;
  lo : uint64
}.

(** Result type for extended division (128 / 64 -> 64) *)
Record div64_result := {
  quot64 : uint64;
  rem64 : uint64
}.

Module Primitives (Import U64 : Uint64Ops).
Module MN := UintNotations(U64).
Import MN.
Open Scope uint_scope.

(** 64-bit result with carry/borrow *)
Record result64 := {
  value64 : U64.t;
  carry64 : bool
}.

(** ** Addition with Carry *)

(** Specification for addc (matches addc_constexpr from uint256.hpp)

    Computes: sum = lhs + rhs + carry_in
    Returns: (sum mod 2^64, carry_out)

    This matches the logic:
      uint64_t const sum = lhs + rhs;
      bool carry_out = sum < lhs;
      uint64_t const sum_carry = sum + carry_in;
      carry_out |= sum_carry < sum;
*)
Definition addc64 (lhs rhs : U64.t) (carry_in : bool) : result64 :=
  let sum := lhs + rhs in
  let cout := sum <? lhs in
  let sum_carry := sum + of_bool carry_in in
  {|
    value64 := sum_carry;
    carry64 := (cout || (sum_carry <? sum))%bool
  |}.

(** ** Subtraction with Borrow *)

(** Specification for subb (matches subb_constexpr from uint256.hpp)

    Computes: diff = lhs - rhs - borrow_in
    Returns: (diff mod 2^64, borrow_out)

    This matches the logic:
      uint64_t const sub = lhs - rhs;
      bool borrow_out = rhs > lhs;
      uint64_t const sub_borrow = sub - borrow_in;
      borrow_out |= borrow_in > sub;
*)

Definition subb64 (lhs rhs : U64.t) (borrow_in : bool) : result64 :=
  let bin := of_bool borrow_in in
  let sub := lhs - rhs in
  let bout := rhs >? lhs in
  let sub_borrow := sub - bin in
  {|
    value64 := sub_borrow;
    carry64 := (bout || (bin >? sub))%bool  (* borrow if result would be negative *)
  |}.

(** ** Double-Precision Shifts *)

(** Left shift with double precision (shld instruction)

    Computes: high bits of [(high || low) << shift]

    This matches shld_constexpr in uint256.hpp:
      return (high << shift) | ((low >> 1) >> (63 - shift));

    The formulation [(low >> 1) >> (63 - shift)] instead of
    [low >> (64 - shift)] avoids undefined behavior when
    [shift = 0] (x86 masks the shift count to 6 bits). *)
Definition shld64 (high low : U64.t) (shift : nat) : U64.t :=
  orw (shl high shift) (shr (shr low 1) (63 - shift)).

(** Right shift with double precision (shrd instruction)

    Computes: low bits of [(high || low) >> shift]

    This matches shrd_constexpr in uint256.hpp:
      return (low >> shift) | ((high << 1) << (63 - shift)); *)
Definition shrd64 (high low : U64.t) (shift : nat) : U64.t :=
  orw (shr low shift) (shl (shl high 1) (63 - shift)).

(** Note: [mulx] and [div] are part of the [UintOps] interface
    and do not need separate definitions here. *)

End Primitives.

(** ** Pure Z utility lemmas *)

Lemma mod_overflow_iff : forall a b M,
    0 <= a < M -> 0 <= b < M -> M > 0 ->
    ((a + b) mod M < a <-> a + b >= M).
Proof.
  intros a b M Ha Hb HM.
  split; intro H.
  - destruct (Z_lt_ge_dec (a + b) M) as [Hno_ov | Hov].
    + rewrite Z.mod_small in H; lia.
    + assumption.
  - rewrite Z.mod_eq by lia.
    assert (Hdiv: 1 = (a + b) / M) by
      (apply Z.div_unique with (r := a + b - M); lia).
    rewrite <- Hdiv, Z.mul_1_r; clear Hdiv.
    lia.
Qed.

Lemma le_add_nonneg_r : forall n m p : Z,
  m <= n -> 0 <= p -> m <= n + p.
Proof.
  intros n m p Hmn Hp.
  rewrite <- (Z.add_0_r m).
  apply Z.add_le_mono; assumption.
Qed.

Lemma mod_underflow_iff : forall a b M,
    0 <= a < M -> 0 <= b < M -> M > 0 ->
    ((a - b) mod M > a <-> a < b).
Proof.
  intros a b M Ha Hb HM.
  split; intro H.
  - destruct (Z_lt_ge_dec a b) as [Hlt | Hge].
    + assumption.
    + rewrite Z.mod_small in H; lia.
  - rewrite Z.mod_eq by lia.
    replace ((a - b) / M) with (-1) by (apply Z.div_unique with (a - b + M); lia).
    lia.
Qed.

(** ** Legacy concrete definitions

    The following definitions use a direct Z representation for uint64
    and are still used by RuntimeMul.v, Words.v, Division.v, etc.
    They will be migrated to the module interface incrementally. *)

Definition mulx64 (x y : uint64) : mulx_result :=
  let prod := to_Z64 x * to_Z64 y in
  {|
    hi := from_Z64 (Z.shiftr prod 64);
    lo := from_Z64 (normalize64 prod)
  |}.

Definition div64 (u_hi u_lo v : uint64) : div64_result :=
  let u := Z.shiftl (to_Z64 u_hi) 64 + to_Z64 u_lo in
  let v_z := to_Z64 v in
  {|
    quot64 := from_Z64 (u / v_z);
    rem64 := from_Z64 (u mod v_z)
  |}.

Definition div64_precondition (u_hi v : uint64) : Prop :=
  to_Z64 u_hi < to_Z64 v.

Definition shld64 (high low : uint64) (shift : nat) : uint64 :=
  if Nat.leb 64 shift then from_Z64 0
  else
    let h := to_Z64 high in
    let l := to_Z64 low in
    let shifted_high := Z.shiftl h (Z.of_nat shift) in
    let shifted_low := Z.shiftr (Z.shiftr l 1) (Z.of_nat (63 - shift)) in
    normalize64 (Z.lor shifted_high shifted_low).

Definition shrd64 (high low : uint64) (shift : nat) : uint64 :=
  if Nat.leb 64 shift then from_Z64 0
  else
    let h := to_Z64 high in
    let l := to_Z64 low in
    let shifted_low := Z.shiftr l (Z.of_nat shift) in
    let shifted_high := Z.shiftl (Z.shiftl h 1) (Z.of_nat (63 - shift)) in
    normalize64 (Z.lor shifted_low shifted_high).

(** Legacy concrete addc64/subb64 used by other files *)
Definition addc64 (lhs rhs : uint64) (carry_in : bool) : result64_with_carry :=
  let sum := normalize64 (to_Z64 lhs + to_Z64 rhs) in
  let cout := sum <? to_Z64 lhs in
  let cin_z := if carry_in then 1 else 0 in
  let sum_carry := normalize64 (sum + cin_z) in
  {|
    value64 := sum_carry;
    carry64 := (cout || (sum_carry <? sum))%bool
  |}.

Definition subb64 (lhs rhs : uint64) (borrow_in : bool) : result64_with_carry :=
  let sub := normalize64 (to_Z64 lhs - to_Z64 rhs) in
  let bout := to_Z64 rhs >? to_Z64 lhs in
  let bin_z := if borrow_in then 1 else 0 in
  let sub_borrow := normalize64 (sub - bin_z) in
  {|
    value64 := sub_borrow;
    carry64 := (bout || (bin_z >? sub))%bool
  |}.

(** ** Legacy correctness lemmas *)

Lemma mulx64_correct : forall x y,
  0 <= x -> 0 <= y ->
  let result := mulx64 x y in
  let prod := to_Z64 x * to_Z64 y in
  prod = Z.shiftl (to_Z64 (hi result)) 64 + to_Z64 (lo result).
Proof.
  intros x y Hx Hy.
  unfold mulx64. cbn [hi lo].
  unfold from_Z64, to_Z64, normalize64, modulus64.
  set (p := x * y).
  assert (Hp: 0 <= p) by (unfold p; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_eq by lia.
  ring.
Qed.

Lemma mulx64_hi_bounded : forall x y,
  0 <= x < modulus64 ->
  0 <= y < modulus64 ->
  0 <= to_Z64 (hi (mulx64 x y)) < modulus64.
Proof.
  intros x y Hx Hy.
  unfold mulx64, hi, from_Z64, to_Z64, modulus64 in *. split.
  - apply Z.shiftr_nonneg. lia.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_lt_upper_bound; [lia|].
    assert (x * y < 2^64 * 2^64) by nia.
    rewrite <- Z.pow_add_r by lia. simpl. lia.
Qed.

Lemma mulx64_lo_bounded : forall x y,
  0 <= x < modulus64 ->
  0 <= y < modulus64 ->
  0 <= to_Z64 (lo (mulx64 x y)) < modulus64.
Proof.
  intros x y Hx Hy.
  unfold mulx64, lo, from_Z64, to_Z64, normalize64, modulus64 in *.
  apply Z.mod_pos_bound. lia.
Qed.

Lemma div64_correct : forall u_hi u_lo v,
  0 < v ->
  div64_precondition u_hi v ->
  let result := div64 u_hi u_lo v in
  let u := Z.shiftl (to_Z64 u_hi) 64 + to_Z64 u_lo in
  u = to_Z64 (quot64 result) * to_Z64 v + to_Z64 (rem64 result) /\
  to_Z64 (rem64 result) < to_Z64 v.
Proof.
  intros u_hi u_lo v Hv_pos Hprecond.
  unfold div64. cbn [quot64 rem64].
  unfold from_Z64, to_Z64.
  split.
  - rewrite Z.mul_comm. apply Z_div_mod_eq_full.
  - apply Z.mod_pos_bound. lia.
Qed.

Lemma shld64_shift_0 : forall high low,
  0 <= high < modulus64 ->
  0 <= low < modulus64 ->
  shld64 high low 0 = high.
Proof.
  intros high low Hhigh Hlow.
  unfold shld64, from_Z64, to_Z64, normalize64, modulus64 in *. simpl.
  rewrite Z.shiftr_shiftr by lia. simpl (1 + 63).
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.div_small by lia.
  rewrite Z.lor_0_r.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma shld64_shift_ge_64 : forall high low shift,
  (64 <= shift)%nat ->
  shld64 high low shift = from_Z64 0.
Proof.
  intros high low shift Hshift.
  unfold shld64.
  destruct (Nat.leb 64 shift) eqn:Hle.
  - reflexivity.
  - apply Nat.leb_gt in Hle. lia.
Qed.

Lemma shld64_correct : forall high low shift,
  0 <= high < modulus64 ->
  0 <= low < modulus64 ->
  (0 < shift < 64)%nat ->
  let combined := high * modulus64 + low in
  let shifted := Z.shiftl combined (Z.of_nat shift) in
  to_Z64 (shld64 high low shift) = normalize64 (Z.shiftr shifted 64).
Proof.
  intros high low shift Hhigh Hlow Hshift.
  unfold shld64, normalize64.
  destruct (Nat.leb 64 shift) eqn:Hle.
  { apply Nat.leb_le in Hle. lia. }
  unfold from_Z64, to_Z64, modulus64.
  rewrite Z.shiftr_shiftl_r by lia.
  rewrite Z.shiftr_shiftr by lia.
  replace (1 + Z.of_nat (63 - shift)) with (64 - Z.of_nat shift) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hpow: 2 ^ 64 = 2 ^ (64 - Z.of_nat shift) * 2 ^ Z.of_nat shift).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  replace (high * 2 ^ 64 + low) with
    (high * 2 ^ Z.of_nat shift * 2 ^ (64 - Z.of_nat shift) + low)
    by (rewrite Hpow; ring).
  rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  f_equal.
  set (a := high * 2 ^ Z.of_nat shift).
  set (b := low / 2 ^ (64 - Z.of_nat shift)).
  rewrite <- Z.add_0_r at 1.
  enough (Z.land a b = 0) by (rewrite <- H; apply Z.add_lor_land).
  unfold a, b.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. rewrite Z.bits_0.
  destruct (Z.lt_ge_cases n (Z.of_nat shift)) as [Hlt | Hge].
  - rewrite Bool.andb_false_iff. left.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec_low by lia.
    reflexivity.
  - rewrite Bool.andb_false_iff. right.
    rewrite <- Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_spec by lia.
    apply Z.bits_above_log2; [lia|].
    enough (Z.log2 low < 64) by lia.
    destruct (Z.eq_dec low 0).
    + subst; simpl; lia.
    + apply Z.log2_lt_pow2; unfold modulus64 in Hlow; lia.
Qed.

Lemma shrd64_shift_0 : forall high low,
  0 <= high < modulus64 ->
  0 <= low < modulus64 ->
  shrd64 high low 0 = low.
Proof.
  intros high low Hhigh Hlow.
  unfold shrd64. simpl (Nat.leb 64 0). cbv iota.
  simpl (63 - 0)%nat. simpl (Z.of_nat 0). simpl (Z.of_nat 63).
  rewrite Z.shiftr_0_r.
  unfold normalize64, from_Z64, to_Z64, modulus64 in *.
  rewrite Z.shiftl_shiftl by lia. simpl (1 + 63).
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite <- Z.land_ones by lia.
  rewrite Z.land_lor_distr_l.
  rewrite Z.land_ones_low.
  2: lia.
  2: { destruct (Z.eq_dec low 0); [subst; simpl|apply Z.log2_lt_pow2]; lia. }
  enough (Z.land (high * 2 ^ 64) (Z.ones 64) = 0) by (rewrite H; apply Z.lor_0_r).
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n 64) as [Hlt | Hge].
  - rewrite Bool.andb_false_iff. left.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    apply Z.shiftl_spec_low; lia.
  - rewrite Bool.andb_false_iff. right.
    apply Z.ones_spec_high; lia.
Qed.

Lemma shrd64_shift_ge_64 : forall high low shift,
  (64 <= shift)%nat ->
  shrd64 high low shift = from_Z64 0.
Proof.
  intros high low shift Hshift.
  unfold shrd64.
  destruct (Nat.leb 64 shift) eqn:Hle.
  - reflexivity.
  - apply Nat.leb_gt in Hle. lia.
Qed.

Lemma shrd64_correct : forall high low shift,
  0 <= high < modulus64 ->
  0 <= low < modulus64 ->
  (0 < shift < 64)%nat ->
  let combined := high * modulus64 + low in
  let shifted := Z.shiftr combined (Z.of_nat shift) in
  to_Z64 (shrd64 high low shift) = shifted mod modulus64.
Proof.
  intros high low shift Hhigh Hlow Hshift.
  unfold shrd64, normalize64.
  destruct (Nat.leb 64 shift) eqn:Hle.
  { apply Nat.leb_le in Hle. lia. }
  unfold from_Z64, to_Z64, modulus64.
  rewrite Z.shiftl_shiftl by lia.
  replace (1 + Z.of_nat (63 - shift)) with (64 - Z.of_nat shift) by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  assert (Hpow: 2 ^ 64 = 2 ^ (64 - Z.of_nat shift) * 2 ^ Z.of_nat shift).
  { rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  replace (high * 2 ^ 64 + low) with
    (high * 2 ^ (64 - Z.of_nat shift) * 2 ^ Z.of_nat shift + low)
    by (rewrite Hpow; ring).
  rewrite Z.div_add_l by (apply Z.pow_nonzero; lia).
  f_equal.
  set (a := low / 2 ^ Z.of_nat shift).
  set (b := high * 2 ^ (64 - Z.of_nat shift)).
  rewrite Z.add_comm. rewrite <- Z.add_0_r at 1.
  enough (Z.land a b = 0) by (rewrite <- H; apply Z.add_lor_land).
  unfold a, b.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec. rewrite Z.bits_0.
  destruct (Z.lt_ge_cases n (64 - Z.of_nat shift)) as [Hlt | Hge].
  - rewrite Bool.andb_false_iff. right.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec_low by lia.
    reflexivity.
  - rewrite Bool.andb_false_iff. left.
    rewrite <- Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_spec by lia.
    apply Z.bits_above_log2; [lia|].
    enough (Z.log2 low < 64) by lia.
    destruct (Z.eq_dec low 0).
    + subst; simpl; lia.
    + apply Z.log2_lt_pow2; unfold modulus64 in Hlow; lia.
Qed.

Lemma shld64_bounded : forall high low shift,
  0 <= to_Z64 (shld64 high low shift) < modulus64.
Proof.
  intros high low shift.
  unfold shld64.
  destruct (Nat.leb 64 shift) eqn:Hle.
  - unfold from_Z64, to_Z64, modulus64. lia.
  - unfold normalize64, from_Z64, to_Z64, modulus64.
    apply Z.mod_pos_bound. lia.
Qed.

Lemma shrd64_bounded : forall high low shift,
  0 <= to_Z64 (shrd64 high low shift) < modulus64.
Proof.
  intros high low shift.
  unfold shrd64.
  destruct (Nat.leb 64 shift) eqn:Hle.
  - unfold from_Z64, to_Z64, modulus64. lia.
  - unfold normalize64, from_Z64, to_Z64, modulus64.
    apply Z.mod_pos_bound. lia.
Qed.
