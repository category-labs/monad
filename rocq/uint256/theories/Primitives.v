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
From Stdlib Require Import List.
Import ListNotations.
Require Import Spec.
Open Scope Z_scope.

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

(** 64-bit result with carry/borrow *)
Record result64_with_carry := {
  value64 : uint64;
  carry64 : bool
}.

(* 256-bit result with carry/borrow *)
Record result256_with_carry := {
    value256 : uint256;
    carry256 : bool
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
Definition addc64 (lhs rhs : uint64) (carry_in : bool) : result64_with_carry :=
  let lhs_z := to_Z64 lhs in
  let rhs_z := to_Z64 rhs in
  let cin := if carry_in then 1 else 0 in
  let sum := normalize64 (lhs_z + rhs_z) in
  let cout := sum <? lhs_z in
  let sum_carry := normalize64 (sum + cin) in
  {|
    value64 := from_Z64 sum_carry;
    carry64 := (cout || (sum_carry <? sum))%bool
  |}.

(* Matches addc in uint256.hpp *)
(** Add two uint256 values, return result and carry *)
Definition add256_c (x y : uint256) : result256_with_carry :=
  let w0 := addc64 x.(v0) y.(v0) false in
  let w1 := addc64 x.(v1) y.(v1) w0.(carry64) in
  let w2 := addc64 x.(v2) y.(v2) w1.(carry64) in
  let w3 := addc64 x.(v3) y.(v3) w2.(carry64) in
  {|
    value256 := (mk_uint256 w0.(value64) w1.(value64)
                            w2.(value64) w3.(value64));
    carry256 := w3.(carry64)
  |}.

(** ** Correctness Properties *)


(* Claude Code-inspired Proof *)
Lemma mod_overflow_iff : forall a b M,
    0 <= a < M -> 0 <= b < M -> M > 0 ->
    ((a + b) mod M < a <-> a + b >= M).
Proof.
  intros a b M Ha Hb HM.
  split; intro H.
  - (* -> direction: (a + b) mod M < a implies a + b >= M *)
    destruct (Z_lt_ge_dec (a + b) M) as [Hno_ov | Hov].
    + (* a + b < M case: derive contradiction *)
      rewrite Z.mod_small in H; lia.
    + assumption.
  - (* <- direction: a + b >= M implies (a + b) mod M < a *)
    rewrite Z.mod_eq by lia.
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

(* Underflow detection: (a - b) mod M > a iff a < b (when 0 <= a, b < M) *)
Lemma mod_underflow_iff : forall a b M,
    0 <= a < M -> 0 <= b < M -> M > 0 ->
    ((a - b) mod M > a <-> a < b).
Proof.
  intros a b M Ha Hb HM.
  split; intro H.
  - (* -> direction: (a - b) mod M > a implies a < b *)
    destruct (Z_lt_ge_dec a b) as [Hlt | Hge].
    + assumption.
    + (* a >= b, so a - b >= 0, mod is identity, contradiction *)
      rewrite Z.mod_small in H; lia.
  - (* <- direction: a < b implies (a - b) mod M > a *)
    rewrite Z.mod_eq by lia.
    replace ((a - b) / M) with (-1) by (apply Z.div_unique with (a - b + M); lia).
    lia.
Qed.

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

Definition subb64 (lhs rhs : uint64) (borrow_in : bool) : result64_with_carry :=
  let lhs_z := to_Z64 lhs in
  let rhs_z := to_Z64 rhs in
  let bin := if borrow_in then 1 else 0 in
  let sub := normalize64 (lhs_z - rhs_z) in
  let bout := rhs_z >? lhs_z in
  let sub_borrow := normalize64 (sub - bin) in
  {|
    value64 := from_Z64 sub_borrow;
    carry64 := (bout || (bin >? sub))%bool  (* borrow if result would be negative *)
  |}.

(** ** Extended Multiplication *)

(** Specification for mulx (64-bit × 64-bit → 128-bit)

    Computes: product = x * y
    Returns: (high 64 bits, low 64 bits)

    This matches mulx_constexpr:
      uint128_t const prod = static_cast<uint128_t>(x) * static_cast<uint128_t>(y);
      r_hi = static_cast<uint64_t>(prod >> uint128_t{64});
      r_lo = static_cast<uint64_t>(prod);
*)
Definition mulx64 (x y : uint64) : mulx_result :=
  let prod := to_Z64 x * to_Z64 y in
  {|
    hi := from_Z64 (Z.shiftr prod 64);
    lo := from_Z64 (normalize64 prod)
  |}.

(** ** Extended Division *)

(** Specification for div (128-bit / 64-bit → 64-bit with remainder)

    Computes: (u_hi * 2^64 + u_lo) / v = quotient remainder rem
    Returns: (quotient, remainder)

    Precondition: u_hi < v (to ensure quotient fits in 64 bits)

    This matches div_constexpr:
      auto const u = (static_cast<uint128_t>(u_hi) << 64) | u_lo;
      auto const quot = static_cast<uint64_t>(u / v);
      auto const rem = static_cast<uint64_t>(u % v);
*)
Definition div64 (u_hi u_lo v : uint64) : div64_result :=
  let u := Z.shiftl (to_Z64 u_hi) 64 + to_Z64 u_lo in
  let v_z := to_Z64 v in
  {|
    quot64 := from_Z64 (u / v_z);
    rem64 := from_Z64 (u mod v_z)
  |}.

(** Precondition for div64: high word must be less than divisor *)
Definition div64_precondition (u_hi v : uint64) : Prop :=
  to_Z64 u_hi < to_Z64 v.

(** ** Double-Precision Shifts *)

(** Left shift with double precision (shld instruction)

    Specification: (high || low) << shift, return high part

    This matches shld_constexpr:
      return (high << shift) | ((low >> 1) >> (63 - shift));

    The peculiar formulation (low >> 1) >> (63 - shift) instead of low
    >> (64 - shift) is to avoid undefined behavior when shift = 0 (x86
    masks the shift count to 6 bits).
*)
Definition shld64 (high low : uint64) (shift : nat) : uint64 :=
  if Nat.leb 64 shift then from_Z64 0
  else
    let h := to_Z64 high in
    let l := to_Z64 low in
    let shifted_high := Z.shiftl h (Z.of_nat shift) in
    let shifted_low := Z.shiftr (Z.shiftr l 1) (Z.of_nat (63 - shift)) in
    normalize64 (Z.lor shifted_high shifted_low).

(** Right shift with double precision (shrd instruction)

    Specification: (high || low) >> shift, return low part

    This matches shrd_constexpr:
      return (low >> shift) | ((high << 1) << (63 - shift));

    Note: We use normalize64 on shifted_high to simulate C++ uint64_t
    overflow behavior (shifting left by 64 or more gives 0).
*)
Definition shrd64 (high low : uint64) (shift : nat) : uint64 :=
  if Nat.leb 64 shift then from_Z64 0
  else
    let h := to_Z64 high in
    let l := to_Z64 low in
    let shifted_low := Z.shiftr l (Z.of_nat shift) in
    let shifted_high := Z.shiftl (Z.shiftl h 1) (Z.of_nat (63 - shift)) in
    normalize64 (Z.lor shifted_low shifted_high).

(** ** Correctness Properties *)

(** addc64 produces correct mathematical result *)
Lemma addc64_correct : forall lhs rhs cin,
  let result := addc64 lhs rhs cin in
  let cin_z := if cin then 1 else 0 in
  to_Z64 (value64 result) = (to_Z64 lhs + to_Z64 rhs + cin_z) mod modulus64.
Proof.
  intros; simpl.
  unfold normalize64, from_Z64, to_Z64, modulus64, cin_z.
  rewrite Zplus_mod_idemp_l.
  reflexivity.
Qed.

(** addc64 carry is correct *)
Lemma addc64_carry_correct : forall lhs rhs cin,
  0 <= lhs < modulus64 ->
  0 <= rhs < modulus64 ->
  let result := addc64 lhs rhs cin in
  let cin_z := if cin then 1 else 0 in
  carry64 result = true <-> to_Z64 lhs + to_Z64 rhs + cin_z >= modulus64.
Proof.
  intros lhs rhs cin Hlhs Hrhs.
  simpl. unfold normalize64, to_Z64, modulus64 in *.
  set (M := 2^64) in *.
  set (sum := (lhs + rhs) mod M).
  set (cin_z := if cin then 1 else 0).
  set (sum_carry := (sum + cin_z) mod M).
  assert (Hcin_bound: 0 <= cin_z <= 1) by (unfold cin_z; destruct cin; lia).
  assert (Hsum_bound: 0 <= sum < M) by (unfold sum; apply Z.mod_pos_bound; lia).
  assert (Hsum_le: sum <= lhs + rhs) by (unfold sum; apply Z.mod_le; lia).
  rewrite Bool.orb_true_iff, 2!Z.ltb_lt.
  split.
  - intros [Hov1 | Hov2].
    + enough (lhs + rhs >= M) by lia. apply mod_overflow_iff; lia.
    + apply -> mod_overflow_iff in Hov2; lia.
  - intro Hoverflow.
    destruct (Z_lt_ge_dec (lhs + rhs) M) as [Hno_ov1 | Hov1].
    + right. apply <- mod_overflow_iff; [|lia | lia | lia].
      unfold sum; rewrite Z.mod_small by lia. lia.
    + left. apply <- mod_overflow_iff; lia.
Qed.

(** subb64 produces correct mathematical result *)
Lemma subb64_correct : forall lhs rhs bin,
  let result := subb64 lhs rhs bin in
  let bin_z := if bin then 1 else 0 in
  to_Z64 (value64 result) = (to_Z64 lhs - to_Z64 rhs - bin_z) mod modulus64.
Proof.
  intros; simpl. unfold normalize64, from_Z64, to_Z64, modulus64, bin_z.
  rewrite Zminus_mod_idemp_l.
  reflexivity.
Qed.

(** subb64 borrow is correct *)
Lemma subb64_carry_correct : forall lhs rhs bin,
  0 <= lhs < modulus64 ->
  0 <= rhs < modulus64 ->
  let result := subb64 lhs rhs bin in
  let bin_z := if bin then 1 else 0 in
  carry64 result = true <-> to_Z64 lhs - to_Z64 rhs - bin_z < 0.
Proof.
  intros lhs rhs bin Hlhs Hrhs.
  simpl. unfold normalize64, to_Z64, modulus64 in *.
  set (M := 2^64) in *.
  set (sub := (lhs - rhs) mod M).
  set (bin_z := if bin then 1 else 0).
  set (sub_borrow := (sub - bin_z) mod M).
  assert (Hbin_bound: 0 <= bin_z <= 1) by (unfold bin_z; destruct bin; lia).
  assert (Hsub_bound: 0 <= sub < M) by (unfold sub; apply Z.mod_pos_bound; lia).
  assert (Hsub_ge: sub >= lhs - rhs).
  { unfold sub.
    destruct (Z_lt_ge_dec (lhs - rhs) 0) as [Hneg | Hpos].
    - (* Negative case: lhs - rhs < 0 *)
      pose proof (Z.mod_pos_bound (lhs - rhs) M ltac:(lia)) as Hmod_bound.
      lia.
    - (* Positive case: lhs - rhs >= 0 *)
      rewrite Z.mod_small; lia. }
  rewrite Bool.orb_true_iff, Z.gtb_lt, Z.gtb_lt.
  split.
  - (* Forward: borrow detected -> mathematical underflow *)
    intros [Huf1 | Huf2].
    + lia.
    + lia.
  - (* Backward: mathematical underflow -> borrow detected *)
    intro Hunderflow.
    destruct (Z_lt_ge_dec (lhs - rhs) 0) as [Huf1 | Hno_uf1].
    + left. lia.
    + right.
      (* lhs >= rhs but lhs - rhs - bin_z < 0, so bin_z = 1 and lhs = rhs *)
      assert (Hsub_eq: sub = lhs - rhs) by (unfold sub; rewrite Z.mod_small; lia).
      lia.
Qed.

(** mulx64 produces correct 128-bit product *)
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

(** div64 produces correct quotient and remainder *)
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

(** ** Double-Precision Shift Correctness *)

(** shld64 returns high when shift is 0 *)
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

(** shld64 returns 0 when shift >= 64 *)
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

(** shld64 computes high bits of 128-bit left shift *)
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
  - (* n < shift: high * 2^shift has no bits below shift *)
    rewrite Bool.andb_false_iff. left.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec_low by lia.
    reflexivity.
  - (* n >= shift: low / 2^(64-shift) has no bits at or above shift *)
    rewrite Bool.andb_false_iff. right.
    rewrite <- Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_spec by lia.
    apply Z.bits_above_log2; [lia|].
    enough (Z.log2 low < 64) by lia.
    destruct (Z.eq_dec low 0).
    + subst; simpl; lia.
    + apply Z.log2_lt_pow2; unfold modulus64 in Hlow; lia.
Qed.

(** shrd64 returns low when shift is 0 *)
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
  - (* n < 64: high * 2^64 has no bits below 64 *)
    rewrite Bool.andb_false_iff. left.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    apply Z.shiftl_spec_low; lia.
  - (* n >= 64: Z.ones 64 has no bits at or above 64 *)
    rewrite Bool.andb_false_iff. right.
    apply Z.ones_spec_high; lia.
Qed.

(** shrd64 returns 0 when shift >= 64 *)
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

(** shrd64 computes low bits of 128-bit right shift *)
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
  - (* n < 64 - shift: high * 2^(64-shift) has no bits below 64-shift *)
    rewrite Bool.andb_false_iff. right.
    rewrite <- Z.shiftl_mul_pow2 by lia.
    rewrite Z.shiftl_spec_low by lia.
    reflexivity.
  - (* n >= 64 - shift: low / 2^shift has no bits at or above 64-shift *)
    rewrite Bool.andb_false_iff. left.
    rewrite <- Z.shiftr_div_pow2 by lia.
    rewrite Z.shiftr_spec by lia.
    apply Z.bits_above_log2; [lia|].
    enough (Z.log2 low < 64) by lia.
    destruct (Z.eq_dec low 0).
    + subst; simpl; lia.
    + apply Z.log2_lt_pow2; unfold modulus64 in Hlow; lia.
Qed.

(** ** Double-Precision Shift Bounds Lemmas *)

(** shld64 result is always in uint64 range *)
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

(** shld64 with valid inputs produces valid output *)
Lemma shld64_valid : forall high low shift,
  0 <= high < modulus64 ->
  0 <= low < modulus64 ->
  0 <= to_Z64 (shld64 high low shift) < modulus64.
Proof.
  intros. apply shld64_bounded.
Qed.

(** shrd64 result is always in uint64 range *)
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

(** shrd64 with valid inputs produces valid output *)
Lemma shrd64_valid : forall high low shift,
  0 <= high < modulus64 ->
  0 <= low < modulus64 ->
  0 <= to_Z64 (shrd64 high low shift) < modulus64.
Proof.
  intros. apply shrd64_bounded.
Qed.

(** ** Multi-word Addition Helper *)

(** Add two 2-word numbers with carry propagation *)
Definition add128_spec (x_hi x_lo y_hi y_lo : uint64) : mulx_result :=
  let r0 := addc64 x_lo y_lo false in
  let r1 := addc64 x_hi y_hi (carry64 r0) in
  {|
    hi := value64 r1;
    lo := value64 r0
  |}.

(** ** Chaining Lemmas *)

(** Chaining two addc operations correctly computes the sum *)
Lemma addc64_chain_2 : forall x0 x1 y0 y1,
  let r0 := addc64 x0 y0 false in
  let r1 := addc64 x1 y1 (carry64 r0) in
  let x := Z.shiftl (to_Z64 x1) 64 + to_Z64 x0 in
  let y := Z.shiftl (to_Z64 y1) 64 + to_Z64 y0 in
  let result := Z.shiftl (to_Z64 (value64 r1)) 64 + to_Z64 (value64 r0) in
  result = (x + y) mod (2^128).
Proof.
  intros.
  (* This proof would expand the definitions and use arithmetic properties *)
  (* For now we admit it as a lemma to be proven *)
Admitted.

(** Similarly for 4-word (256-bit) addition *)
Lemma addc64_chain_4 : forall x0 x1 x2 x3 y0 y1 y2 y3,
  let r0 := addc64 x0 y0 false in
  let r1 := addc64 x1 y1 (carry64 r0) in
  let r2 := addc64 x2 y2 (carry64 r1) in
  let r3 := addc64 x3 y3 (carry64 r2) in
  let x := Z.shiftl (to_Z64 x3) 192 + Z.shiftl (to_Z64 x2) 128 +
           Z.shiftl (to_Z64 x1) 64 + to_Z64 x0 in
  let y := Z.shiftl (to_Z64 y3) 192 + Z.shiftl (to_Z64 y2) 128 +
           Z.shiftl (to_Z64 y1) 64 + to_Z64 y0 in
  let result := Z.shiftl (to_Z64 (value64 r3)) 192 +
                Z.shiftl (to_Z64 (value64 r2)) 128 +
                Z.shiftl (to_Z64 (value64 r1)) 64 +
                to_Z64 (value64 r0) in
  result = (x + y) mod (2^256).
Proof.
  (* This is the key lemma for proving 256-bit addition correctness *)
Admitted.

(** * Word-List Representation for Multi-Word Arithmetic *)

(** A word list represents a multi-word unsigned integer in little-endian order.
    The first element is the least significant word. *)
Definition words := list uint64.

(** Convert a word list to its mathematical value (little-endian) *)
Fixpoint to_Z_words (ws : words) : Z :=
  match ws with
  | [] => 0
  | w :: rest => to_Z64 w + 2^64 * to_Z_words rest
  end.

(** The number of bits needed to represent an n-word number *)
Definition words_bits (n : nat) : Z := Z.of_nat n * 64.

(** Modulus for an n-word number *)
Definition modulus_words (n : nat) : Z := 2 ^ (words_bits n).

(** ** Conversion Between uint256 and Words *)

(** Convert uint256 record to 4-element word list *)
Definition uint256_to_words (x : uint256) : words :=
  [v0 x; v1 x; v2 x; v3 x].

(** Convert 4-element word list to uint256 record *)
Definition words_to_uint256 (ws : words) : uint256 :=
  match ws with
  | [w0; w1; w2; w3] => mk_uint256 w0 w1 w2 w3
  | _ => mk_uint256 0 0 0 0  (* fallback for malformed input *)
  end.

(** Equivalence lemma: uint256 and word list representations agree *)
Lemma uint256_words_equiv : forall x : uint256,
  to_Z256 x = to_Z_words (uint256_to_words x).
Proof.
  intros x.
  unfold to_Z256, uint256_to_words, to_Z_words, to_Z64.
  ring.
Qed.

(** ** Word List Validity and Bounds *)

(** All words in list are in valid uint64 range *)
Definition words_valid (ws : words) : Prop :=
  Forall (fun w => 0 <= w < modulus64) ws.

(** Value of valid n-word list is bounded *)
Lemma words_valid_bound : forall ws,
  words_valid ws ->
  0 <= to_Z_words ws < modulus_words (length ws).
Proof.
  induction ws as [| w rest IH]; intros Hvalid.
  - unfold modulus_words, words_bits; simpl; lia.
  - unfold modulus_words, words_bits; cbn [to_Z_words length].
    inversion Hvalid as [| w' rest' Hw Hrest]; subst.
    specialize (IH Hrest).
    unfold to_Z64 in *.
    unfold modulus_words, words_bits in *.
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat (length rest)) * 64)
      with (64 + Z.of_nat (length rest) * 64) by ring.
    rewrite Z.pow_add_r by lia.
    unfold modulus64 in *.
    split; lia.
Qed.

(** Normalize a word list value to n words *)
Definition normalize_words (z : Z) (n : nat) : Z :=
  z mod modulus_words n.

(** ** Word Access and Update Helpers *)

(** Get word at index i (0 if out of bounds) *)
Definition get_word (ws : words) (i : nat) : uint64 :=
  nth i ws 0.

(** Set word at index i *)
Fixpoint set_word (ws : words) (i : nat) (v : uint64) : words :=
  match ws, i with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | w :: rest, S i' => w :: set_word rest i' v
  end.

(** Extend word list to length n (padding with zeros) *)
Definition extend_words (n : nat) : words := repeat 0 n.

(** ** Word List Helper Lemmas *)

(** Length of set_word is preserved *)
Lemma set_word_length : forall ws i v,
  length (set_word ws i v) = length ws.
Proof.
  induction ws as [|w rest IH]; intros i v.
  - simpl; reflexivity.
  - destruct i.
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(** get_word after set_word at same index *)
Lemma get_set_word_same : forall ws i v,
  (i < length ws)%nat ->
  get_word (set_word ws i v) i = v.
Proof.
  induction ws as [|w rest IH]; intros i v Hi.
  - simpl in Hi. lia.
  - destruct i.
    + simpl. reflexivity.
    + simpl in Hi. simpl. apply IH. lia.
Qed.

(** get_word after set_word at different index *)
Lemma get_set_word_other : forall ws i j v,
  i <> j ->
  get_word (set_word ws i v) j = get_word ws j.
Proof.
  induction ws as [|w rest IH]; intros i j v Hij.
  - simpl. reflexivity.
  - destruct i; destruct j; try lia.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply IH. lia.
Qed.

(** Length of extend_words *)
Lemma extend_words_length : forall n,
  length (extend_words n) = n.
Proof.
  intros. unfold extend_words. apply repeat_length.
Qed.

(** get_word from extend_words returns 0 *)
Lemma get_extend_words : forall n i,
  (i < n)%nat ->
  get_word (extend_words n) i = 0.
Proof.
  intros n i Hi.
  unfold get_word, extend_words.
  apply nth_repeat.
Qed.

(** extend_words has valid words (all zeros) *)
Lemma extend_words_valid : forall n,
  words_valid (extend_words n).
Proof.
  intros n. unfold extend_words, words_valid.
  apply Forall_forall. intros x Hx.
  apply repeat_spec in Hx. subst.
  unfold modulus64; lia.
Qed.

(** to_Z_words of extend_words is 0 *)
Lemma to_Z_extend_words : forall n,
  to_Z_words (extend_words n) = 0.
Proof.
  intros n. induction n as [|n' IH].
  - simpl. reflexivity.
  - unfold extend_words in *. simpl.
    unfold to_Z64. rewrite IH. lia.
Qed.

(** ** Word List Mathematical Properties *)

(** Contribution of setting word i to v *)
Lemma to_Z_words_set_word : forall ws i v,
  (i < length ws)%nat ->
  words_valid ws ->
  0 <= v < modulus64 ->
  to_Z_words (set_word ws i v) =
    to_Z_words ws - to_Z64 (get_word ws i) * 2^(64 * Z.of_nat i) +
    to_Z64 v * 2^(64 * Z.of_nat i).
Proof.
  induction ws as [|w rest IH]; intros i v Hi Hvalid Hv.
  - simpl in Hi. lia.
  - destruct i.
    + simpl. unfold get_word. simpl.
      unfold to_Z64. ring.
    + simpl in Hi.
      inversion Hvalid as [|w' rest' Hw Hrest]; subst.
      cbn [set_word to_Z_words].
      specialize (IH i v ltac:(lia) Hrest Hv).
      unfold to_Z64, get_word in *.
      rewrite IH.
      rewrite Nat2Z.inj_succ.
      replace (64 * Z.succ (Z.of_nat i)) with (64 + 64 * Z.of_nat i) by ring.
      rewrite Z.pow_add_r by lia.
Admitted.

(** * Truncating Multiplication (constexpr version)

    Models the C++ truncating_mul_constexpr function's unified nested-loop structure.
    This is schoolbook multiplication with truncation to R words.

    C++ reference:
      for (size_t j = 0; j < N; j++) {
          uint64_t carry = 0;
          for (size_t i = 0; i < M && i + j < R; i++) {
              uint64_t hi, lo;
              mulx(x[i], y[j], hi, lo);
              auto [s0, c0] = addc(lo, result[i + j], false);
              auto [s1, c1] = addc(s0, carry, false);
              result[i + j] = s1;
              auto [s2, c2] = addc(hi, c0, c1);
              carry = s2;
          }
          if (j + M < R) result[j + M] = carry;
      }
*)

(** Inner loop: process x[i] * y[j] for i = 0..M-1, accumulating into result[i+j]
    Returns updated result and final carry *)
Fixpoint constexpr_inner_loop (xs : words) (y : uint64) (result : words)
    (j : nat) (i : nat) (R : nat) (carry : uint64) : words * uint64 :=
  match xs with
  | [] => (result, carry)
  | x :: rest =>
      if (i + j <? R)%nat then
        let r := mulx64 x y in                                      (* hi:lo = x[i] * y[j] *)
        let s0 := addc64 (lo r) (get_word result (i + j)) false in  (* lo + result[i+j] *)
        let s1 := addc64 (value64 s0) carry false in                (* + carry *)
        let new_result := set_word result (i + j) (value64 s1) in
        let s2 := addc64 (hi r) 0 (carry64 s0 || carry64 s1) in     (* hi + c0 + c1 *)
        constexpr_inner_loop rest y new_result j (S i) R (value64 s2)
      else
        (result, carry)  (* i + j >= R: stop early (truncation) *)
  end.

(** Outer loop: iterate over y[j] for j = 0..N-1 *)
Fixpoint constexpr_outer_loop (xs ys : words) (result : words)
    (j : nat) (R : nat) : words :=
  match ys with
  | [] => result
  | y :: rest =>
      let '(new_result, carry) := constexpr_inner_loop xs y result j 0 R 0 in
      (* Store final carry at result[j + M] if in bounds *)
      let final_result :=
        if (j + length xs <? R)%nat
        then set_word new_result (j + length xs) carry
        else new_result in
      constexpr_outer_loop xs rest final_result (S j) R
  end.

(** truncating_mul_constexpr: schoolbook multiplication with truncation *)
Definition truncating_mul_constexpr (xs ys : words) (R : nat) : words :=
  let result := extend_words R in  (* Initialize to zeros *)
  constexpr_outer_loop xs ys result 0 R.

(** Specialization for uint256: 4x4 -> 4 words *)
Definition truncating_mul256_constexpr (x y : uint256) : uint256 :=
  words_to_uint256 (truncating_mul_constexpr (uint256_to_words x)
                                              (uint256_to_words y) 4).

(** * Long Division (single-word divisor)

    Models the C++ long_div function which divides an M-word number
    by a single-word divisor.

    C++ reference:
      constexpr uint64_t long_div(size_t m, uint64_t const *u, uint64_t v, uint64_t *quot) {
          auto r = div(0, u[m - 1], v);
          quot[m - 1] = r.quot;
          for (auto i = static_cast<intmax_t>(m) - 2; i >= 0; i--) {
              r = div(r.rem, u[i], v);
              quot[i] = r.quot;
          }
          return r.rem;
      }
*)

(** Result of long division *)
Record long_div_result := mk_long_div_result {
  ld_quot : words;
  ld_rem : uint64
}.

(** Process words from most significant to least significant.
    Input: us in little-endian order, we use fold_right semantics to process
    from the tail (MSW) toward the head (LSW). *)
Fixpoint long_div_fold (us : words) (v : uint64) (rem : uint64) : long_div_result :=
  match us with
  | [] => mk_long_div_result [] rem
  | u :: rest =>
      (* First process more significant words (rest) *)
      let rec_result := long_div_fold rest v rem in
      (* Then divide this word using remainder from more significant *)
      let r := div64 (ld_rem rec_result) u v in
      mk_long_div_result (quot64 r :: ld_quot rec_result) (rem64 r)
  end.

(** long_div: divide word list by single word.
    Input is little-endian, so we reverse to process MSW first,
    then reverse quotient back to little-endian. *)
Definition long_div (us : words) (v : uint64) : long_div_result :=
  let r := long_div_fold (rev us) v 0 in
  mk_long_div_result (rev (ld_quot r)) (ld_rem r).

(** ** Correctness Properties for Multi-Word Operations *)

(** *** Helper Lemmas for addc64 Carry Computation *)

(** When adding with carry, the result value is correct regardless of bounds *)
Lemma addc64_value_correct : forall lhs rhs cin,
  to_Z64 (value64 (addc64 lhs rhs cin)) =
  (to_Z64 lhs + to_Z64 rhs + (if cin then 1 else 0)) mod modulus64.
Proof.
  intros. unfold addc64, value64, to_Z64, from_Z64, normalize64, modulus64.
  simpl. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

(** Boolean carry output can be converted to integer *)
Definition carry_to_Z (c : bool) : Z := if c then 1 else 0.

(** Carry propagation: when adding a, b, cin, the carry out is 1 iff sum >= modulus *)
Lemma addc64_carry_value : forall lhs rhs cin,
  0 <= to_Z64 lhs < modulus64 ->
  0 <= to_Z64 rhs < modulus64 ->
  carry_to_Z (carry64 (addc64 lhs rhs cin)) =
    (to_Z64 lhs + to_Z64 rhs + carry_to_Z cin) / modulus64.
Proof.
  intros lhs rhs cin Hlhs Hrhs.
  unfold carry_to_Z.
  destruct (carry64 (addc64 lhs rhs cin)) eqn:Hcarry.
  - (* carry = true *)
    apply addc64_carry_correct in Hcarry; [|assumption|assumption].
    unfold to_Z64 in *.
Admitted.
(*     destruct cin; simpl in *. *)
(*     + assert (lhs + rhs + 1 >= modulus64) by lia. *)
(*       assert (lhs + rhs + 1 < 2 * modulus64) by (unfold modulus64 in *; lia). *)
(*       rewrite Z.div_small_iff in *; [|unfold modulus64; lia]. *)
(*       destruct H0; [lia|]. *)
(*       apply Z.div_unique with (r := lhs + rhs + 1 - modulus64); lia. *)
(*     + assert (lhs + rhs >= modulus64) by lia. *)
(*       assert (lhs + rhs < 2 * modulus64) by (unfold modulus64 in *; lia). *)
(*       apply Z.div_unique with (r := lhs + rhs - modulus64); lia. *)
(*   - (* carry = false *) *)
(*     unfold addc64 in Hcarry. simpl in Hcarry. *)
(*     unfold to_Z64, normalize64, modulus64 in *. *)
(*     apply Bool.orb_false_elim in Hcarry. *)
(*     destruct Hcarry as [H1 H2]. *)
(*     apply Z.ltb_ge in H1. *)
(*     apply Z.ltb_ge in H2. *)
(*     destruct cin; simpl in *. *)
(*     + assert ((lhs + rhs) mod 2^64 + 1 >= (lhs + rhs) mod 2^64) by lia. *)
(*       destruct (Z_lt_ge_dec (lhs + rhs) (2^64)) as [Hno_ov | Hov]. *)
(*       * rewrite Z.mod_small in H2 by lia. *)
(*         rewrite Z.mod_small in H1 by lia. *)
(*         rewrite Z.div_small; lia. *)
(*       * (* overflow on first add: sum mod M < lhs, but H1 says sum mod M >= lhs *) *)
(*         rewrite Z.mod_eq in H1 by lia. *)
(*         assert ((lhs + rhs) / 2^64 = 1) by (apply Z.div_unique with (r := lhs + rhs - 2^64); lia). *)
(*         lia. *)
(*     + destruct (Z_lt_ge_dec (lhs + rhs) (2^64)) as [Hno_ov | Hov]. *)
(*       * rewrite Z.div_small; lia. *)
(*       * rewrite Z.mod_eq in H1 by lia. *)
(*         assert ((lhs + rhs) / 2^64 = 1) by (apply Z.div_unique with (r := lhs + rhs - 2^64); lia). *)
(*         lia. *)
(* Qed. *)

(** *** mulx64 Bounds Lemmas *)

(** mulx64 high result is bounded *)
Lemma mulx64_hi_bounded : forall x y,
  0 <= x < modulus64 ->
  0 <= y < modulus64 ->
  0 <= to_Z64 (hi (mulx64 x y)) < modulus64.
Proof.
Admitted.
(*   intros x y Hx Hy. *)
(*   unfold mulx64, hi, from_Z64, to_Z64, modulus64 in *. *)
(*   split. *)
(*   - apply Z.shiftr_nonneg. lia. *)
(*   - rewrite Z.shiftr_div_pow2 by lia. *)
(*     apply Z.div_lt_upper_bound; [lia|]. *)
(*     assert (x * y < 2^64 * 2^64) by lia. *)
(*     rewrite <- Z.pow_add_r by lia. simpl. lia. *)
(* Qed. *)

(** mulx64 low result is bounded *)
Lemma mulx64_lo_bounded : forall x y,
  0 <= x < modulus64 ->
  0 <= y < modulus64 ->
  0 <= to_Z64 (lo (mulx64 x y)) < modulus64.
Proof.
Admitted.
(*   intros x y Hx Hy. *)
(*   unfold mulx64, lo, from_Z64, to_Z64, normalize64, modulus64 in *. *)
(*   apply Z.mod_pos_bound. lia. *)
(* Qed. *)

(** *** Inner Loop Invariant *)

(** The inner loop maintains an invariant about partial products.
    After processing x[0..k-1] * y, we have accumulated the contribution
    into result[j..j+k-1] with a carry for position j+k. *)

(** Inner loop result maintains word validity *)
Lemma constexpr_inner_loop_valid : forall xs y result j i R carry,
  words_valid xs ->
  0 <= y < modulus64 ->
  0 <= carry < modulus64 ->
  words_valid result ->
  length result = R ->
  words_valid (fst (constexpr_inner_loop xs y result j i R carry)).
Proof.
Admitted.
(*   induction xs as [|x rest IH]; intros y result j i R carry Hxs Hy Hcarry Hresult HR. *)
(*   - simpl. assumption. *)
(*   - simpl. *)
(*     destruct (i + j <? R)%nat eqn:Hlt. *)
(*     + apply Nat.ltb_lt in Hlt. *)
(*       inversion Hxs as [|x' rest' Hx Hrest]; subst. *)
(*       apply IH; try assumption. *)
(*       * (* carry from s2 is valid *) *)
(*         unfold addc64, value64, from_Z64, normalize64, modulus64. simpl. *)
(*         apply Z.mod_pos_bound. lia. *)
(*       * (* set_word preserves validity *) *)
(*         unfold words_valid, set_word. *)
(*         apply Forall_forall. intros w Hw. *)
(*         { (* New result after set_word is valid *) *)
(*           assert (Hvalid_val: 0 <= value64 (addc64 (value64 (addc64 (lo (mulx64 x y)) *)
(*                               (get_word result (i + j)) false)) carry false) < modulus64). *)
(*           { unfold addc64, value64, from_Z64, normalize64, modulus64. simpl. *)
(*             apply Z.mod_pos_bound. lia. } *)
(*           (* The new word list contains either the new value or existing words *) *)
(*           clear IH. *)
(*           generalize dependent i. *)
(*           generalize dependent result. *)
(*           induction result as [|r0 rrest IHr]; intros Hresult HR i Hlt Hw. *)
(*           - simpl in Hw. destruct Hw. *)
(*           - destruct i. *)
(*             + simpl in Hw. destruct Hw as [Heq | Hin]. *)
(*               * subst. unfold modulus64 in Hvalid_val. assumption. *)
(*               * inversion Hresult; subst. rewrite Forall_forall in H2. *)
(*                 apply H2. assumption. *)
(*             + simpl in Hw. destruct Hw as [Heq | Hin]. *)
(*               * subst. inversion Hresult; subst. assumption. *)
(*               * inversion Hresult; subst. *)
(*                 eapply IHr; try eassumption. *)
(*                 -- simpl in HR. lia. *)
(*                 -- simpl in Hlt. lia. *)
(*         } *)
(*       * rewrite set_word_length. assumption. *)
(*     + simpl. assumption. *)
(* Qed. *)

(** Inner loop preserves result length *)
Lemma constexpr_inner_loop_length : forall xs y result j i R carry,
  length (fst (constexpr_inner_loop xs y result j i R carry)) = length result.
Proof.
Admitted.
(*   induction xs as [|x rest IH]; intros y result j i R carry. *)
(*   - simpl. reflexivity. *)
(*   - simpl. *)
(*     destruct (i + j <? R)%nat eqn:Hlt. *)
(*     + rewrite IH. rewrite set_word_length. reflexivity. *)
(*     + reflexivity. *)
(* Qed. *)

(** *** Outer Loop Invariant *)

(** Outer loop result maintains word validity *)
Lemma constexpr_outer_loop_valid : forall xs ys result j R,
  words_valid xs ->
  words_valid ys ->
  words_valid result ->
  length result = R ->
  words_valid (constexpr_outer_loop xs ys result j R).
Proof.
Admitted.
(*   intros xs ys. revert j. *)
(*   induction ys as [|y rest IH]; intros j result R Hxs Hys Hresult HR. *)
(*   - simpl. assumption. *)
(*   - simpl. *)
(*     inversion Hys as [|y' rest' Hy Hrest]; subst. *)
(*     destruct (constexpr_inner_loop xs y result j 0 R 0) as [new_result carry] eqn:Hinner. *)
(*     apply IH; try assumption. *)
(*     + (* final_result is valid *) *)
(*       destruct (j + length xs <? R)%nat eqn:Hlt. *)
(*       * apply Nat.ltb_lt in Hlt. *)
(*         unfold words_valid. apply Forall_forall. *)
(*         intros w Hw. *)
(*         assert (Hnew_valid: words_valid new_result). *)
(*         { assert (H := constexpr_inner_loop_valid xs y result j 0 R 0 *)
(*                         Hxs Hy ltac:(unfold modulus64; lia) Hresult HR). *)
(*           rewrite Hinner in H. simpl in H. assumption. } *)
(*         assert (Hcarry_bound: 0 <= carry < modulus64). *)
(*         { (* carry is the second component of inner_loop result *) *)
(*           clear IH. *)
(*           revert j result Hresult HR Hinner. *)
(*           induction xs as [|x xrest IHx]; intros j result Hresult HR Hinner. *)
(*           - simpl in Hinner. inversion Hinner. unfold modulus64. lia. *)
(*           - simpl in Hinner. *)
(*             destruct (0 + j <? R)%nat eqn:Hlt'. *)
(*             + (* inner loop continues *) *)
(*               inversion Hxs; subst. *)
(*               eapply IHx; try eassumption. *)
(*               * apply (constexpr_inner_loop_valid [x] y result j 0 R 0). *)
(*                 -- constructor; [assumption|constructor]. *)
(*                 -- assumption. *)
(*                 -- unfold modulus64; lia. *)
(*                 -- assumption. *)
(*                 -- assumption. *)
(*               * rewrite set_word_length. assumption. *)
(*             + inversion Hinner. unfold modulus64. lia. *)
(*         } *)
(*         generalize dependent (j + length xs). *)
(*         intros idx Hlt Hw. *)
(*         destruct idx. *)
(*         -- simpl in Hw. destruct Hw as [Heq | Hin]. *)
(*            ++ subst. assumption. *)
(*            ++ rewrite Forall_forall in Hnew_valid. apply Hnew_valid. assumption. *)
(*         -- simpl in Hw. destruct Hw as [Heq | Hin]. *)
(*            ++ subst. destruct new_result; simpl in *. *)
(*               ** destruct Hin. *)
(*               ** inversion Hnew_valid; subst. assumption. *)
(*            ++ clear Hlt. *)
(*               revert new_result Hnew_valid Hw idx. *)
(*               induction new_result as [|n0 nrest IHn]; intros Hnew_valid Hw idx. *)
(*               ** simpl in Hw. destruct Hw. *)
(*               ** destruct idx. *)
(*                  --- simpl in Hw. destruct Hw as [Heq | Hin]. *)
(*                      +++ subst. assumption. *)
(*                      +++ inversion Hnew_valid; subst. *)
(*                          rewrite Forall_forall in H2. apply H2. assumption. *)
(*                  --- simpl in Hw. destruct Hw as [Heq | Hin]. *)
(*                      +++ subst. inversion Hnew_valid; subst. assumption. *)
(*                      +++ inversion Hnew_valid; subst. eapply IHn; eassumption. *)
(*       * assert (H := constexpr_inner_loop_valid xs y result j 0 R 0 *)
(*                       Hxs Hy ltac:(unfold modulus64; lia) Hresult HR). *)
(*         rewrite Hinner in H. simpl in H. assumption. *)
(*     + destruct (j + length xs <? R)%nat. *)
(*       * rewrite set_word_length. *)
(*         assert (H := constexpr_inner_loop_length xs y result j 0 R 0). *)
(*         rewrite Hinner in H. simpl in H. rewrite H. assumption. *)
(*       * assert (H := constexpr_inner_loop_length xs y result j 0 R 0). *)
(*         rewrite Hinner in H. simpl in H. rewrite H. assumption. *)
(* Qed. *)

(* (** Outer loop preserves result length *) *)
(* Lemma constexpr_outer_loop_length : forall xs ys result j R, *)
(*   length result = R -> *)
(*   length (constexpr_outer_loop xs ys result j R) = R. *)
(* Proof. *)
(*   intros xs ys. revert xs. *)
(*   induction ys as [|y rest IH]; intros xs j result R HR. *)
(*   - simpl. assumption. *)
(*   - simpl. *)
(*     destruct (constexpr_inner_loop xs y result j 0 R 0) as [new_result carry] eqn:Hinner. *)
(*     apply IH. *)
(*     destruct (j + length xs <? R)%nat. *)
(*     + rewrite set_word_length. *)
(*       assert (H := constexpr_inner_loop_length xs y result j 0 R 0). *)
(*       rewrite Hinner in H. simpl in H. rewrite H. assumption. *)
(*     + assert (H := constexpr_inner_loop_length xs y result j 0 R 0). *)
(*       rewrite Hinner in H. simpl in H. rewrite H. assumption. *)
(* Qed. *)

(** *** Truncating Multiplication Correctness *)

(** truncating_mul_constexpr produces valid word list *)
Lemma truncating_mul_constexpr_valid : forall xs ys R,
  words_valid xs ->
  words_valid ys ->
  words_valid (truncating_mul_constexpr xs ys R).
Proof.
Admitted.
(*   intros xs ys R Hxs Hys. *)
(*   unfold truncating_mul_constexpr. *)
(*   apply constexpr_outer_loop_valid; try assumption. *)
(*   - apply extend_words_valid. *)
(*   - apply extend_words_length. *)
(* Qed. *)

(** truncating_mul_constexpr produces correct length *)
Lemma truncating_mul_constexpr_length : forall xs ys R,
  length (truncating_mul_constexpr xs ys R) = R.
Proof.
Admitted.
(*   intros xs ys R. *)
(*   unfold truncating_mul_constexpr. *)
(*   apply constexpr_outer_loop_length. *)
(*   apply extend_words_length. *)
(* Qed. *)

(** Main correctness theorem for truncating multiplication (stated but proof is complex) *)
Theorem truncating_mul256_constexpr_correct : forall x y,
  words_valid (uint256_to_words x) ->
  words_valid (uint256_to_words y) ->
  to_Z256 (truncating_mul256_constexpr x y) = (to_Z256 x * to_Z256 y) mod 2^256.
Proof.
  intros x y Hx Hy.
  unfold truncating_mul256_constexpr.
  (* The proof requires showing that the nested loops correctly accumulate
     partial products. This is a complex induction over both loops.
     For now, we admit this theorem as the main goal is to establish
     the model structure. *)
Admitted.

(** *** Long Division Correctness *)

(** long_div_fold produces quotient with same length as input *)
Lemma long_div_fold_length : forall us v rem,
  length (ld_quot (long_div_fold us v rem)) = length us.
Proof.
  induction us as [|u rest IH]; intros v rem.
  - simpl. reflexivity.
  - simpl. rewrite IH. simpl. reflexivity.
Qed.

(** long_div produces quotient with same length as input *)
Lemma long_div_length : forall us v,
  length (ld_quot (long_div us v)) = length us.
Proof.
  intros us v.
  unfold long_div.
Admitted.
(*   rewrite rev_length. *)
(*   rewrite long_div_fold_length. *)
(*   rewrite rev_length. *)
(*   reflexivity. *)
(* Qed. *)

(** Correctness of long_div_fold: processes MSW-first (reversed list) *)
Lemma long_div_fold_correct : forall us v rem,
  0 < v < modulus64 ->
  0 <= rem < v ->
  words_valid us ->
  let r := long_div_fold us v rem in
  (* The division invariant: rem * base^n + u = quot * v + rem' *)
  rem * modulus_words (length us) + to_Z_words us =
    to_Z_words (ld_quot r) * to_Z64 v + to_Z64 (ld_rem r) /\
  0 <= to_Z64 (ld_rem r) < to_Z64 v.
Proof.
Admitted.
(*   induction us as [|u rest IH]; intros v rem Hv Hrem Hvalid. *)
(*   - simpl. split. *)
(*     + unfold modulus_words, words_bits. simpl. ring. *)
(*     + unfold to_Z64. assumption. *)
(*   - simpl. *)
(*     inversion Hvalid as [|u' rest' Hu Hrest]; subst. *)
(*     specialize (IH v rem Hv Hrem Hrest). *)
(*     destruct IH as [IHeq IHrem]. *)
(*     set (rec_result := long_div_fold rest v rem) in *. *)
(*     set (r := div64 (ld_rem rec_result) u v). *)
(*     split. *)
(*     + (* Main equation *) *)
(*       unfold modulus_words, words_bits in *. *)
(*       simpl length. *)
(*       rewrite Nat2Z.inj_succ. *)
(*       replace (Z.succ (Z.of_nat (length rest)) * 64) with *)
(*               (64 + Z.of_nat (length rest) * 64) by ring. *)
(*       rewrite Z.pow_add_r by lia. *)
(*       unfold to_Z_words at 1. fold to_Z_words. *)
(*       unfold to_Z64 at 1 3. *)
(*       (* Use the division equation for div64 *) *)
(*       assert (Hdiv: let u128 := Z.shiftl (to_Z64 (ld_rem rec_result)) 64 + to_Z64 u in *)
(*                     u128 = to_Z64 (quot64 r) * to_Z64 v + to_Z64 (rem64 r) /\ *)
(*                     to_Z64 (rem64 r) < to_Z64 v). *)
(*       { apply div64_correct. *)
(*         - unfold to_Z64. lia. *)
(*         - unfold div64_precondition, to_Z64. *)
(*           assert (0 <= ld_rem rec_result < v) by (unfold to_Z64 in IHrem; lia). *)
(*           lia. } *)
(*       destruct Hdiv as [Hdiv_eq Hdiv_rem]. *)
(*       unfold r at 2. simpl. *)
(*       rewrite Z.shiftl_mul_pow2 in Hdiv_eq by lia. *)
(*       unfold to_Z64 in Hdiv_eq at 1. *)
(*       (* Now relate to the recursive result *) *)
(*       rewrite IHeq. *)
(*       unfold to_Z64 at 4. *)
(*       (* Algebraic manipulation *) *)
(*       assert (Hpow: 2^64 = modulus64) by reflexivity. *)
(*       rewrite Hpow in Hdiv_eq. *)
(*       unfold to_Z64 at 3 4 5. *)
(*       ring_simplify. *)
(*       rewrite Hdiv_eq. *)
(*       ring. *)
(*     + (* Remainder bound *) *)
(*       unfold r. *)
(*       assert (Hdiv: to_Z64 (rem64 (div64 (ld_rem rec_result) u v)) < to_Z64 v). *)
(*       { apply div64_correct. *)
(*         - unfold to_Z64. lia. *)
(*         - unfold div64_precondition, to_Z64. *)
(*           assert (0 <= ld_rem rec_result < v) by (unfold to_Z64 in IHrem; lia). *)
(*           lia. } *)
(*       unfold to_Z64 in *. split; [|assumption]. *)
(*       unfold div64, rem64, from_Z64. *)
(*       apply Z.mod_pos_bound. lia. *)
(* Qed. *)

(** Main correctness theorem for long_div *)
Theorem long_div_correct : forall us v,
  words_valid us ->
  0 < v < modulus64 ->
  let r := long_div us v in
  to_Z_words us = to_Z_words (ld_quot r) * to_Z64 v + to_Z64 (ld_rem r) /\
  0 <= to_Z64 (ld_rem r) < to_Z64 v.
Proof.
Admitted.
(*   intros us v Hvalid Hv. *)
(*   unfold long_div. *)
(*   (* Use correctness of long_div_fold on reversed input *) *)
(*   assert (Hrev_valid: words_valid (rev us)). *)
(*   { unfold words_valid in *. apply Forall_rev. assumption. } *)
(*   assert (H := long_div_fold_correct (rev us) v 0 Hv ltac:(lia) Hrev_valid). *)
(*   destruct H as [Heq Hrem]. *)
(*   rewrite rev_length in Heq. *)
(*   (* The reversed quotient, when reversed back, gives the correct value *) *)
(*   (* This requires showing that reversing preserves the mathematical value *)
(*      when the word positions are also reversed *) *)
(*   split. *)
(*   - (* Main division equation *) *)
(*     (* This proof requires relating to_Z_words on reversed lists *) *)
(*     (* For now we admit it *) *)
(*     admit. *)
(*   - (* Remainder bound *) *)
(*     assumption. *)
(* Admitted. *)

(** ** Notes on Implementation *)

(**
   The specifications in this file directly mirror the _constexpr versions
   from uint256.hpp. The _intrinsic versions using compiler built-ins or
   inline assembly should produce identical results, which would be verified
   by testing or assumed as a compiler correctness property.

   Key verification strategy:
   1. Prove these specifications are correct mathematical operations
   2. Prove the multi-word operations (like 256-bit add) correctly chain
      these primitives together
   3. Test or assume that the actual C++ intrinsics match these specs
*)
