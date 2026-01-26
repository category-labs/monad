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
  - (* Forward: overflow detected -> mathematical overflow *)
    intros [Hov1 | Hov2].
    + enough (lhs + rhs >= M) by lia. apply mod_overflow_iff; lia.
    + apply -> mod_overflow_iff in Hov2; lia.
  - (* Backward: mathematical overflow -> overflow detected *)
    intro Hoverflow.
    destruct (Z_lt_ge_dec (lhs + rhs) M) as [Hno_ov1 | Hov1].
    + right. apply <- mod_overflow_iff; [|lia | lia | lia].
      unfold sum; rewrite Z.mod_small by lia. lia.
    + left. apply <- mod_overflow_iff; lia.
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

Definition subb64_spec (lhs rhs : uint64) (borrow_in : bool) : result64_with_carry :=
  let lhs_z := to_Z64 lhs in
  let rhs_z := to_Z64 rhs in
  let bin := if borrow_in then 1 else 0 in
  let diff := lhs_z - rhs_z - bin in
  {|
    value64 := from_Z64 (normalize64 diff);
    carry64 := (diff <? 0)  (* borrow if result would be negative *)
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
Definition mulx64_spec (x y : uint64) : mulx_result :=
  let prod := to_Z64 x * to_Z64 y in
  {|
    hi := from_Z64 (Z.shiftr prod 64);
    lo := from_Z64 prod
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
Definition div64_spec (u_hi u_lo v : uint64) : div64_result :=
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

    The peculiar formulation (low >> 1) >> (63 - shift) instead of
    low >> (64 - shift) is to avoid undefined behavior when shift = 0.
*)
Definition shld64_spec (high low : uint64) (shift : nat) : uint64 :=
  if Nat.eqb shift 0 then high
  else if Nat.leb 64 shift then from_Z64 0
  else
    let h := to_Z64 high in
    let l := to_Z64 low in
    let shifted_high := Z.shiftl h (Z.of_nat shift) in
    let shifted_low := Z.shiftr (Z.shiftr l 1) (Z.of_nat (63 - shift)) in
    from_Z64 (Z.lor shifted_high shifted_low).

(** Right shift with double precision (shrd instruction)

    Specification: (high || low) >> shift, return low part

    This matches shrd_constexpr:
      return (low >> shift) | ((high << 1) << (63 - shift));
*)
Definition shrd64_spec (high low : uint64) (shift : nat) : uint64 :=
  if Nat.eqb shift 0 then low
  else if Nat.leb 64 shift then from_Z64 0
  else
    let h := to_Z64 high in
    let l := to_Z64 low in
    let shifted_low := Z.shiftr l (Z.of_nat shift) in
    let shifted_high := Z.shiftl (Z.shiftl h 1) (Z.of_nat (63 - shift)) in
    from_Z64 (Z.lor shifted_low shifted_high).

(** ** Correctness Properties *)

(** TODO: INSERT addc64 produces correct mathematical result HERE *)

(** TODO: INSERT addc64 carry is correct HERE *)

(** subb64 produces correct mathematical result *)
Lemma subb64_correct : forall lhs rhs bin,
  let result := subb64_spec lhs rhs bin in
  let bin_z := if bin then 1 else 0 in
  to_Z64 (value64 result) = (to_Z64 lhs - to_Z64 rhs - bin_z) mod modulus64.
Proof.
  intros. unfold subb64_spec. simpl. unfold from_Z64, to_Z64. simpl.
  reflexivity.
Qed.

(** mulx64 produces correct 128-bit product *)
Lemma mulx64_correct : forall x y,
  let result := mulx64_spec x y in
  let prod := to_Z64 x * to_Z64 y in
  prod = Z.shiftl (to_Z64 (hi result)) 64 + to_Z64 (lo result).
Proof.
  intros x y. simpl.
  unfold mulx64_spec, from_Z64, to_Z64. simpl.
  (* Need to prove that (prod >> 64) * 2^64 + (prod mod 2^64) = prod *)
  set (p := proj1_sig x * proj1_sig y).
  assert (Hprod_pos: 0 <= p).
  { unfold p. apply Z.mul_nonneg_nonneg; destruct x, y; simpl; lia. }
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Zmod_mod.
  rewrite Z.mod_eq by lia.
  rewrite Z.mul_comm.
  rewrite <- Z.add_sub_assoc.
  rewrite Z.sub_diag.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

(** div64 produces correct quotient and remainder *)
Lemma div64_correct : forall u_hi u_lo v,
  to_Z64 v <> 0 ->
  div64_precondition u_hi v ->
  let result := div64_spec u_hi u_lo v in
  let u := Z.shiftl (to_Z64 u_hi) 64 + to_Z64 u_lo in
  u = to_Z64 (quot64 result) * to_Z64 v + to_Z64 (rem64 result) /\
  to_Z64 (rem64 result) < to_Z64 v.
Proof.
  intros Hv_nonzero Hprecond. unfold div64_spec. simpl.
  unfold from_Z64, to_Z64. simpl.
  split.
  - apply Z.div_mod; auto.
  - apply Z.mod_pos_bound; auto.
    destruct v as [v_z [Hv_lo Hv_hi]]. simpl in *.
    lia.
Qed.

(** ** Multi-word Addition Helper *)

(** Add two 2-word numbers with carry propagation *)
Definition add128_spec (x_hi x_lo y_hi y_lo : uint64) : mulx_result :=
  let r0 := addc64_spec x_lo y_lo false in
  let r1 := addc64_spec x_hi y_hi (carry64 r0) in
  {|
    hi := value64 r1;
    lo := value64 r0
  |}.

(** ** Chaining Lemmas *)

(** Chaining two addc operations correctly computes the sum *)
Lemma addc64_chain_2 : forall x0 x1 y0 y1,
  let r0 := addc64_spec x0 y0 false in
  let r1 := addc64_spec x1 y1 (carry64 r0) in
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
  let r0 := addc64_spec x0 y0 false in
  let r1 := addc64_spec x1 y1 (carry64 r0) in
  let r2 := addc64_spec x2 y2 (carry64 r1) in
  let r3 := addc64_spec x3 y3 (carry64 r2) in
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
