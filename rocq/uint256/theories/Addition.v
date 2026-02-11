(** * Multi-Word Addition via Carry Chaining

    This file proves correctness of multi-word addition implemented
    by chaining 64-bit add-with-carry (addc64) operations.
    These correspond to the adc_2 / adc_4 inline assembly functions
    in uint256.hpp.
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives.
Import ListNotations.
Open Scope Z_scope.

(** ** Helper Definitions *)

(** Boolean carry output can be converted to integer *)
Definition carry_to_Z (c : bool) : Z := if c then 1 else 0.

(** ** Carry Value Lemma *)

(** Carry propagation: when adding a, b, cin, the carry out equals the quotient *)
Lemma addc64_carry_value : forall lhs rhs cin,
  0 <= to_Z64 lhs < modulus64 ->
  0 <= to_Z64 rhs < modulus64 ->
  carry_to_Z (carry64 (addc64 lhs rhs cin)) =
    (to_Z64 lhs + to_Z64 rhs + carry_to_Z cin) / modulus64.
Proof.
  intros lhs rhs cin Hlhs Hrhs.
  unfold carry_to_Z.
  destruct (carry64 (addc64 lhs rhs cin)) eqn:Hcarry.
  - (* carry = true: sum >= modulus64, so div = 1 *)
    apply addc64_carry_correct in Hcarry; [|assumption|assumption].
    unfold to_Z64 in *. destruct cin.
    + apply (Z.div_unique _ _ _ (lhs + rhs + 1 - modulus64)).
      left. unfold modulus64 in *; lia. unfold modulus64 in *; lia.
    + apply (Z.div_unique _ _ _ (lhs + rhs - modulus64)).
      left. unfold modulus64 in *; lia. unfold modulus64 in *; lia.
  - (* carry = false: sum < modulus64, so div = 0 *)
    unfold addc64 in Hcarry. unfold carry64 in Hcarry.
    apply Bool.orb_false_elim in Hcarry. destruct Hcarry as [H1 H2].
    apply Z.ltb_ge in H1. apply Z.ltb_ge in H2.
    unfold to_Z64, normalize64, modulus64 in *.
    assert (Hno_ov1: lhs + rhs < 2^64).
    { destruct (Z_lt_ge_dec (lhs + rhs) (2^64)) as [Hlt|Hge]; [assumption|].
      exfalso. apply mod_overflow_iff in Hge; [|lia|lia|lia]. lia. }
    destruct cin.
    + (* cin=true *)
      symmetry. apply Z.div_small.
      destruct (Z_lt_ge_dec (lhs + rhs + 1) (2^64)); [lia|].
      assert (lhs + rhs + 1 = 2^64) by lia.
      rewrite Z.mod_small in H2 by lia.
      rewrite H in H2. rewrite Z_mod_same in H2 by lia. lia.
    + (* cin=false *)
      symmetry. apply Z.div_small. lia.
Qed.

(** ** Chaining Lemmas *)

(** Chaining two addc operations correctly computes the 128-bit sum *)
Lemma addc64_chain_2 : forall x0 x1 y0 y1,
  0 <= x0 < modulus64 -> 0 <= x1 < modulus64 ->
  0 <= y0 < modulus64 -> 0 <= y1 < modulus64 ->
  let r0 := addc64 x0 y0 false in
  let r1 := addc64 x1 y1 (carry64 r0) in
  let x := Z.shiftl (to_Z64 x1) 64 + to_Z64 x0 in
  let y := Z.shiftl (to_Z64 y1) 64 + to_Z64 y0 in
  let result := Z.shiftl (to_Z64 (value64 r1)) 64 + to_Z64 (value64 r0) in
  result = (x + y) mod (2^128).
Proof.
  intros x0 x1 y0 y1 Hx0 Hx1 Hy0 Hy1. cbv zeta.
  set (r0 := addc64 x0 y0 false). set (r1 := addc64 x1 y1 (carry64 r0)).
  rewrite !Z.shiftl_mul_pow2 by lia. unfold to_Z64.
  pose proof (addc64_value_correct x0 y0 false) as Hv0.
  change (addc64 x0 y0 false) with r0 in Hv0.
  unfold to_Z64 in Hv0. simpl (if false then 1 else 0) in Hv0.
  pose proof (addc64_carry_value x0 y0 false
    (conj (proj1 Hx0) (proj2 Hx0)) (conj (proj1 Hy0) (proj2 Hy0))) as Hc0.
  change (addc64 x0 y0 false) with r0 in Hc0.
  unfold to_Z64, carry_to_Z in Hc0. simpl (if false then 1 else 0) in Hc0.
  pose proof (addc64_value_correct x1 y1 (carry64 r0)) as Hv1.
  change (addc64 x1 y1 (carry64 r0)) with r1 in Hv1. unfold to_Z64 in Hv1.
  set (c0 := if carry64 r0 then 1 else 0) in *.
  rewrite Z.add_0_r in Hv0, Hc0.
  replace modulus64 with (2^64) in * by reflexivity.
  rewrite Hv0, Hv1, Hc0.
  set (M := 2^64).
  replace (2^128) with (M * M) by (unfold M; ring).
  assert (HM: 0 < M) by (unfold M; lia).
  pose proof (Z.mod_pos_bound (x0 + y0) M HM) as Hv0_bound.
  pose proof (Z.mod_pos_bound (x1 + y1 + (x0 + y0) / M) M HM) as Hv1_bound.
  pose proof (Z_div_mod_eq_full (x0 + y0) M) as Hdm.
  assert (Hrewrite: x1 * M + x0 + (y1 * M + y0) =
    (x1 + y1 + (x0 + y0) / M) * M + (x0 + y0) mod M) by nia.
  rewrite Hrewrite. symmetry.
  rewrite (Z_div_mod_eq_full (x1 + y1 + (x0 + y0) / M) M) at 1.
  replace ((M * ((x1 + y1 + (x0 + y0) / M) / M) +
    (x1 + y1 + (x0 + y0) / M) mod M) * M + (x0 + y0) mod M) with
    ((x1 + y1 + (x0 + y0) / M) / M * (M * M) +
     ((x1 + y1 + (x0 + y0) / M) mod M * M + (x0 + y0) mod M)) by ring.
  rewrite Z.add_comm. rewrite Z.mod_add by lia.
  apply Z.mod_small. split; [nia|nia].
Qed.

(** Chaining four addc operations correctly computes the 256-bit sum *)
Lemma addc64_chain_4 : forall x0 x1 x2 x3 y0 y1 y2 y3,
  0 <= x0 < modulus64 -> 0 <= x1 < modulus64 ->
  0 <= x2 < modulus64 -> 0 <= x3 < modulus64 ->
  0 <= y0 < modulus64 -> 0 <= y1 < modulus64 ->
  0 <= y2 < modulus64 -> 0 <= y3 < modulus64 ->
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
  intros x0 x1 x2 x3 y0 y1 y2 y3 Hx0 Hx1 Hx2 Hx3 Hy0 Hy1 Hy2 Hy3.
  cbv zeta.
  set (r0 := addc64 x0 y0 false). set (r1 := addc64 x1 y1 (carry64 r0)).
  set (r2 := addc64 x2 y2 (carry64 r1)). set (r3 := addc64 x3 y3 (carry64 r2)).
  rewrite !Z.shiftl_mul_pow2 by lia. unfold to_Z64.
  replace modulus64 with (2^64) in * by reflexivity.
  set (M := 2^64) in *.
  assert (HM: 0 < M) by (unfold M; lia).
  (* Value equations *)
  pose proof (addc64_value_correct x0 y0 false) as Hv0.
  change (addc64 x0 y0 false) with r0 in Hv0.
  unfold to_Z64 in Hv0. simpl (if false then 1 else 0) in Hv0.
  rewrite Z.add_0_r in Hv0. change modulus64 with M in Hv0.
  (* Carry equations *)
  pose proof (addc64_carry_value x0 y0 false
    (conj (proj1 Hx0) (proj2 Hx0)) (conj (proj1 Hy0) (proj2 Hy0))) as Hc0.
  change (addc64 x0 y0 false) with r0 in Hc0.
  unfold to_Z64, carry_to_Z in Hc0. simpl (if false then 1 else 0) in Hc0.
  rewrite Z.add_0_r in Hc0. change modulus64 with M in Hc0.
  set (c0 := if carry64 r0 then 1 else 0) in *.
  (* Stage 1 *)
  pose proof (addc64_value_correct x1 y1 (carry64 r0)) as Hv1.
  change (addc64 x1 y1 (carry64 r0)) with r1 in Hv1.
  unfold to_Z64 in Hv1. change modulus64 with M in Hv1. fold c0 in Hv1.
  pose proof (addc64_carry_value x1 y1 (carry64 r0)
    (conj (proj1 Hx1) (proj2 Hx1)) (conj (proj1 Hy1) (proj2 Hy1))) as Hc1.
  change (addc64 x1 y1 (carry64 r0)) with r1 in Hc1.
  unfold to_Z64, carry_to_Z in Hc1. change modulus64 with M in Hc1. fold c0 in Hc1.
  set (c1 := if carry64 r1 then 1 else 0) in *.
  (* Stage 2 *)
  pose proof (addc64_value_correct x2 y2 (carry64 r1)) as Hv2.
  change (addc64 x2 y2 (carry64 r1)) with r2 in Hv2.
  unfold to_Z64 in Hv2. change modulus64 with M in Hv2. fold c1 in Hv2.
  pose proof (addc64_carry_value x2 y2 (carry64 r1)
    (conj (proj1 Hx2) (proj2 Hx2)) (conj (proj1 Hy2) (proj2 Hy2))) as Hc2.
  change (addc64 x2 y2 (carry64 r1)) with r2 in Hc2.
  unfold to_Z64, carry_to_Z in Hc2. change modulus64 with M in Hc2. fold c1 in Hc2.
  set (c2 := if carry64 r2 then 1 else 0) in *.
  (* Stage 3 *)
  pose proof (addc64_value_correct x3 y3 (carry64 r2)) as Hv3.
  change (addc64 x3 y3 (carry64 r2)) with r3 in Hv3.
  unfold to_Z64 in Hv3. change modulus64 with M in Hv3. fold c2 in Hv3.
  (* Rewrite values *)
  replace (2^128) with (M*M) in * by (unfold M; ring).
  replace (2^192) with (M*M*M) in * by (unfold M; ring).
  replace (2^256) with (M*M*M*M) by (unfold M; ring).
  rewrite Hv0, Hv1, Hv2, Hv3. rewrite Hc0, Hc1, Hc2 in *.
  (* Introduce short names for quotients *)
  set (q0 := (x0 + y0) / M) in *.
  set (q1 := (x1 + y1 + q0) / M) in *.
  set (q2 := (x2 + y2 + q1) / M) in *.
  set (q3 := (x3 + y3 + q2) / M) in *.
  (* Division-modulus equations *)
  assert (Hdm0: x0 + y0 = M * q0 + (x0 + y0) mod M) by (apply Z_div_mod_eq_full).
  assert (Hdm1: x1 + y1 + q0 = M * q1 + (x1 + y1 + q0) mod M) by (apply Z_div_mod_eq_full).
  assert (Hdm2: x2 + y2 + q1 = M * q2 + (x2 + y2 + q1) mod M) by (apply Z_div_mod_eq_full).
  assert (Hdm3: x3 + y3 + q2 = M * q3 + (x3 + y3 + q2) mod M) by (apply Z_div_mod_eq_full).
  (* Key sum decomposition *)
  assert (Hsum: x3 * (M * M * M) + x2 * (M * M) + x1 * M + x0 +
    (y3 * (M * M * M) + y2 * (M * M) + y1 * M + y0) =
    q3 * (M * M * M * M) + ((x3 + y3 + q2) mod M * (M * M * M) +
    (x2 + y2 + q1) mod M * (M * M) + (x1 + y1 + q0) mod M * M +
    (x0 + y0) mod M)) by nia.
  rewrite Hsum. symmetry. rewrite Z.add_comm. rewrite Z.mod_add by lia.
  apply Z.mod_small.
  pose proof (Z.mod_pos_bound (x0 + y0) M HM) as Hb0.
  pose proof (Z.mod_pos_bound (x1 + y1 + q0) M HM) as Hb1.
  pose proof (Z.mod_pos_bound (x2 + y2 + q1) M HM) as Hb2.
  pose proof (Z.mod_pos_bound (x3 + y3 + q2) M HM) as Hb3.
  split; [nia|nia].
Qed.
