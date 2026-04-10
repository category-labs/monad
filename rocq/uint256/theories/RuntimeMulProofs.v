(** * Runtime Multiplication Proofs

    Correctness proofs for the runtime multiplication model
    defined in RuntimeMul.v.

    Structure (bottom-up):
    1. Structural helpers (length, equivalence)
    2. Recursive helper correctness (mul_line_recur, mul_add_line_recur)
    3. Row-level correctness (mul_line, mul_add_line)
    4. General word-list theorem (truncating_mul_runtime)
    5. Main 256-bit theorem *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint Words WordsLemmas RuntimeMul.

Module MakeProofs (Import U64 : Uint64).
Include RuntimeMul.Make(U64).
Module WL := WordsLemmas.MakeProofs(U64).
Import WL.

Import ListNotations.
Open Scope Z_scope.

Local Coercion to_Z : t >-> Z.

(** * Local structural lemmas

    These are proved locally because [Include RuntimeMul.Make(U64)] and
    [Module WL := WordsLemmas.MakeProofs(U64)] instantiate [Words.Make]
    separately, so [WL.set_word_length] does not match the [set_word]
    used inside the model functions. *)

Lemma set_word_length_local : forall (ws : words) i v,
  length (set_word ws i v) = length ws.
Proof.
  induction ws as [|w rest IH]; intros i v; [reflexivity|].
  destruct i; simpl; [|rewrite IH]; reflexivity.
Qed.

Lemma extend_words_length_local : forall n,
  length (extend_words n) = n.
Proof. intros n. apply repeat_length. Qed.

Lemma get_word_eq_local : forall (ws : words) i,
  MakeProofs.get_word ws i = WL.get_word ws i.
Proof. reflexivity. Qed.

Lemma set_word_eq_local : forall (ws : words) i v,
  MakeProofs.set_word ws i v = WL.set_word ws i v.
Proof.
  induction ws as [|w rest IH]; intros i v; destruct i; cbn; f_equal; auto.
Qed.

Lemma extend_words_eq_local : forall n,
  MakeProofs.extend_words n = WL.extend_words n.
Proof. reflexivity. Qed.

Lemma get_set_word_same_local : forall ws i v,
  (i < length ws)%nat ->
  MakeProofs.get_word (MakeProofs.set_word ws i v) i = v.
Proof.
  intros ws i v Hi.
  rewrite set_word_eq_local, get_word_eq_local.
  apply WL.get_set_word_same. exact Hi.
Qed.

Lemma get_set_word_other_local : forall ws i j v,
  i <> j ->
  MakeProofs.get_word (MakeProofs.set_word ws i v) j =
  MakeProofs.get_word ws j.
Proof.
  intros ws i j v Hij.
  rewrite set_word_eq_local, !get_word_eq_local.
  apply WL.get_set_word_other. exact Hij.
Qed.

Lemma to_Z_words_set_word_local : forall ws i v,
  (i < length ws)%nat ->
  to_Z_words (MakeProofs.set_word ws i v) =
    to_Z_words ws
    - to_Z (MakeProofs.get_word ws i) * (base width) ^ (Z.of_nat i)
    + to_Z v * (base width) ^ (Z.of_nat i).
Proof.
  intros ws i v Hi.
  rewrite set_word_eq_local, get_word_eq_local.
  apply WL.to_Z_words_set_word. exact Hi.
Qed.

Lemma base_width_pos : 0 < base width.
Proof. unfold base. apply Z.pow_pos_nonneg; lia. Qed.

Lemma base_width_ge_2 : 2 <= base width.
Proof.
  unfold base. change 2 with (2 ^ 1) at 1.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma pow64_modulus_words : forall n,
  2 ^ (64 * Z.of_nat n) = modulus_words n.
Proof.
  intro n.
  unfold modulus_words, base.
  rewrite width_is_64.
  rewrite Z.pow_mul_r by lia.
  reflexivity.
Qed.

Lemma pow64_succ : forall n,
  2 ^ (64 * Z.of_nat (S n)) = base width * 2 ^ (64 * Z.of_nat n).
Proof.
  intro n.
  rewrite !pow64_modulus_words.
  apply modulus_words_succ.
Qed.

Lemma shifted_term_mod_0 : forall z I R,
  (R <= I)%nat ->
  (z * 2 ^ (64 * Z.of_nat I)) mod modulus_words R = 0.
Proof.
  intros z I R HRI.
  assert (Hexp : Z.of_nat I = Z.of_nat R + Z.of_nat (I - R)) by lia.
  rewrite Hexp at 1.
  replace (64 * (Z.of_nat R + Z.of_nat (I - R)))
    with (64 * Z.of_nat R + 64 * Z.of_nat (I - R)) by ring.
  rewrite Z.pow_add_r by lia.
  rewrite pow64_modulus_words.
  replace (z * (modulus_words R * 2 ^ (64 * Z.of_nat (I - R))))
    with ((z * 2 ^ (64 * Z.of_nat (I - R))) * modulus_words R)
    by ring.
  rewrite Z.mod_mul by (pose proof (modulus_words_pos R); lia).
  reflexivity.
Qed.

Lemma low_limb_shift_mod : forall a i,
  ((a mod base width) * 2 ^ (64 * Z.of_nat i)) mod modulus_words (S i) =
  (a * 2 ^ (64 * Z.of_nat i)) mod modulus_words (S i).
Proof.
  intros a i.
  rewrite !pow64_modulus_words.
  rewrite modulus_words_succ.
  rewrite (Z_div_mod_eq_full a (base width)) at 2.
  rewrite Z.mul_add_distr_r.
  rewrite Z.add_mod by (pose proof (modulus_words_pos i); pose proof base_width_pos; lia).
  replace (base width * (a / base width) * modulus_words i)
    with ((a / base width) * modulus_words (S i))
    by (rewrite modulus_words_succ; ring).
  rewrite modulus_words_succ.
  assert (Hm : base width * modulus_words i <> 0).
  { pose proof base_width_pos. pose proof (modulus_words_pos i). lia. }
  rewrite Z.mod_mul by exact Hm.
  rewrite Z.add_0_l.
  rewrite Z.mod_mod by exact Hm.
  reflexivity.
Qed.

Lemma add_shifted_term_mod : forall a z i,
  (a + z * 2 ^ (64 * Z.of_nat (S i))) mod modulus_words (S i) =
  a mod modulus_words (S i).
Proof.
  intros a z i.
  rewrite <- Zplus_mod_idemp_r.
  rewrite shifted_term_mod_0 by lia.
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma add_low_limb_shift_mod : forall a c i,
  (((a mod base width) + c) * 2 ^ (64 * Z.of_nat i)) mod modulus_words (S i) =
  ((a + c) * 2 ^ (64 * Z.of_nat i)) mod modulus_words (S i).
Proof.
  intros a c i.
  rewrite <- low_limb_shift_mod with (a := a mod base width + c).
  rewrite <- low_limb_shift_mod with (a := a + c).
  rewrite Zplus_mod_idemp_l.
  reflexivity.
Qed.

Lemma two_limb_shift_mod : forall a i,
  ((a mod (base width * base width)) * 2 ^ (64 * Z.of_nat i))
    mod modulus_words (S (S i))
  = (a * 2 ^ (64 * Z.of_nat i)) mod modulus_words (S (S i)).
Proof.
  intros a i.
  rewrite !pow64_modulus_words.
  rewrite (Z_div_mod_eq_full a (base width * base width)) at 2.
  rewrite Z.mul_add_distr_r.
  rewrite Z.add_mod by (pose proof (modulus_words_pos (S (S i))); lia).
  replace ((base width * base width) * (a / (base width * base width)) *
           modulus_words i)
    with ((a / (base width * base width)) * modulus_words (S (S i))).
  2:{ rewrite !modulus_words_succ. ring. }
  assert (Hm : modulus_words (S (S i)) <> 0).
  { pose proof (modulus_words_pos (S (S i))). lia. }
  rewrite Z.mod_mul by exact Hm.
  rewrite Z.add_0_l.
  rewrite Z.mod_mod by exact Hm.
  reflexivity.
Qed.

Lemma set_word_add_last_mod : forall result pos c,
  length result = S pos ->
  to_Z_words (set_word result pos (add (get_word result pos) c))
    mod modulus_words (S pos)
  = (to_Z_words result + to_Z c * 2 ^ (64 * Z.of_nat pos))
    mod modulus_words (S pos).
Proof.
  intros result pos c Hlen.
  rewrite to_Z_words_set_word_local.
  2:{ rewrite Hlen. lia. }
  rewrite spec_add.
  change ((base width) ^ Z.of_nat pos) with (modulus_words pos).
  rewrite <- pow64_modulus_words.
  replace
    (to_Z_words result - to_Z (get_word result pos) * 2 ^ (64 * Z.of_nat pos)
     + (to_Z (get_word result pos) + to_Z c) mod base width *
       2 ^ (64 * Z.of_nat pos))
    with
      ((to_Z_words result - to_Z (get_word result pos) *
         2 ^ (64 * Z.of_nat pos))
       + (to_Z (get_word result pos) + to_Z c) mod base width *
         2 ^ (64 * Z.of_nat pos)) by ring.
  rewrite <- Zplus_mod_idemp_r.
  rewrite low_limb_shift_mod.
  rewrite Zplus_mod_idemp_r.
  rewrite get_word_eq_local.
  replace
    (to_Z_words result - to_Z (WL.get_word result pos) * 2 ^ (64 * Z.of_nat pos)
     + (to_Z (WL.get_word result pos) + to_Z c) * 2 ^ (64 * Z.of_nat pos))
    with
      (to_Z_words result + to_Z c * 2 ^ (64 * Z.of_nat pos)) by ring.
  reflexivity.
Qed.

Lemma set_word_add_last_with_high_mod : forall result pos c_hi c_lo,
  length result = S pos ->
  to_Z_words (set_word result pos (add (get_word result pos) c_lo))
    mod modulus_words (S pos)
  = (to_Z_words result
     + (to_Z c_hi * base width + to_Z c_lo) * 2 ^ (64 * Z.of_nat pos))
    mod modulus_words (S pos).
Proof.
  intros result pos c_hi c_lo Hlen.
  rewrite set_word_add_last_mod by exact Hlen.
  replace
    (to_Z_words result +
     (to_Z c_hi * base width + to_Z c_lo) * 2 ^ (64 * Z.of_nat pos))
    with
      (to_Z_words result + to_Z c_lo * 2 ^ (64 * Z.of_nat pos)
       + to_Z c_hi * 2 ^ (64 * Z.of_nat (S pos)))
    by (rewrite pow64_succ; ring).
  rewrite add_shifted_term_mod.
  reflexivity.
Qed.

Lemma mul_add_line_recur_nil_correct :
  forall (y_i : t) result J I R (c_hi c_lo : t),
  length result = R ->
  (R <= I + J + 1)%nat ->
  to_Z_words (mul_add_line_recur nil y_i result J I R c_hi c_lo)
    mod modulus_words R
  = (to_Z_words result
     + (to_Z c_hi * base width + to_Z c_lo) *
       2 ^ (64 * Z.of_nat (I + J)))
    mod modulus_words R.
Proof.
  intros y_i result J I R c_hi c_lo Hlen HRbound.
  cbn [mul_add_line_recur to_Z_words].
  destruct (Nat.ltb (I + J + 1) R) eqn:HI1.
  - apply Nat.ltb_lt in HI1. exfalso. lia.
  - destruct (Nat.ltb (I + J) R) eqn:HI.
    + apply Nat.ltb_lt in HI.
      apply Nat.ltb_ge in HI1.
      assert (HR : R = S (I + J)) by lia.
      rewrite HR.
      apply set_word_add_last_with_high_mod.
      rewrite HR in Hlen. exact Hlen.
    + apply Nat.ltb_ge in HI.
      rewrite <- Zplus_mod_idemp_r.
      rewrite shifted_term_mod_0 by lia.
      cbn. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma adc_2_full_mul_step_mod_words :
  forall result pos x y c_hi c_lo c_lo' res,
  length result = S (S pos) ->
  adc_2_full (mul x y) (get_word result pos) c_hi c_lo = (c_lo', res) ->
  (to_Z_words (set_word result pos res)
   + to_Z c_lo' * modulus_words (S pos))
    mod modulus_words (S (S pos))
  = (to_Z_words result
     + (to_Z (mul x y) * base width
        + to_Z c_hi * base width + to_Z c_lo)
       * modulus_words pos)
    mod modulus_words (S (S pos)).
Proof. Admitted.

Lemma mulx_hi_bound : forall x y hi lo,
  mulx x y = (hi, lo) ->
  to_Z hi <= base width - 2.
Proof.
  intros x y hi lo Hmulx.
  pose proof (spec_mulx x y) as Hspec.
  rewrite Hmulx in Hspec.
  pose proof (spec_to_Z x) as Hx.
  pose proof (spec_to_Z y) as Hy.
  pose proof (spec_to_Z lo) as Hlo.
  set (B := base width) in *.
  assert (HB : 0 < B) by (subst B; apply base_width_pos).
  assert (HB2 : 2 <= B) by (subst B; apply base_width_ge_2).
  assert (Hx' : to_Z x <= B - 1) by lia.
  assert (Hy' : to_Z y <= B - 1) by lia.
  assert (Hprod : to_Z x * to_Z y <= (B - 1) * (B - 1)) by nia.
  assert (Hhi : to_Z hi * B <= (B - 1) * (B - 1)) by nia.
  assert (Hhi_lt : to_Z hi < B - 1).
  { apply Z.nle_gt. intro Hge.
    assert ((B - 1) * B <= to_Z hi * B).
    { apply Z.mul_le_mono_nonneg_r; lia. }
    nia. }
  lia.
Qed.

Lemma to_Z_words_set_word_zero_local : forall ws i v,
  (i < length ws)%nat ->
  MakeProofs.get_word ws i = zero ->
  to_Z_words (MakeProofs.set_word ws i v) =
    to_Z_words ws + to_Z v * 2 ^ (64 * Z.of_nat i).
Proof.
  intros ws i v Hi Hz.
  rewrite to_Z_words_set_word_local by exact Hi.
  rewrite Hz, spec_zero.
  change ((base width) ^ Z.of_nat i) with (modulus_words i).
  rewrite pow64_modulus_words.
  replace (to_Z_words ws - 0 * modulus_words i + to_Z v * modulus_words i)
    with (to_Z_words ws + to_Z v * modulus_words i) by ring.
  reflexivity.
Qed.

Lemma zero_tail_after_set_word_local :
  forall result I R res_I,
  (forall j, (I <= j)%nat -> (j < R)%nat -> get_word result j = zero) ->
  forall j, (S I <= j)%nat -> (j < R)%nat ->
    get_word (MakeProofs.set_word result I res_I) j = zero.
Proof.
  intros result I R res_I Hzero j Hij HjR.
  rewrite set_word_eq_local.
  rewrite WL.get_set_word_other.
  - apply Hzero; lia.
  - lia.
Qed.

(** * Structural Helpers *)

Lemma mul_line_recur_length : forall xs (y : t) result I R (carry : t),
  length result = R ->
  length (mul_line_recur xs y result I R carry) = R.
Proof.
  induction xs as [| x rest IH]; intros y result I R carry Hlen; simpl.
  - destruct (Nat.ltb I R); [rewrite set_word_length_local|]; exact Hlen.
  - destruct (Nat.ltb I R); [|exact Hlen].
    destruct (Nat.ltb (I + 1) R).
    + destruct (mulx x y) as [hi lo].
      destruct (adc_2_short hi lo carry) as [nc ri].
      apply IH. rewrite set_word_length_local. exact Hlen.
    + rewrite set_word_length_local. exact Hlen.
Qed.

Lemma mul_line_length : forall R xs (y : t),
  length (mul_line R xs y) = R.
Proof.
  intros R xs y. unfold mul_line.
  destruct xs as [| x0 rest].
  - apply extend_words_length_local.
  - destruct (mulx y x0) as [carry lo].
    apply mul_line_recur_length.
    rewrite set_word_length_local. apply extend_words_length_local.
Qed.

Lemma mul_add_line_recur_length :
  forall xs_tail (y_i : t) result J I R (c_hi c_lo : t),
  length result = R ->
  length (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo) = R.
Proof.
  induction xs_tail as [| x rest IH]; intros y_i result J I R c_hi c_lo Hlen;
    simpl.
  - destruct (Nat.ltb (I + J + 1) R).
    + destruct (adc_2_short c_hi c_lo (MakeProofs.get_word result (I + J)))
        as [r1 r0] eqn:Hadc.
      cbn.
      rewrite set_word_length_local, set_word_length_local. exact Hlen.
    + destruct (Nat.ltb (I + J) R);
        [rewrite set_word_length_local|]; exact Hlen.
  - destruct (Nat.ltb (I + J) R); [|exact Hlen].
    destruct (Nat.ltb (I + J + 2) R).
    + destruct (mulx x y_i) as [hi lo] eqn:Hmulx.
      destruct (adc_3 hi lo (MakeProofs.get_word result (I + J)) c_hi c_lo)
        as [[ch cl] ri] eqn:Hadc.
      cbn.
      apply IH. rewrite set_word_length_local. exact Hlen.
    + destruct (Nat.ltb (I + J + 1) R).
      * destruct
          (adc_2_full (mul x y_i) (MakeProofs.get_word result (I + J))
             c_hi c_lo)
          as [cl ri] eqn:Hadc.
        cbn.
        apply IH. rewrite set_word_length_local. exact Hlen.
      * cbn. apply IH. rewrite set_word_length_local. exact Hlen.
Qed.

Lemma mul_add_line_length : forall I R xs (y_i : t) result,
  length result = R ->
  length (mul_add_line I R xs y_i result) = R.
Proof.
  intros I R xs y_i result Hlen. unfold mul_add_line.
  destruct xs as [| x0 rest]; [exact Hlen|].
  destruct (Nat.ltb (I + 1) R); [destruct (mulx x0 y_i) as [ch cl]|].
  - apply mul_add_line_recur_length. exact Hlen.
  - apply mul_add_line_recur_length. exact Hlen.
Qed.

Lemma truncating_mul_runtime_recur_length : forall xs ys result I R,
  length result = R ->
  length (truncating_mul_runtime_recur xs ys result I R) = R.
Proof.
  intros xs ys. induction ys as [| y rest IH]; intros result I R Hlen; simpl.
  - exact Hlen.
  - apply IH. apply mul_add_line_length. exact Hlen.
Qed.

Lemma truncating_mul_runtime_length : forall xs ys R,
  (0 < R)%nat ->
  length (truncating_mul_runtime xs ys R) = R.
Proof.
  intros xs ys R HR. unfold truncating_mul_runtime.
  destruct ys as [| y rest].
  - apply extend_words_length_local.
  - apply truncating_mul_runtime_recur_length.
    apply mul_line_length.
Qed.

Lemma mul_add_line_recur_alt_eq :
  forall xs (y_i : t) result J I R (c_hi c_lo : t),
  mul_add_line_recur_alt xs y_i result J I R c_hi c_lo =
  mul_add_line_recur xs y_i result J I R c_hi c_lo.
Proof.
  induction xs as [| x rest IH]; intros y_i result J I R c_hi c_lo; simpl.
  - reflexivity.
  - destruct (Nat.ltb (I + J) R); [|reflexivity].
    destruct (Nat.ltb (I + J + 2) R).
    + destruct (mulx x y_i) as [hi lo].
      destruct (adc_3 hi lo (MakeProofs.get_word result (I + J)) c_hi c_lo)
        as [[ch cl] ri].
      apply IH.
    + destruct (Nat.ltb (I + J + 1) R).
      * destruct
          (adc_2_full (mul x y_i) (MakeProofs.get_word result (I + J))
             c_hi c_lo)
          as [cl ri].
        apply IH.
      * apply IH.
Qed.

(** * Recursive Helper Correctness *)

Lemma mul_line_recur_correct : forall xs (y : t) result I R (carry : t),
  length result = R ->
  (I <= R)%nat ->
  (forall j, (I <= j)%nat -> (j < R)%nat -> get_word result j = zero) ->
  to_Z_words (mul_line_recur xs y result I R carry) mod modulus_words R
  = (to_Z_words result +
       (to_Z_words xs * to_Z y + to_Z carry) * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof.
  induction xs as [|x rest IH]; intros y result I R carry Hlen HIR Hzero.
  - cbn [mul_line_recur to_Z_words].
    destruct (Nat.ltb I R) eqn:HI.
    + apply Nat.ltb_lt in HI.
      assert (HzI : MakeProofs.get_word result I = zero).
      { rewrite get_word_eq_local. apply Hzero; lia. }
      rewrite to_Z_words_set_word_zero_local.
      2:{ rewrite Hlen. lia. }
      2:{ exact HzI. }
      ring_simplify. reflexivity.
    + apply Nat.ltb_ge in HI.
      rewrite <- Zplus_mod_idemp_r.
      rewrite shifted_term_mod_0 by lia.
      cbn. rewrite Z.add_0_r. reflexivity.
  - cbn [mul_line_recur to_Z_words].
    destruct (Nat.ltb I R) eqn:HI.
    + apply Nat.ltb_lt in HI.
      destruct (Nat.ltb (I + 1) R) eqn:HI1.
      * apply Nat.ltb_lt in HI1.
        destruct (mulx x y) as [hi lo] eqn:Hmulx.
        destruct (adc_2_short hi lo carry) as [new_carry res_I] eqn:Hadc.
        rewrite (IH y (MakeProofs.set_word result I res_I) (S I) R new_carry).
        2:{ rewrite set_word_length_local. exact Hlen. }
        2:{ lia. }
        2:{ intros j Hij HjR.
            rewrite set_word_eq_local.
            rewrite WL.get_set_word_other.
            - apply Hzero; lia.
            - lia. }
        assert (HzI : MakeProofs.get_word result I = zero).
        { rewrite get_word_eq_local. apply Hzero; lia. }
        rewrite to_Z_words_set_word_zero_local.
        2:{ rewrite Hlen. lia. }
        2:{ exact HzI. }
        replace (2 ^ (64 * Z.of_nat (S I)))
          with (base width * 2 ^ (64 * Z.of_nat I))
          by (symmetry; apply pow64_succ).
        pose proof (spec_mulx x y) as Hmul.
        rewrite Hmulx in Hmul.
        pose proof (spec_adc_2_short hi lo carry (mulx_hi_bound _ _ _ _ Hmulx))
          as Hcarry.
        rewrite Hadc in Hcarry.
        rewrite Hmul in Hcarry.
        assert (Hstep :
          to_Z res_I + base width * (to_Z_words rest * to_Z y + to_Z new_carry) =
          (to_Z x + base width * to_Z_words rest) * to_Z y + to_Z carry).
        { nia. }
        replace
          (to_Z_words result + to_Z res_I * 2 ^ (64 * Z.of_nat I) +
           (to_Z_words rest * to_Z y + to_Z new_carry) *
           (base width * 2 ^ (64 * Z.of_nat I)))
          with
            (to_Z_words result +
             (to_Z res_I
              + base width * (to_Z_words rest * to_Z y + to_Z new_carry)) *
             2 ^ (64 * Z.of_nat I))
          by ring.
        replace (to_Z_words (x :: rest))
          with (to_Z x + base width * to_Z_words rest) by reflexivity.
        rewrite Hstep.
        reflexivity.
      * apply Nat.ltb_ge in HI1.
        assert (HSR : R = S I) by lia.
        assert (HzI : MakeProofs.get_word result I = zero).
        { rewrite get_word_eq_local. apply Hzero; lia. }
        rewrite to_Z_words_set_word_zero_local.
        2:{ rewrite Hlen. lia. }
        2:{ exact HzI. }
        rewrite spec_add, spec_mul.
        rewrite <- Zplus_mod_idemp_l.
        subst R.
        rewrite HSR.
        rewrite (Z.mod_small (to_Z_words result) (modulus_words (S I))).
        2:{ pose proof (to_Z_words_bound result) as Hbound.
            rewrite HSR in Hbound. exact Hbound. }
        rewrite <- Zplus_mod_idemp_r.
        rewrite low_limb_shift_mod.
        rewrite add_low_limb_shift_mod.
        rewrite Zplus_mod_idemp_r.
        replace (to_Z_words (x :: rest))
          with (to_Z x + base width * to_Z_words rest) by reflexivity.
        replace
          (((to_Z x + base width * to_Z_words rest) * to_Z y + to_Z carry) *
           2 ^ (64 * Z.of_nat I))
          with
            ((to_Z x * to_Z y + to_Z carry) * 2 ^ (64 * Z.of_nat I)
             + (to_Z_words rest * to_Z y) *
               2 ^ (64 * Z.of_nat (S I)))
          by (rewrite pow64_succ; ring).
        replace
          (to_Z_words result +
           ((x * y + carry) * 2 ^ (64 * Z.of_nat I) +
            to_Z_words rest * y * 2 ^ (64 * Z.of_nat (S I))))
          with
            ((to_Z_words result + (x * y + carry) * 2 ^ (64 * Z.of_nat I))
             + to_Z_words rest * y * 2 ^ (64 * Z.of_nat (S I)))
          by ring.
        rewrite add_shifted_term_mod.
        replace (y * x) with (x * y) by ring.
        reflexivity.
    + apply Nat.ltb_ge in HI.
      rewrite <- Zplus_mod_idemp_r.
      rewrite shifted_term_mod_0 by lia.
      cbn. rewrite Z.add_0_r. reflexivity.
Qed.

Lemma mul_add_line_recur_correct :
  forall xs_tail (y_i : t) result J I R (c_hi c_lo : t),
  length result = R ->
  (R <= I + J + length xs_tail + 1)%nat ->
  to_Z_words (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo)
    mod modulus_words R
  = (to_Z_words result
     + (to_Z_words xs_tail * to_Z y_i * base width
        + to_Z c_hi * base width + to_Z c_lo)
       * 2^(64 * Z.of_nat (I + J)))
    mod modulus_words R.
Proof. Admitted.

(** * Row-Level Correctness *)

Lemma mul_line_correct : forall R xs (y : t),
  (0 < R)%nat ->
  to_Z_words (mul_line R xs y) mod modulus_words R
  = (to_Z y * to_Z_words xs) mod modulus_words R.
Proof. Admitted.

Lemma mul_add_line_correct : forall I R xs (y_i : t) result,
  length result = R ->
  (R <= I + length xs)%nat ->
  to_Z_words (mul_add_line I R xs y_i result) mod modulus_words R
  = (to_Z_words result + to_Z y_i * to_Z_words xs * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof. Admitted.

(** * General Word-List Theorem *)

Lemma truncating_mul_runtime_recur_correct : forall xs ys_tail result I R,
  length result = R ->
  (0 < R)%nat ->
  (length xs <= R)%nat ->
  (R <= I + length xs)%nat ->
  to_Z_words (truncating_mul_runtime_recur xs ys_tail result I R)
    mod modulus_words R
  = (to_Z_words result
     + to_Z_words xs * to_Z_words ys_tail * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof. Admitted.

Theorem truncating_mul_runtime_correct : forall xs ys R,
  (0 < R)%nat ->
  (length xs <= R)%nat ->
  (R <= 1 + length xs)%nat ->
  to_Z_words (truncating_mul_runtime xs ys R) mod modulus_words R
  = (to_Z_words xs * to_Z_words ys) mod modulus_words R.
Proof. Admitted.

(** * Main 256-bit Theorem *)

Theorem truncating_mul256_runtime_correct : forall (x y : words),
  length x = 4%nat ->
  length y = 4%nat ->
  to_Z_words (truncating_mul_runtime x y 4) mod modulus_words 4
  = (to_Z_words x * to_Z_words y) mod modulus_words 4.
Proof. Admitted.

End MakeProofs.
