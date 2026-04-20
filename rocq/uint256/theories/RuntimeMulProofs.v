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
From Uint256 Require Import Uint Base Words WordsLemmas RuntimeMul.

Module MakeProofsOn
  (B : Base.BaseProofSig)
  (RM : RuntimeMul.RuntimeMulProofSig with Module U64 := B.U64)
  (WL : WordsLemmas.WordsLemmasProofSig with Module U64 := B.U64).
Include RM.
Import WL.
Import B.U64.

Import ListNotations.
Open Scope Z_scope.

Local Coercion to_Z : t >-> Z.

(** * Local structural lemmas

    These are retained as local aliases for proof-script stability while
    the shared-base migration is in progress. *)

Lemma set_word_length_local : forall (ws : words) i v,
  length (set_word ws i v) = length ws.
Proof.
  apply WL.set_word_length.
Qed.

Lemma extend_words_length_local : forall n,
  length (extend_words n) = n.
Proof. apply WL.extend_words_length. Qed.

Lemma get_set_word_same_local : forall ws i v,
  (i < length ws)%nat ->
  MakeProofsOn.get_word (MakeProofsOn.set_word ws i v) i = v.
Proof.
  intros ws i v Hi.
  apply WL.get_set_word_same. exact Hi.
Qed.

Lemma get_set_word_other_local : forall ws i j v,
  i <> j ->
  MakeProofsOn.get_word (MakeProofsOn.set_word ws i v) j =
  MakeProofsOn.get_word ws j.
Proof.
  intros ws i j v Hij.
  apply WL.get_set_word_other. exact Hij.
Qed.

Lemma to_Z_words_set_word_local : forall ws i v,
  (i < length ws)%nat ->
  to_Z_words (MakeProofsOn.set_word ws i v) =
    to_Z_words ws
    - to_Z (MakeProofsOn.get_word ws i) * (base width) ^ (Z.of_nat i)
    + to_Z v * (base width) ^ (Z.of_nat i).
Proof.
  intros ws i v Hi.
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
  change (get_word result pos) with (MakeProofsOn.get_word result pos).
  replace
    (to_Z_words result
     - to_Z (MakeProofsOn.get_word result pos) * 2 ^ (64 * Z.of_nat pos)
     + (to_Z (MakeProofsOn.get_word result pos) + to_Z c) *
       2 ^ (64 * Z.of_nat pos))
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
      cbn; rewrite Z.add_0_r; reflexivity.
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
Proof.
  intros result pos x y c_hi c_lo c_lo' res Hlen Hadc.
  rewrite to_Z_words_set_word_local by (rewrite Hlen; lia).
  change (MakeProofsOn.get_word result pos) with (get_word result pos).
  change ((base width) ^ Z.of_nat pos) with (modulus_words pos).
  rewrite modulus_words_succ.
  pose proof (spec_adc_2_full (mul x y) (get_word result pos) c_hi c_lo)
    as Hspec.
  rewrite Hadc in Hspec.
  set (P := modulus_words pos) in *.
  set (M := modulus_words (S (S pos))) in *.
  assert (Hpair :
    (to_Z_words result - to_Z (get_word result pos) * P
     + (to_Z c_lo' * base width + to_Z res) * P) mod M
    =
    (to_Z_words result - to_Z (get_word result pos) * P
     + ((to_Z (mul x y) * base width + to_Z (get_word result pos)
         + to_Z c_hi * base width + to_Z c_lo)
        mod (base width * base width)) * P) mod M).
  { apply (f_equal (fun z =>
      (to_Z_words result - to_Z (get_word result pos) * P + z * P) mod M))
      in Hspec.
    exact Hspec. }
  transitivity
    ((to_Z_words result - to_Z (get_word result pos) * P
      + (to_Z c_lo' * base width + to_Z res) * P) mod M).
  { apply (f_equal (fun z => z mod M)). nia. }
  transitivity
    ((to_Z_words result - to_Z (get_word result pos) * P
      + ((to_Z (mul x y) * base width + to_Z (get_word result pos)
          + to_Z c_hi * base width + to_Z c_lo)
         mod (base width * base width)) * P) mod M).
  { exact Hpair. }
  subst P M.
  rewrite <- pow64_modulus_words.
  rewrite <- Zplus_mod_idemp_r.
  rewrite two_limb_shift_mod.
  rewrite Zplus_mod_idemp_r.
  transitivity
    ((to_Z_words result
      + (to_Z (mul x y) * base width
         + to_Z c_hi * base width + to_Z c_lo) * modulus_words pos)
     mod modulus_words (S (S pos))).
  { apply (f_equal (fun z => z mod modulus_words (S (S pos)))).
    rewrite pow64_modulus_words.
    ring. }
  rewrite <- pow64_modulus_words.
  reflexivity.
Qed.

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
  MakeProofsOn.get_word ws i = zero ->
  to_Z_words (MakeProofsOn.set_word ws i v) =
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
    get_word (MakeProofsOn.set_word result I res_I) j = zero.
Proof.
  intros result I R res_I Hzero j Hij HjR.
  rewrite WL.get_set_word_other.
  - apply Hzero; lia.
  - lia.
Qed.

Definition carry_pair_bounded (c_hi c_lo : t) : Prop :=
  to_Z c_hi * base width + to_Z c_lo <=
    base width * base width - base width.

Lemma add_modulus_words_term_mod : forall a z n,
  (a + z * modulus_words n) mod modulus_words n = a mod modulus_words n.
Proof.
  intros a z n.
  rewrite <- Zplus_mod_idemp_r.
  rewrite Z.mod_mul by (pose proof (modulus_words_pos n); lia).
  rewrite Z.add_0_r.
  reflexivity.
Qed.

Lemma mulx_carry_pair_bounded : forall x y hi lo,
  mulx x y = (hi, lo) ->
  carry_pair_bounded hi lo.
Proof.
  intros x y hi lo Hmulx.
  pose proof (spec_mulx x y) as Hmul.
  pose proof (spec_to_Z x) as Hx.
  pose proof (spec_to_Z y) as Hy.
  pose proof base_width_ge_2 as HB.
  unfold carry_pair_bounded.
  rewrite Hmulx in Hmul.
  nia.
Qed.

Lemma adc_2_short_exact_pair_bound : forall c_hi c_lo y0 r1 r0,
  carry_pair_bounded c_hi c_lo ->
  adc_2_short c_hi c_lo y0 = (r1, r0) ->
  to_Z r1 * base width + to_Z r0 =
    to_Z c_hi * base width + to_Z c_lo + to_Z y0.
Proof.
  intros c_hi c_lo y0 r1 r0 Hbound Hadc.
  pose proof (spec_adc_2_short_mod c_hi c_lo y0) as Hspec.
  pose proof (spec_to_Z c_hi) as Hhi.
  pose proof (spec_to_Z c_lo) as Hlo.
  pose proof (spec_to_Z y0) as Hy.
  pose proof base_width_pos as HB.
  unfold carry_pair_bounded in Hbound.
  rewrite Hadc in Hspec.
  rewrite Z.mod_small in Hspec by lia.
  exact Hspec.
Qed.

Lemma adc_3_carry_pair_bounded :
  forall x y x0 c_hi c_lo hi lo c_hi' c_lo' r0,
  mulx x y = (hi, lo) ->
  carry_pair_bounded c_hi c_lo ->
  adc_3 hi lo x0 c_hi c_lo = (c_hi', c_lo', r0) ->
  carry_pair_bounded c_hi' c_lo'.
Proof.
  intros x y x0 c_hi c_lo hi lo c_hi' c_lo' r0 Hmulx Hbound Hadc.
  pose proof (spec_mulx x y) as Hmul.
  pose proof (spec_to_Z x) as Hx.
  pose proof (spec_to_Z y) as Hy.
  pose proof (spec_to_Z x0) as Hx0.
  pose proof (spec_to_Z c_hi') as Hhi'.
  pose proof (spec_to_Z c_lo') as Hlo'.
  pose proof (spec_to_Z r0) as Hr0.
  pose proof base_width_ge_2 as HB.
  pose proof base_width_pos as HBpos.
  pose proof (spec_adc_3 hi lo x0 c_hi c_lo (mulx_hi_bound _ _ _ _ Hmulx))
    as Hadc_spec.
  unfold carry_pair_bounded in *.
  rewrite Hmulx in Hmul.
  rewrite Hadc in Hadc_spec.
  assert (Hprod : to_Z hi * base width + to_Z lo <=
                  base width * base width - 2 * base width + 1).
  { rewrite Hmul. nia. }
  assert (Hsum :
    (to_Z c_hi' * base width + to_Z c_lo') * base width + to_Z r0 <=
      (base width * base width - base width) * base width +
      (base width - 1)).
  { replace ((to_Z c_hi' * base width + to_Z c_lo') * base width + to_Z r0)
      with (to_Z c_hi' * base width * base width
            + to_Z c_lo' * base width + to_Z r0) by ring.
    rewrite Hadc_spec. nia. }
  nia.
Qed.

Lemma adc_3_mul_step_mod_words :
  forall result pos R x y hi lo c_hi c_lo c_hi' c_lo' res,
  length result = R ->
  (pos < R)%nat ->
  mulx x y = (hi, lo) ->
  adc_3 hi lo (get_word result pos) c_hi c_lo = (c_hi', c_lo', res) ->
  (to_Z_words (set_word result pos res)
   + (to_Z c_hi' * base width + to_Z c_lo') * modulus_words (S pos))
    mod modulus_words R
  = (to_Z_words result
     + (to_Z x * to_Z y * base width
        + to_Z c_hi * base width + to_Z c_lo)
       * modulus_words pos)
    mod modulus_words R.
Proof.
  intros result pos R x y hi lo c_hi c_lo c_hi' c_lo' res Hlen Hpos Hmulx
    Hadc.
  rewrite to_Z_words_set_word_local by (rewrite Hlen; lia).
  change ((base width) ^ Z.of_nat pos) with (modulus_words pos).
  rewrite modulus_words_succ.
  pose proof (spec_mulx x y) as Hmul.
  pose proof (spec_adc_3 hi lo (get_word result pos) c_hi c_lo
    (mulx_hi_bound _ _ _ _ Hmulx)) as Hadc_spec.
  rewrite Hmulx in Hmul.
  rewrite Hadc in Hadc_spec.
  assert (Heq :
    to_Z_words result - to_Z (get_word result pos) * modulus_words pos
    + to_Z res * modulus_words pos
    + (to_Z c_hi' * base width + to_Z c_lo') *
      (base width * modulus_words pos)
    = to_Z_words result
      + (to_Z x * to_Z y * base width + to_Z c_hi * base width + to_Z c_lo) *
        modulus_words pos).
  { nia. }
  apply (f_equal (fun z => z mod modulus_words R)) in Heq.
  exact Heq.
Qed.

Lemma adc_2_short_carry_step_zero_mod :
  forall result pos R c_hi c_lo r1 r0,
  length result = R ->
  (S pos < R)%nat ->
  carry_pair_bounded c_hi c_lo ->
  get_word result (S pos) = zero ->
  adc_2_short c_hi c_lo (get_word result pos) = (r1, r0) ->
  to_Z_words (set_word (set_word result pos r0) (S pos) r1)
    mod modulus_words R
  = (to_Z_words result
     + (to_Z c_hi * base width + to_Z c_lo) * modulus_words pos)
    mod modulus_words R.
Proof.
  intros result pos R c_hi c_lo r1 r0 Hlen Hpos Hbound Hzero Hadc.
  rewrite to_Z_words_set_word_zero_local.
  2:{ rewrite set_word_length_local, Hlen. lia. }
  2:{ rewrite get_set_word_other_local by lia. exact Hzero. }
  rewrite to_Z_words_set_word_local by (rewrite Hlen; lia).
  change (MakeProofsOn.get_word result pos) with (get_word result pos).
  change ((base width) ^ Z.of_nat pos) with (modulus_words pos).
  rewrite pow64_succ.
  pose proof (adc_2_short_exact_pair_bound c_hi c_lo
    (get_word result pos) r1 r0 Hbound Hadc) as Hpair.
  rewrite <- pow64_modulus_words.
  transitivity
    ((to_Z_words result - to_Z (get_word result pos) * modulus_words pos
      + (to_Z r1 * base width + to_Z r0) * modulus_words pos)
     mod modulus_words R).
  { apply (f_equal (fun z => z mod modulus_words R)).
    rewrite pow64_modulus_words.
    ring. }
  transitivity
    ((to_Z_words result - to_Z (get_word result pos) * modulus_words pos
      + (to_Z c_hi * base width + to_Z c_lo + to_Z (get_word result pos)) *
        modulus_words pos)
     mod modulus_words R).
  { apply (f_equal (fun z =>
      (to_Z_words result - to_Z (get_word result pos) * modulus_words pos
       + z * modulus_words pos) mod modulus_words R)) in Hpair.
    exact Hpair. }
  transitivity
    ((to_Z_words result
      + (to_Z c_hi * base width + to_Z c_lo) * modulus_words pos)
     mod modulus_words R).
  { apply (f_equal (fun z => z mod modulus_words R)). ring. }
  rewrite <- pow64_modulus_words.
  reflexivity.
Qed.

Lemma zero_tail_before_set_word_local :
  forall result I R res_I,
  (forall j, (S I <= j)%nat -> (j < R)%nat -> get_word result j = zero) ->
  forall j, (S I <= j)%nat -> (j < R)%nat ->
    get_word (MakeProofsOn.set_word result I res_I) j = zero.
Proof.
  intros result I R res_I Hzero j Hij HjR.
  rewrite get_set_word_other_local by lia.
  apply Hzero; lia.
Qed.

Lemma mul_add_line_recur_zero_tail :
  forall xs_tail (y_i : t) result J I R (c_hi c_lo : t),
  length result = R ->
  (R <= I + J + length xs_tail + 1)%nat ->
  (forall j, (I + J + length xs_tail <= j)%nat -> (j < R)%nat ->
     get_word result j = zero) ->
  forall j, (I + J + S (length xs_tail) <= j)%nat -> (j < R)%nat ->
    get_word (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo) j = zero.
Proof.
  induction xs_tail as [|x rest IH];
    intros y_i result J I R c_hi c_lo Hlen HRbound Hzero j Hj HjR;
    cbn [mul_add_line_recur].
  - exfalso. lia.
  - remember (I + J)%nat as pos eqn:Hpos_def in *.
    destruct (Nat.ltb pos R) eqn:Hpos.
    + destruct (Nat.ltb (pos + 2) R) eqn:Hpos2.
      * destruct (mulx x y_i) as [hi lo] eqn:Hmulx.
        destruct (adc_3 hi lo (MakeProofsOn.get_word result pos) c_hi c_lo)
          as [[c_hi' c_lo'] res] eqn:Hadc.
        change (MakeProofsOn.set_word result pos res) with (set_word result pos res).
        eapply IH;
          [rewrite set_word_length_local; exact Hlen
          |cbn [length] in HRbound; subst pos; lia
          |intros k Hk HkR;
             rewrite get_set_word_other_local by lia;
             apply Hzero; subst pos; lia
          |cbn [length] in Hj; subst pos; lia
          |exact HjR].
      * destruct (Nat.ltb (pos + 1) R) eqn:Hpos1.
        -- destruct (adc_2_full (mul x y_i) (MakeProofsOn.get_word result pos)
                     c_hi c_lo) as [c_lo' res] eqn:Hadc.
           change (MakeProofsOn.set_word result pos res)
             with (set_word result pos res).
           eapply IH;
             [rewrite set_word_length_local; exact Hlen
             |cbn [length] in HRbound; subst pos; lia
             |intros k Hk HkR;
                rewrite get_set_word_other_local by lia;
                apply Hzero; subst pos; lia
             |cbn [length] in Hj; subst pos; lia
             |exact HjR].
        -- change MakeProofsOn.set_word with set_word.
           eapply IH;
             [rewrite set_word_length_local; exact Hlen
             |cbn [length] in HRbound; subst pos; lia
             |intros k Hk HkR;
                rewrite get_set_word_other_local by lia;
                apply Hzero; subst pos; lia
             |cbn [length] in Hj; subst pos; lia
             |exact HjR].
    + apply Hzero; subst pos; lia.
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
    + destruct (adc_2_short c_hi c_lo (MakeProofsOn.get_word result (I + J)))
        as [r1 r0] eqn:Hadc.
      cbn.
      rewrite set_word_length_local, set_word_length_local. exact Hlen.
    + destruct (Nat.ltb (I + J) R);
        [rewrite set_word_length_local|]; exact Hlen.
  - destruct (Nat.ltb (I + J) R); [|exact Hlen].
    destruct (Nat.ltb (I + J + 2) R).
    + destruct (mulx x y_i) as [hi lo] eqn:Hmulx.
      destruct (adc_3 hi lo (MakeProofsOn.get_word result (I + J)) c_hi c_lo)
        as [[ch cl] ri] eqn:Hadc.
      cbn.
      apply IH. rewrite set_word_length_local. exact Hlen.
    + destruct (Nat.ltb (I + J + 1) R).
      * destruct
          (adc_2_full (mul x y_i) (MakeProofsOn.get_word result (I + J))
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
      destruct (adc_3 hi lo (MakeProofsOn.get_word result (I + J)) c_hi c_lo)
        as [[ch cl] ri].
      apply IH.
    + destruct (Nat.ltb (I + J + 1) R).
      * destruct
          (adc_2_full (mul x y_i) (MakeProofsOn.get_word result (I + J))
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
      assert (HzI : MakeProofsOn.get_word result I = zero).
      { apply Hzero; lia. }
      rewrite to_Z_words_set_word_zero_local.
      2:{ rewrite Hlen. lia. }
      2:{ exact HzI. }
      ring_simplify. reflexivity.
    + apply Nat.ltb_ge in HI.
      rewrite <- Zplus_mod_idemp_r.
      rewrite shifted_term_mod_0 by lia.
      cbn; rewrite Z.add_0_r; reflexivity.
  - cbn [mul_line_recur to_Z_words].
    destruct (Nat.ltb I R) eqn:HI.
    + apply Nat.ltb_lt in HI.
      destruct (Nat.ltb (I + 1) R) eqn:HI1.
      * apply Nat.ltb_lt in HI1.
        destruct (mulx x y) as [hi lo] eqn:Hmulx.
        destruct (adc_2_short hi lo carry) as [new_carry res_I] eqn:Hadc.
        rewrite (IH y (MakeProofsOn.set_word result I res_I) (S I) R new_carry).
        2:{ rewrite set_word_length_local. exact Hlen. }
        2:{ lia. }
        2:{ intros j Hij HjR.
            rewrite WL.get_set_word_other.
            - apply Hzero; lia.
            - lia. }
        assert (HzI : MakeProofsOn.get_word result I = zero).
        { apply Hzero; lia. }
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
        change (to_Z_words (x :: rest))
          with (to_Z x + base width * to_Z_words rest).
        rewrite Hstep.
        reflexivity.
      * apply Nat.ltb_ge in HI1.
        assert (HSR : R = S I) by lia.
        assert (HzI : MakeProofsOn.get_word result I = zero).
        { apply Hzero; lia. }
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
        change (to_Z_words (x :: rest))
          with (to_Z x + base width * to_Z_words rest).
        replace
          (((to_Z x + base width * to_Z_words rest) * to_Z y + to_Z carry) *
           2 ^ (64 * Z.of_nat I))
          with
            ((to_Z x * to_Z y + to_Z carry) * 2 ^ (64 * Z.of_nat I)
             + (to_Z_words rest * to_Z y) *
               2 ^ (64 * Z.of_nat (S I)))
          by (rewrite !pow64_succ; ring).
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
      cbn; rewrite Z.add_0_r; reflexivity.
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
Proof.
  induction xs_tail as [|x rest IH];
    intros y_i result J I R c_hi c_lo Hlen HRbound.
  - cbn [length] in HRbound.
    assert (HRbound' : (R <= I + J + 1)%nat) by lia.
    apply mul_add_line_recur_nil_correct.
    + exact Hlen.
    + exact HRbound'.
  - remember (I + J)%nat as pos eqn:Hpos_def in *.
    cbn [mul_add_line_recur to_Z_words].
    rewrite <- Hpos_def.
    destruct (Nat.ltb pos R) eqn:Hpos.
    + apply Nat.ltb_lt in Hpos.
      destruct (Nat.ltb (pos + 2) R) eqn:Hpos2.
      * apply Nat.ltb_lt in Hpos2.
        destruct (mulx x y_i) as [hi lo] eqn:Hmulx.
        destruct (adc_3 hi lo (MakeProofsOn.get_word result pos) c_hi c_lo)
          as [[c_hi' c_lo'] res] eqn:Hadc.
        change (MakeProofsOn.set_word result pos res)
          with (set_word result pos res).
        change (MakeProofsOn.get_word result pos)
          with (get_word result pos) in Hadc.
        rewrite (IH y_i (set_word result pos res) (S J) I R c_hi' c_lo').
        2:{ rewrite set_word_length_local. exact Hlen. }
        2:{ cbn [length] in HRbound. subst pos. lia. }
        replace (I + S J)%nat with (S pos) by (subst pos; lia).
        replace
          (to_Z_words (set_word result pos res)
           + (to_Z_words rest * to_Z y_i * base width
              + to_Z c_hi' * base width + to_Z c_lo') *
             2 ^ (64 * Z.of_nat (S pos)))
          with
            ((to_Z_words (set_word result pos res)
              + (to_Z c_hi' * base width + to_Z c_lo') *
                2 ^ (64 * Z.of_nat (S pos)))
             + to_Z_words rest * to_Z y_i *
               2 ^ (64 * Z.of_nat (S (S pos)))).
        2:{
          replace (2 ^ (64 * Z.of_nat (S (S pos))))
            with (base width * 2 ^ (64 * Z.of_nat (S pos)))
            by (symmetry; apply pow64_succ).
          ring.
        }
        rewrite <- Zplus_mod_idemp_l.
        rewrite pow64_modulus_words.
        rewrite (adc_3_mul_step_mod_words result pos R x y_i hi lo c_hi c_lo
          c_hi' c_lo' res Hlen Hpos Hmulx Hadc).
        rewrite Zplus_mod_idemp_l, !pow64_modulus_words, !modulus_words_succ.
        subst pos.
        change (to_Z_words (x :: rest))
          with (to_Z x + base width * to_Z_words rest).
        apply (f_equal (fun z => z mod modulus_words R)); ring.
      * apply Nat.ltb_ge in Hpos2.
        destruct (Nat.ltb (pos + 1) R) eqn:Hpos1.
        -- apply Nat.ltb_lt in Hpos1.
           assert (HR : R = S (S pos)) by lia.
           assert (Hlen2 : length result = S (S pos)).
           { rewrite <- HR. exact Hlen. }
           destruct (adc_2_full (mul x y_i) (MakeProofsOn.get_word result pos)
                      c_hi c_lo) as [c_lo' res] eqn:Hadc.
           change (MakeProofsOn.set_word result pos res)
             with (set_word result pos res).
           change (MakeProofsOn.get_word result pos)
             with (get_word result pos) in Hadc.
           rewrite (IH y_i (set_word result pos res) (S J) I R c_hi c_lo').
           2:{ rewrite set_word_length_local. exact Hlen. }
           2:{ cbn [length] in HRbound. subst pos. lia. }
           rewrite HR.
           replace (I + S J)%nat with (S pos) by (subst pos; lia).
           replace
             (to_Z_words (set_word result pos res)
              + (to_Z_words rest * to_Z y_i * base width
                 + to_Z c_hi * base width + to_Z c_lo') *
                2 ^ (64 * Z.of_nat (S pos)))
             with
               ((to_Z_words (set_word result pos res)
                 + to_Z c_lo' * 2 ^ (64 * Z.of_nat (S pos)))
                + (to_Z_words rest * to_Z y_i + to_Z c_hi) *
                  2 ^ (64 * Z.of_nat (S (S pos))))
             by (rewrite !pow64_succ; ring).
           rewrite add_shifted_term_mod.
           rewrite pow64_modulus_words.
           rewrite (adc_2_full_mul_step_mod_words result pos x y_i c_hi c_lo
             c_lo' res Hlen2 Hadc).
           rewrite <- pow64_modulus_words.
           rewrite spec_mul.
           replace
             (to_Z_words result
              + (((to_Z x * to_Z y_i) mod base width) * base width
                 + to_Z c_hi * base width + to_Z c_lo) *
                2 ^ (64 * Z.of_nat pos))
             with
               ((((to_Z x * to_Z y_i) mod base width + to_Z c_hi) *
                  2 ^ (64 * Z.of_nat (S pos)))
                 + (to_Z_words result
                    + to_Z c_lo * 2 ^ (64 * Z.of_nat pos)))
             by (rewrite !pow64_succ; ring).
           rewrite <- Zplus_mod_idemp_l.
           rewrite add_low_limb_shift_mod.
           rewrite Zplus_mod_idemp_l.
           replace
             (((to_Z x * to_Z y_i + to_Z c_hi) *
               2 ^ (64 * Z.of_nat (S pos)))
              + (to_Z_words result + to_Z c_lo * 2 ^ (64 * Z.of_nat pos)))
             with
               (to_Z_words result
                + (to_Z x * to_Z y_i * base width
                   + to_Z c_hi * base width + to_Z c_lo) *
                  2 ^ (64 * Z.of_nat pos))
             by (rewrite !pow64_succ; ring).
           replace (to_Z_words (x :: rest))
             with (to_Z x + base width * to_Z_words rest) by reflexivity.
           replace
             (to_Z_words result
              + ((to_Z x + base width * to_Z_words rest) * to_Z y_i *
                 base width + to_Z c_hi * base width + to_Z c_lo) *
                2 ^ (64 * Z.of_nat pos))
             with
               ((to_Z_words result
                 + (to_Z x * to_Z y_i * base width
                    + to_Z c_hi * base width + to_Z c_lo) *
                   2 ^ (64 * Z.of_nat pos))
                + (to_Z_words rest * to_Z y_i) *
                  2 ^ (64 * Z.of_nat (S (S pos))))
             by (rewrite !pow64_succ; ring).
           rewrite add_shifted_term_mod.
           reflexivity.
        -- apply Nat.ltb_ge in Hpos1.
           assert (HR : R = S pos) by lia.
           change MakeProofsOn.set_word with set_word.
           change MakeProofsOn.get_word with get_word.
           rewrite (IH y_i
             (set_word result pos (get_word result pos + c_lo)%Uint) (S J) I R
             c_hi c_lo).
           2:{ rewrite set_word_length_local. exact Hlen. }
           2:{ cbn [length] in HRbound. subst pos. lia. }
           rewrite HR.
           replace (I + S J)%nat with R by (subst pos; lia).
           rewrite <- Zplus_mod_idemp_r.
           rewrite shifted_term_mod_0 by lia.
           rewrite Z.add_0_r.
           rewrite set_word_add_last_mod.
           2:{ rewrite HR in Hlen. exact Hlen. }
           replace (to_Z_words (x :: rest))
             with (to_Z x + base width * to_Z_words rest) by reflexivity.
           replace
             (to_Z_words result
              + ((to_Z x + base width * to_Z_words rest) * to_Z y_i *
                 base width + to_Z c_hi * base width + to_Z c_lo) *
                2 ^ (64 * Z.of_nat pos))
             with
               ((to_Z_words result + to_Z c_lo * 2 ^ (64 * Z.of_nat pos))
                + (to_Z x * to_Z y_i
                   + to_Z_words rest * to_Z y_i * base width + to_Z c_hi) *
                  2 ^ (64 * Z.of_nat (S pos)))
             by (rewrite !pow64_succ; ring).
           rewrite add_shifted_term_mod.
           reflexivity.
    + apply Nat.ltb_ge in Hpos.
      rewrite <- Zplus_mod_idemp_r.
      rewrite shifted_term_mod_0 by (subst pos; lia).
      cbn; rewrite Z.add_0_r; reflexivity.
Qed.

Lemma mul_add_line_recur_full_correct :
  forall xs_tail (y_i : t) result J I R (c_hi c_lo : t),
  length result = R ->
  carry_pair_bounded c_hi c_lo ->
  (forall j, (I + J + length xs_tail + 1 <= j)%nat -> (j < R)%nat ->
     get_word result j = zero) ->
  to_Z_words (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo)
    mod modulus_words R
  = (to_Z_words result
     + (to_Z_words xs_tail * to_Z y_i * base width
        + to_Z c_hi * base width + to_Z c_lo)
       * 2 ^ (64 * Z.of_nat (I + J)))
    mod modulus_words R
  /\
  (forall j, (I + J + S (length xs_tail) + 1 <= j)%nat -> (j < R)%nat ->
     get_word (mul_add_line_recur xs_tail y_i result J I R c_hi c_lo) j = zero).
Proof.
  induction xs_tail as [|x rest IH];
    intros y_i result J I R c_hi c_lo Hlen Hbound Hzero.
  - remember (I + J)%nat as pos eqn:Hpos_def in *.
    cbn [mul_add_line_recur to_Z_words].
    cbn [length] in Hzero.
    destruct (Nat.ltb (pos + 1) R) eqn:Hpos1.
    + apply Nat.ltb_lt in Hpos1.
      destruct (adc_2_short c_hi c_lo (MakeProofsOn.get_word result pos))
        as [r1 r0] eqn:Hadc.
      change (MakeProofsOn.set_word (MakeProofsOn.set_word result pos r0)
        (pos + 1) r1) with (set_word (set_word result pos r0) (pos + 1) r1).
      split.
      * assert (Hzero1 : get_word result (S pos) = zero).
        { replace (pos + 0 + 1)%nat with (pos + 1)%nat in Hzero by lia.
          replace (S pos) with (pos + 1)%nat by lia.
          exact (Hzero (pos + 1)%nat (Nat.le_refl _) Hpos1). }
        replace (I + J)%nat with pos by exact Hpos_def.
        assert (Hpos1_eq : (pos + 1 <? R)%nat = true)
          by (apply Nat.ltb_lt; exact Hpos1).
        rewrite Hpos1_eq.
        rewrite Hadc.
        replace (pos + 1)%nat with (S pos) by lia.
        replace
          (to_Z_words result
           + (0 * to_Z y_i * base width + to_Z c_hi * base width + to_Z c_lo) *
             2 ^ (64 * Z.of_nat pos))
          with
            (to_Z_words result
             + (to_Z c_hi * base width + to_Z c_lo) * modulus_words pos).
        2:{ rewrite <- pow64_modulus_words. ring. }
        eapply adc_2_short_carry_step_zero_mod.
        -- exact Hlen.
        -- lia.
        -- exact Hbound.
        -- exact Hzero1.
        -- exact Hadc.
      * intros j Hj HjR.
        replace (I + J)%nat with pos by exact Hpos_def.
        assert (Hpos1_eq : (pos + 1 <? R)%nat = true)
          by (apply Nat.ltb_lt; exact Hpos1).
        rewrite Hpos1_eq.
        rewrite Hadc.
        rewrite get_set_word_other_local by lia.
        rewrite get_set_word_other_local by lia.
        apply Hzero; subst pos; lia.
    + destruct (Nat.ltb pos R) eqn:Hpos.
      * apply Nat.ltb_lt in Hpos.
        apply Nat.ltb_ge in Hpos1.
        assert (HR : R = S pos) by lia.
        split.
        -- replace (I + J)%nat with pos by exact Hpos_def.
           replace (pos + 1 <? R)%nat with false
             by (symmetry; apply Nat.ltb_ge; lia).
           replace (pos <? R)%nat with true
             by (symmetry; apply Nat.ltb_lt; lia).
           change MakeProofsOn.set_word with set_word.
           change MakeProofsOn.get_word with get_word.
           rewrite HR.
           rewrite set_word_add_last_with_high_mod with (c_hi := c_hi) by lia.
           rewrite width_is_64; unfold base.
           f_equal; lia.
        -- intros j Hj HjR. subst pos. exfalso. lia.
      * apply Nat.ltb_ge in Hpos.
        split.
        -- rewrite <- Zplus_mod_idemp_r.
           replace (I + J + 1 <? R)%nat with false
             by (symmetry; apply Nat.ltb_ge; lia).
           replace (I + J <? R)%nat with false
             by (symmetry; apply Nat.ltb_ge; lia).
           rewrite shifted_term_mod_0 by (subst pos; lia).
           rewrite Z.add_0_r. reflexivity.
        -- intros j Hj HjR. subst pos. exfalso. lia.
  - remember (I + J)%nat as pos eqn:Hpos_def in *.
    cbn [mul_add_line_recur to_Z_words].
    change MakeProofsOn.set_word with set_word.
    change MakeProofsOn.get_word with get_word.
    destruct (Nat.ltb pos R) eqn:Hpos.
    + apply Nat.ltb_lt in Hpos.
      destruct (Nat.ltb (pos + 2) R) eqn:Hpos2.
      * apply Nat.ltb_lt in Hpos2.
        destruct (mulx x y_i) as [hi lo] eqn:Hmulx.
        destruct (adc_3 hi lo (get_word result pos) c_hi c_lo)
          as [[c_hi' c_lo'] res] eqn:Hadc.
        destruct (IH y_i (set_word result pos res) (S J) I R c_hi' c_lo')
          as [Hcorr Htail].
        1:{ rewrite set_word_length_local. exact Hlen. }
        1:{ eapply adc_3_carry_pair_bounded; eauto. }
        1:{ intros k Hk HkR.
            rewrite get_set_word_other_local by lia.
            apply Hzero; subst pos; simpl; lia. }
        split.
        -- replace ((I + J <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace ((I + J + 2 <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace (I + J)%nat with pos by lia.
           rewrite Hadc.
           rewrite Hcorr.
           replace (I + S J)%nat with (S pos) by (subst pos; lia).
           replace
             (to_Z_words (set_word result pos res)
              + (to_Z_words rest * to_Z y_i * base width
                 + to_Z c_hi' * base width + to_Z c_lo') *
                2 ^ (64 * Z.of_nat (S pos)))
             with
               ((to_Z_words (set_word result pos res)
                 + (to_Z c_hi' * base width + to_Z c_lo') *
                   2 ^ (64 * Z.of_nat (S pos)))
                + to_Z_words rest * to_Z y_i *
                  2 ^ (64 * Z.of_nat (S (S pos)))).
           2:{ replace (2 ^ (64 * Z.of_nat (S (S pos))))
                 with (base width * 2 ^ (64 * Z.of_nat (S pos)))
                 by (symmetry; apply pow64_succ).
               ring. }
           rewrite <- Zplus_mod_idemp_l.
           rewrite pow64_modulus_words.
           rewrite (adc_3_mul_step_mod_words result pos R x y_i hi lo c_hi c_lo
             c_hi' c_lo' res Hlen Hpos Hmulx Hadc).
           rewrite Zplus_mod_idemp_l, !pow64_modulus_words, !modulus_words_succ.
           subst pos.
           change (to_Z_words (x :: rest))
             with (to_Z x + base width * to_Z_words rest).
           apply (f_equal (fun z => z mod modulus_words R)); ring.
        -- intros j Hj HjR.
           replace ((I + J <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace ((I + J + 2 <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace (I + J)%nat with pos by lia.
           rewrite Hadc.
           apply Htail; [subst pos; simpl in *; lia | exact HjR].
      * apply Nat.ltb_ge in Hpos2.
        destruct (Nat.ltb (pos + 1) R) eqn:Hpos1.
        -- apply Nat.ltb_lt in Hpos1.
           assert (HR : R = S (S pos)) by lia.
           assert (Hlen2 : length result = S (S pos)).
           { rewrite <- HR. exact Hlen. }
           destruct (adc_2_full (mul x y_i) (MakeProofsOn.get_word result pos)
                      c_hi c_lo) as [c_lo' res] eqn:Hadc.
           replace ((I + J <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace ((I + J + 2 <? R)%nat) with false
             by (symmetry; apply Nat.ltb_ge; lia).
           replace ((I + J + 1 <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace (I + J)%nat with pos by lia.
           change MakeProofsOn.get_word with get_word in Hadc.
           rewrite Hadc.
           rewrite (mul_add_line_recur_correct
             rest y_i (set_word result pos res) (S J) I R c_hi c_lo').
           2:{ rewrite set_word_length_local. exact Hlen. }
           2:{ cbn [length]. subst pos. lia. }
           split.
           ++ rewrite HR.
              replace (I + S J)%nat with (S pos) by (subst pos; lia).
              replace
                (to_Z_words (set_word result pos res)
                 + (to_Z_words rest * to_Z y_i * base width
                    + to_Z c_hi * base width + to_Z c_lo') *
                   2 ^ (64 * Z.of_nat (S pos)))
                with
                  ((to_Z_words (set_word result pos res)
                    + to_Z c_lo' * 2 ^ (64 * Z.of_nat (S pos)))
                   + (to_Z_words rest * to_Z y_i + to_Z c_hi) *
                     2 ^ (64 * Z.of_nat (S (S pos))))
                by (rewrite !pow64_succ; ring).
              rewrite add_shifted_term_mod.
              rewrite pow64_modulus_words.
              rewrite (adc_2_full_mul_step_mod_words result pos x y_i c_hi c_lo
                c_lo' res Hlen2 Hadc).
              rewrite <- pow64_modulus_words.
              rewrite spec_mul.
              replace
                (to_Z_words result
                 + (((to_Z x * to_Z y_i) mod base width) * base width
                    + to_Z c_hi * base width + to_Z c_lo) *
                   2 ^ (64 * Z.of_nat pos))
                with
                  ((((to_Z x * to_Z y_i) mod base width + to_Z c_hi) *
                     2 ^ (64 * Z.of_nat (S pos)))
                    + (to_Z_words result
                       + to_Z c_lo * 2 ^ (64 * Z.of_nat pos)))
                by (rewrite !pow64_succ; ring).
              rewrite <- Zplus_mod_idemp_l.
              rewrite add_low_limb_shift_mod.
              rewrite Zplus_mod_idemp_l.
              replace
                (((to_Z x * to_Z y_i + to_Z c_hi) *
                  2 ^ (64 * Z.of_nat (S pos)))
                 + (to_Z_words result + to_Z c_lo * 2 ^ (64 * Z.of_nat pos)))
                with
                  (to_Z_words result
                   + (to_Z x * to_Z y_i * base width
                      + to_Z c_hi * base width + to_Z c_lo) *
                     2 ^ (64 * Z.of_nat pos))
                by (rewrite !pow64_succ; ring).
              replace (to_Z_words (x :: rest))
                with (to_Z x + base width * to_Z_words rest) by reflexivity.
              replace
                (to_Z_words result
                 + ((to_Z x + base width * to_Z_words rest) * to_Z y_i *
                    base width + to_Z c_hi * base width + to_Z c_lo) *
                   2 ^ (64 * Z.of_nat pos))
                with
                  ((to_Z_words result
                    + (to_Z x * to_Z y_i * base width
                       + to_Z c_hi * base width + to_Z c_lo) *
                      2 ^ (64 * Z.of_nat pos))
                   + (to_Z_words rest * to_Z y_i) *
                     2 ^ (64 * Z.of_nat (S (S pos))))
                by (rewrite !pow64_succ; ring).
              rewrite add_shifted_term_mod.
              reflexivity.
           ++ intros j Hj HjR. exfalso. subst pos. lia.
        -- apply Nat.ltb_ge in Hpos1.
           assert (HR : R = S pos) by lia.
           replace ((I + J <? R)%nat) with true
             by (symmetry; apply Nat.ltb_lt; lia).
           replace ((I + J + 2 <? R)%nat) with false
             by (symmetry; apply Nat.ltb_ge; lia).
           replace ((I + J + 1 <? R)%nat) with false
             by (symmetry; apply Nat.ltb_ge; lia).
           replace (I + J)%nat with pos by lia.
           change MakeProofsOn.set_word with set_word.
           change MakeProofsOn.get_word with get_word.
           rewrite (mul_add_line_recur_correct
             rest y_i (set_word result pos (get_word result pos + c_lo)%Uint)
             (S J) I R c_hi c_lo).
           2:{ rewrite set_word_length_local. exact Hlen. }
           2:{ cbn [length]. subst pos. lia. }
           split.
           ++ rewrite HR.
              replace (I + S J)%nat with R by (subst pos; lia).
              rewrite <- Zplus_mod_idemp_r.
              rewrite shifted_term_mod_0 by lia.
              rewrite Z.add_0_r.
              rewrite set_word_add_last_mod.
              2:{ rewrite HR in Hlen. exact Hlen. }
              replace (to_Z_words (x :: rest))
                with (to_Z x + base width * to_Z_words rest) by reflexivity.
              replace
                (to_Z_words result
                 + ((to_Z x + base width * to_Z_words rest) * to_Z y_i *
                    base width + to_Z c_hi * base width + to_Z c_lo) *
                   2 ^ (64 * Z.of_nat pos))
                with
                  ((to_Z_words result + to_Z c_lo * 2 ^ (64 * Z.of_nat pos))
                   + (to_Z x * to_Z y_i
                      + to_Z_words rest * to_Z y_i * base width + to_Z c_hi) *
                     2 ^ (64 * Z.of_nat (S pos)))
                by (rewrite !pow64_succ; ring).
              rewrite add_shifted_term_mod.
              reflexivity.
           ++ intros j Hj HjR. exfalso. subst pos. lia.
    + apply Nat.ltb_ge in Hpos.
      replace ((I + J <? R)%nat) with false
        by (symmetry; apply Nat.ltb_ge; lia).
      split.
      * rewrite <- Zplus_mod_idemp_r.
        rewrite shifted_term_mod_0 by (subst pos; lia).
        cbn; rewrite Z.add_0_r; reflexivity.
      * intros j Hj HjR. subst pos. exfalso. lia.
Qed.

Lemma mul_line_recur_zero_tail : forall xs (y : t) result I R (carry : t),
  length result = R ->
  (forall j, (I <= j)%nat -> (j < R)%nat -> get_word result j = zero) ->
  forall j, (I + length xs + 1 <= j)%nat -> (j < R)%nat ->
    get_word (mul_line_recur xs y result I R carry) j = zero.
Proof.
  induction xs as [|x rest IH]; intros y result I R carry Hlen Hzero j Hj HjR;
    simpl.
  - destruct (Nat.ltb I R) eqn:HI.
    + eapply zero_tail_after_set_word_local.
      * exact Hzero.
      * lia.
      * exact HjR.
    + apply Hzero; lia.
  - destruct (Nat.ltb I R) eqn:HI.
    + destruct (Nat.ltb (I + 1) R) eqn:HI1.
      * destruct (mulx x y) as [hi lo].
        destruct (adc_2_short hi lo carry) as [new_carry res_I].
        eapply IH.
        -- rewrite set_word_length_local. exact Hlen.
        -- eapply zero_tail_after_set_word_local. exact Hzero.
        -- simpl in Hj; lia.
        -- exact HjR.
      * eapply zero_tail_after_set_word_local.
        -- exact Hzero.
        -- lia.
        -- exact HjR.
    + apply Hzero; lia.
Qed.

Lemma mul_line_zero_tail : forall R xs (y : t),
  (0 < length xs)%nat ->
  (0 < R)%nat ->
  forall j, (S (length xs) <= j)%nat -> (j < R)%nat ->
    get_word (mul_line R xs y) j = zero.
Proof.
  intros R xs y Hxs HR j Hj HjR.
  destruct xs as [|x0 rest].
  - simpl in Hxs. lia.
  - unfold mul_line.
    destruct (mulx y x0) as [carry lo].
    eapply (mul_line_recur_zero_tail
      rest y (set_word (extend_words R) 0 lo) 1 R carry).
    + rewrite set_word_length_local, extend_words_length_local.
      reflexivity.
    + intros k Hk HkR.
      rewrite get_set_word_other_local by lia.
      apply get_extend_words_zero.
      exact HkR.
    + simpl in Hj; lia.
    + exact HjR.
Qed.

Lemma mul_add_line_zero_tail : forall I R xs (y_i : t) result,
  (0 < length xs)%nat ->
  length result = R ->
  (forall j, (I + length xs <= j)%nat -> (j < R)%nat ->
     get_word result j = zero) ->
  forall j, (I + S (length xs) <= j)%nat -> (j < R)%nat ->
    get_word (mul_add_line I R xs y_i result) j = zero.
Proof.
  intros I R xs y_i result Hxs Hlen Hzero j Hj HjR.
  destruct xs as [|x0 rest].
  - simpl in Hxs. lia.
  - unfold mul_add_line.
    destruct (Nat.ltb (I + 1) R) eqn:HI1.
    + destruct (mulx x0 y_i) as [c_hi c_lo] eqn:Hmulx.
      assert (Hzero' :
        forall k, (I + 0 + length rest + 1 <= k)%nat -> (k < R)%nat ->
          get_word result k = zero).
      { intros k Hk HkR.
        apply Hzero; cbn [length]; lia. }
      pose proof
        (mul_add_line_recur_full_correct
           rest y_i result 0 I R c_hi c_lo Hlen
           (mulx_carry_pair_bounded _ _ _ _ Hmulx)
           Hzero')
        as [_ Htail].
      apply Htail.
      * cbn [length] in Hj. lia.
      * exact HjR.
    + apply Nat.ltb_ge in HI1.
      cbn [length] in Hj. lia.
Qed.

(** * Row-Level Correctness *)

Lemma mul_line_correct : forall R xs (y : t),
  (0 < length xs)%nat ->
  (0 < R)%nat ->
  to_Z_words (mul_line R xs y) mod modulus_words R
  = (to_Z y * to_Z_words xs) mod modulus_words R.
Proof.
  intros R xs y Hxs HR.
  destruct xs as [|x0 rest].
  - simpl in Hxs. lia.
  - unfold mul_line.
    destruct (mulx y x0) as [carry lo] eqn:Hmulx.
    pose proof
      (mul_line_recur_correct rest y (set_word (extend_words R) 0 lo) 1 R
         carry) as Hrecur.
    assert (Hlen :
      length (set_word (extend_words R) 0 lo) = R).
    { rewrite set_word_length_local, extend_words_length_local.
      reflexivity. }
    assert (Hzero :
      forall j, (1 <= j)%nat -> (j < R)%nat ->
        get_word (set_word (extend_words R) 0 lo) j = zero).
    { intros j Hj HjR.
      rewrite get_set_word_other_local by lia.
      apply get_extend_words_zero.
      exact HjR. }
    specialize (Hrecur Hlen ltac:(lia) Hzero).
    change (MakeProofsOn.set_word (MakeProofsOn.extend_words R) 0 lo)
      with (set_word (extend_words R) 0 lo).
    rewrite Hrecur.
    assert (Hinit :
      to_Z_words (set_word (extend_words R) 0 lo) = to_Z lo).
    { rewrite to_Z_words_set_word_zero_local.
      2:{ rewrite extend_words_length_local. lia. }
      2:{ apply get_extend_words_zero. lia. }
      rewrite to_Z_extend_words.
      simpl Z.of_nat.
      rewrite Z.pow_0_r.
      ring. }
    rewrite Hinit.
    pose proof (spec_mulx y x0) as Hmul.
    rewrite Hmulx in Hmul.
    replace (to_Z_words (x0 :: rest))
      with (to_Z x0 + base width * to_Z_words rest) by reflexivity.
    replace (2 ^ (64 * Z.of_nat 1)) with (base width).
    2:{ unfold base. rewrite width_is_64. simpl. lia. }
    replace
      (to_Z lo + (to_Z_words rest * to_Z y + to_Z carry) * base width)
      with
        (to_Z carry * base width + to_Z lo
         + to_Z_words rest * to_Z y * base width) by ring.
    rewrite Hmul.
    ring_simplify.
    replace
      (to_Z y * to_Z x0 + to_Z_words rest * to_Z y * base width)
      with
        (to_Z y * (to_Z x0 + base width * to_Z_words rest)) by ring.
    reflexivity.
Qed.

Lemma mul_add_line_correct : forall I R xs (y_i : t) result,
  (0 < length xs)%nat ->
  length result = R ->
  (forall j, (I + length xs <= j)%nat -> (j < R)%nat ->
     get_word result j = zero) ->
  to_Z_words (mul_add_line I R xs y_i result) mod modulus_words R
  = (to_Z_words result + to_Z y_i * to_Z_words xs * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof.
  intros I R xs y_i result Hxs Hlen Hzero.
  destruct xs as [|x0 rest].
  - simpl in Hxs. lia.
  - unfold mul_add_line.
    destruct (Nat.ltb (I + 1) R) eqn:HI1.
    + destruct (mulx x0 y_i) as [c_hi c_lo] eqn:Hmulx.
      assert (Hzero' :
        forall k, (I + 0 + length rest + 1 <= k)%nat -> (k < R)%nat ->
          get_word result k = zero).
      { intros k Hk HkR.
        apply Hzero; cbn [length]; lia. }
      pose proof
        (mul_add_line_recur_full_correct
           rest y_i result 0 I R c_hi c_lo Hlen
           (mulx_carry_pair_bounded _ _ _ _ Hmulx) Hzero')
        as [Hcorr _].
      rewrite Hcorr.
      change (to_Z_words (x0 :: rest))
        with (to_Z x0 + base width * to_Z_words rest).
      pose proof (spec_mulx x0 y_i) as Hmul.
      rewrite Hmulx in Hmul.
      replace (2 ^ (64 * Z.of_nat (I + 0))) with (2 ^ (64 * Z.of_nat I)).
      2:{ replace (Z.of_nat (I + 0)) with (Z.of_nat I) by lia.
          reflexivity. }
      replace
        (to_Z_words rest * to_Z y_i * base width
         + to_Z c_hi * base width + to_Z c_lo)
        with
          (to_Z c_hi * base width + to_Z c_lo
           + to_Z_words rest * to_Z y_i * base width) by ring.
      rewrite Hmul.
      ring_simplify.
      replace
        (to_Z x0 * to_Z y_i + to_Z_words rest * to_Z y_i * base width)
        with
          (to_Z y_i * (to_Z x0 + base width * to_Z_words rest)) by ring.
      reflexivity.
    + apply Nat.ltb_ge in HI1.
      change 0 with zero.
      pose proof
        (mul_add_line_recur_correct
           rest y_i result 0 I R zero (mul x0 y_i) Hlen)
        as Hcorr.
      assert (HRbound : (R <= I + 0 + length rest + 1)%nat) by lia.
      specialize (Hcorr HRbound).
      rewrite Hcorr.
      change (to_Z_words (x0 :: rest))
        with (to_Z x0 + base width * to_Z_words rest).
      rewrite spec_zero, spec_mul.
      destruct (Nat.ltb I R) eqn:HI.
      * apply Nat.ltb_lt in HI.
        assert (HR : R = S I) by lia.
        subst R.
        rewrite HR.
        replace (2 ^ (64 * Z.of_nat (I + 0))) with (2 ^ (64 * Z.of_nat I)).
        2:{ replace (Z.of_nat (I + 0)) with (Z.of_nat I) by lia.
            reflexivity. }
        replace
          (to_Z_words result
           + (to_Z_words rest * to_Z y_i * base width
              + 0 * base width
              + (to_Z x0 * to_Z y_i) mod base width)
             * 2 ^ (64 * Z.of_nat I))
          with
            ((to_Z_words result
              + ((to_Z x0 * to_Z y_i) mod base width) *
                2 ^ (64 * Z.of_nat I))
             + (to_Z_words rest * to_Z y_i) *
               2 ^ (64 * Z.of_nat (S I)))
          by (rewrite pow64_succ; ring).
        rewrite add_shifted_term_mod.
        rewrite <- Zplus_mod_idemp_r.
        rewrite low_limb_shift_mod.
        rewrite Zplus_mod_idemp_r.
        replace
          (to_Z_words result
           + to_Z y_i * (to_Z x0 + base width * to_Z_words rest) *
             2 ^ (64 * Z.of_nat I))
          with
            ((to_Z_words result
              + to_Z x0 * to_Z y_i * 2 ^ (64 * Z.of_nat I))
             + (to_Z_words rest * to_Z y_i) *
               2 ^ (64 * Z.of_nat (S I)))
          by (rewrite pow64_succ; ring).
        rewrite add_shifted_term_mod.
        reflexivity.
      * apply Nat.ltb_ge in HI.
        transitivity (to_Z_words result mod modulus_words R).
        -- rewrite <- Zplus_mod_idemp_r.
           rewrite shifted_term_mod_0 by lia.
           rewrite Z.add_0_r.
           reflexivity.
        -- symmetry.
           rewrite <- Zplus_mod_idemp_r.
           rewrite shifted_term_mod_0 by lia.
           rewrite Z.add_0_r.
           reflexivity.
Qed.

(** * General Word-List Theorem *)

Lemma truncating_mul_runtime_recur_correct : forall xs ys_tail result I R,
  (0 < length xs)%nat ->
  length result = R ->
  (forall j, (I + length xs <= j)%nat -> (j < R)%nat ->
     get_word result j = zero) ->
  to_Z_words (truncating_mul_runtime_recur xs ys_tail result I R)
    mod modulus_words R
  = (to_Z_words result
      + to_Z_words xs * to_Z_words ys_tail * 2^(64 * Z.of_nat I))
    mod modulus_words R.
Proof.
  induction ys_tail as [|y_i rest IH]; intros result I R Hxs Hlen Hzero.
  - cbn [truncating_mul_runtime_recur to_Z_words].
    rewrite Z.mul_0_r, Z.add_0_r.
    reflexivity.
  - cbn [truncating_mul_runtime_recur].
    pose proof (mul_add_line_correct I R xs y_i result Hxs Hlen Hzero) as Hrow.
    pose proof
      (IH (mul_add_line I R xs y_i result) (S I) R Hxs
          (mul_add_line_length I R xs y_i result Hlen)
          (fun j Hj HjR => mul_add_line_zero_tail I R xs y_i result Hxs Hlen
             Hzero j ltac:(lia) HjR)) as Hrest.
    rewrite Hrest, Zplus_mod, Hrow.
    rewrite <- Zplus_mod.
    cbn [to_Z_words].
    rewrite pow64_succ, width_is_64; unfold base.
    f_equal.
    ring.
Qed.

Theorem truncating_mul_runtime_correct : forall xs ys R,
  (0 < length xs)%nat ->
  (0 < length ys)%nat ->
  (0 < R)%nat ->
  (R <= length xs + length ys)%nat ->
  to_Z_words (truncating_mul_runtime xs ys R) mod modulus_words R
  = (to_Z_words xs * to_Z_words ys) mod modulus_words R.
Proof.
  intros xs ys R Hxs Hys HR Hbound.
  destruct ys as [|y ys_tail].
  - simpl in Hys. lia.
  - cbn [truncating_mul_runtime].
    pose proof (mul_line_correct R xs y Hxs HR) as Hline.
    pose proof
      (truncating_mul_runtime_recur_correct
         xs ys_tail (mul_line R xs y) 1 R Hxs (mul_line_length R xs y)
         (fun j Hj HjR => mul_line_zero_tail R xs y Hxs HR j Hj HjR))
      as Htail.
    rewrite Htail, Zplus_mod, Hline.
    rewrite <- Zplus_mod.
    cbn [to_Z_words].
    rewrite Z.mul_add_distr_l, Z.mul_assoc, width_is_64.
    unfold base.
    f_equal.
    lia.
Qed.

(** * Main 256-bit Theorem *)

Theorem truncating_mul256_runtime_correct : forall (x y : words),
  length x = 4%nat ->
  length y = 4%nat ->
  to_Z_words (truncating_mul_runtime x y 4) mod modulus_words 4
  = (to_Z_words x * to_Z_words y) mod modulus_words 4.
Proof.
  intros x y Hx Hy.
  apply truncating_mul_runtime_correct; lia.
Qed.

(* Checked in concrete models:
   Print Assumptions truncating_mul_runtime_correct.*)

End MakeProofsOn.

Module MakeProofs (Import Word64 : Uint64).
Module B := Base.MakeProof(Word64).
Module RM := RuntimeMul.MakeOnProof(B).
Module WL := WordsLemmas.MakeProofsOn(B).
Include MakeProofsOn(B)(RM)(WL).
End MakeProofs.
