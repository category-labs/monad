From Stdlib Require Import ZArith Zquot Lia List Bool.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint Base Words WordsLemmas RuntimeMul Division.
From Uint256 Require Import Arithmetic Barrett RuntimeMulProofs DivisionProofs.
From Uint256 Require Import ArithmeticProofs.

Import ListNotations.

Module MakeProofs (B : Base.BaseProofSig) (U128 : Uint128)
  (Bridge : UintWiden B.U64 U128)
  (WL : WordsLemmas.WordsLemmasProofSig with Module U64 := B.U64)
  (Div : Division.DivisionProofSig(B)(U128)(Bridge))
  (DP : DivisionProofs.DivisionProofsSig(B)(U128)(Bridge)(Div)(WL))
  (RM : RuntimeMul.RuntimeMulProofSig with Module U64 := B.U64)
  (RMP : RuntimeMulProofs.RuntimeMulProofsSig(B)(RM)(WL))
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM))
  (Bar : Barrett.BarrettSig(B)(U128)(Bridge)(Div)(RM)(Arith)).
Module AP := ArithmeticProofs.MakeProofs(B)(U128)(Bridge)(WL)(RM)(RMP)(Div)(DP)(Arith).
Import B.U64.

Open Scope Z_scope.

Local Notation to_Z_words := WL.to_Z_words.
Local Notation modulus_words := WL.modulus_words.

Definition modulus256 : Z := modulus_words 4%nat.
Definition sign_threshold256 : Z := modulus256 / 2.

Definition to_Z_uint256 (x : Bar.uint256) : Z :=
  to_Z_words (Bar.uint256_to_words x).

Definition params_admissible (params : Bar.BarrettParams) : Prop :=
  0 < to_Z_uint256 (Bar.min_denominator params) /\
  to_Z_uint256 (Bar.min_denominator params) <=
    to_Z_uint256 (Bar.max_denominator params) /\
  (0 < Bar.input_bits params)%nat.

Definition uint256_fits_words (n : nat) (x : Bar.uint256) : Prop :=
  to_Z_uint256 x < modulus_words n.

Definition to_Z_signed_uint256 (x : Bar.uint256) : Z :=
  let ux := to_Z_uint256 x in
  if Z.ltb ux sign_threshold256 then ux else ux - modulus256.

Definition to_Z_signed_words (ws : Bar.words) : Z :=
  to_Z_signed_uint256 (Bar.words_to_uint256 ws).

Definition reciprocal_Z (rec : Bar.reciprocal) : Z :=
  to_Z_words (Bar.reciprocal_ rec).

Definition denominator_Z (rec : Bar.reciprocal) : Z :=
  to_Z_words (Bar.denominator_ rec).

Definition multiplier_Z (rec : Bar.reciprocal) : Z :=
  to_Z_words (Bar.multiplier_ rec).

Definition reciprocal_scale_factor (rec : Bar.reciprocal) : Z :=
  if Nat.eqb (Bar.multiplier_words (Bar.reciprocal_params rec)) 0%nat
  then 1
  else multiplier_Z rec.

Definition reciprocal_invariant (rec : Bar.reciprocal) : Prop :=
  let params := Bar.reciprocal_params rec in
  0 < denominator_Z rec /\
  reciprocal_Z rec =
    Z.div
      (reciprocal_scale_factor rec * 2 ^ (Z.of_nat (Bar.shift params)))
      (denominator_Z rec).

Definition input_value_Z (rec : Bar.reciprocal) (x : Bar.words) : Z :=
  let params := Bar.reciprocal_params rec in
  to_Z_words (Bar.fit_words (Bar.input_words params) x).

Definition input_within_bound (rec : Bar.reciprocal) (x : Bar.words) : Prop :=
  let params := Bar.reciprocal_params rec in
  0 <= input_value_Z rec x < 2 ^ (Z.of_nat (Bar.input_bits params)).

Definition online_numerator_Z (rec : Bar.reciprocal) (x : Bar.words) : Z :=
  to_Z_words (Bar.online_numerator rec x).

Definition estimate_q_Z (need_quotient : bool) (rec : Bar.reciprocal)
    (x : Bar.words) : Z :=
  to_Z_words (Bar.estimate_q need_quotient rec x).

Definition reduce_quot_Z (result : Bar.reduce_result) : Z :=
  to_Z_words (Bar.reduce_quot result).

Definition reduce_rem_Z (result : Bar.reduce_result) : Z :=
  to_Z_words (Bar.reduce_rem result).

Definition signed_divisor_Z (denominator_neg : bool) (rec : Bar.reciprocal) : Z :=
  if denominator_neg then - denominator_Z rec else denominator_Z rec.

Lemma uint256_to_words_length : forall x,
  length (Bar.uint256_to_words x) = 4%nat.
Proof.
  intros [x0 x1 x2 x3]. reflexivity.
Qed.

Lemma fit_words_length : forall n ws,
  length (Bar.fit_words n ws) = n.
Proof.
  intros n ws.
  unfold Bar.fit_words.
  rewrite firstn_length_le.
  - reflexivity.
  - rewrite length_app, repeat_length. lia.
Qed.

Lemma multiplier_words_zero : forall params,
  Bar.multiplier_bits params = 0%nat ->
  Bar.multiplier_words params = 0%nat.
Proof.
  intros params Hbits.
  unfold Bar.multiplier_words, Bar.min_words, Bar.word_width.
  rewrite Hbits, Nat.add_0_l.
  apply Nat.div_small.
  pose proof (Pos2Nat.is_pos Bar.U64.width).
  lia.
Qed.

Lemma to_Z_fit_words_small : forall n ws,
  to_Z_words ws < modulus_words n ->
  to_Z_words (Bar.fit_words n ws) = to_Z_words ws.
Proof.
  intros n ws Hsmall.
  unfold Bar.fit_words.
  destruct (Nat.leb_spec0 n (length ws)) as [Hle | Hgt].
  - rewrite firstn_app.
    replace (n - length ws)%nat with 0%nat by lia.
    cbn [firstn app].
    rewrite app_nil_r.
    pose proof (WL.to_Z_words_firstn_skipn ws n Hle) as Hsplit.
    pose proof (WL.to_Z_words_bound (firstn n ws)) as Hlow.
    rewrite firstn_length_le in Hlow by lia.
    pose proof (WL.to_Z_words_bound (skipn n ws)) as Hhigh.
    pose proof (WL.modulus_words_pos n) as Hmod.
    assert (Htail0 : to_Z_words (skipn n ws) = 0) by nia.
    rewrite Hsplit, Htail0. ring.
  - apply WL.to_Z_words_firstn_app_repeat. lia.
Qed.

Lemma to_Z_fit_uint256_words_small : forall n x,
  uint256_fits_words n x ->
  to_Z_words (Bar.fit_words n (Bar.uint256_to_words x)) = to_Z_uint256 x.
Proof.
  intros n x Hfits.
  unfold uint256_fits_words, to_Z_uint256 in Hfits |- *.
  now apply to_Z_fit_words_small.
Qed.

Lemma leb_uint256_correct : forall x y,
  Bar.leb_uint256 x y = (to_Z_uint256 x <=? to_Z_uint256 y).
Proof.
  intros x y.
  unfold Bar.leb_uint256.
  rewrite AP.ltb_uint256_correct.
  unfold AP.to_Z_uint256, to_Z_uint256.
  destruct (Z.ltb_spec (to_Z_words (Bar.uint256_to_words y))
              (to_Z_words (Bar.uint256_to_words x))).
  - symmetry. apply Z.leb_gt. lia.
  - symmetry. apply Z.leb_le. lia.
Qed.

Lemma valid_denominator_bounds : forall params d,
  Bar.valid_denominator params d = true ->
  to_Z_uint256 (Bar.min_denominator params) <= to_Z_uint256 d /\
  to_Z_uint256 d <= to_Z_uint256 (Bar.max_denominator params).
Proof.
  intros params d Hvalid.
  unfold Bar.valid_denominator in Hvalid.
  apply andb_true_iff in Hvalid as [Hmin Hmax].
  rewrite leb_uint256_correct in Hmin, Hmax.
  split; now apply Z.leb_le.
Qed.

Lemma valid_denominator_positive : forall params d,
  params_admissible params ->
  Bar.valid_denominator params d = true ->
  0 < to_Z_uint256 d.
Proof.
  intros params d Hadm Hvalid.
  destruct Hadm as [Hmin_pos _].
  pose proof (valid_denominator_bounds params d Hvalid) as [Hd_min _].
  lia.
Qed.

Lemma min_denominator_valid : forall params,
  params_admissible params ->
  Bar.valid_denominator params (Bar.min_denominator params) = true.
Proof.
  intros params Hadm.
  destruct Hadm as [_ [Hmin_le_max _]].
  unfold Bar.valid_denominator.
  rewrite !leb_uint256_correct.
  apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

Lemma Z_div_denominator_anti_nonneg : forall a b c,
  0 <= a ->
  0 < b ->
  b <= c ->
  a / c <= a / b.
Proof.
  intros a b c Ha Hb Hbc.
  assert (Hc : 0 < c) by lia.
  pose proof (Z.div_pos a c Ha ltac:(lia)) as Hq_nonneg.
  pose proof (Z.div_mod a c ltac:(lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound a c ltac:(lia)) as Hmod.
  apply Z.div_le_lower_bound; [exact Hb |].
  nia.
Qed.

Lemma min_words_bit_width_words : forall ws,
  Bar.min_words (Bar.bit_width_words ws) =
    Div.count_significant_words ws.
Proof.
  intro ws.
  unfold Bar.bit_width_words.
  destruct (Div.count_significant_words ws) as [|n] eqn:Hn.
  - unfold Bar.min_words, Bar.word_width.
    rewrite Nat.add_0_l.
    apply Nat.div_small.
    pose proof (Pos2Nat.is_pos Bar.U64.width).
    lia.
  - unfold Bar.min_words, Bar.bit_width_word, Bar.word_width.
    pose proof (DP.count_significant_words_msw_nonzero ws) as Hmsw.
    cbn zeta in Hmsw.
    rewrite Hn in Hmsw.
    assert (Hnpos : (S n > 0)%nat) by lia.
    specialize (Hmsw Hnpos).
    replace (S n - 1)%nat with n in Hmsw by lia.
    change (WL.get_word ws n) with (Bar.get_word ws n) in Hmsw.
    pose proof (DP.countl_zero_bound (Bar.get_word ws n) Hmsw) as Hcz.
    rewrite Bar.U64.width_is_64 in *.
    cbn [Pos.to_nat Nat.pred] in *.
    change (Pos.to_nat 64) with 64%nat.
    symmetry.
    apply Nat.div_unique
      with (r := (64 - Div.countl_zero (Bar.get_word ws n) - 1)%nat);
      lia.
Qed.

Lemma to_Z_words_count_significant_bound : forall ws,
  to_Z_words ws < modulus_words (Div.count_significant_words ws).
Proof.
  intro ws.
  rewrite <- (DP.count_significant_words_preserves_value ws).
  pose proof
    (WL.to_Z_words_bound
       (firstn (Div.count_significant_words ws) ws)) as Hbound.
  rewrite firstn_length_le in Hbound.
  - exact (proj2 Hbound).
  - apply DP.count_significant_words_bound.
Qed.

Lemma max_denominator_fits_words : forall params,
  uint256_fits_words
    (Bar.max_denominator_words params) (Bar.max_denominator params).
Proof.
  intro params.
  unfold uint256_fits_words, Bar.max_denominator_words.
  unfold Bar.max_denominator_bits, Bar.bit_width_uint256, to_Z_uint256.
  rewrite min_words_bit_width_words.
  apply to_Z_words_count_significant_bound.
Qed.

Lemma valid_denominator_fits_words : forall params d,
  Bar.valid_denominator params d = true ->
  uint256_fits_words (Bar.max_denominator_words params) d.
Proof.
  intros params d Hvalid.
  unfold uint256_fits_words.
  pose proof (valid_denominator_bounds params d Hvalid) as [_ Hd_max].
  pose proof (max_denominator_fits_words params) as Hmax.
  unfold uint256_fits_words in Hmax.
  lia.
Qed.

Lemma numerator_no_multiplier_value : forall params,
  Bar.multiplier_bits params = 0%nat ->
  to_Z_words (Bar.numerator params) =
    2 ^ Z.of_nat (Bar.input_bits params).
Proof.
  intros params Hbits.
  pose proof (multiplier_words_zero params Hbits) as Hmwords.
  unfold Bar.numerator, Bar.numerator_words.
  rewrite Hmwords. cbn [Nat.eqb].
  rewrite WL.to_Z_words_set_word.
  2: { rewrite WL.extend_words_length. lia. }
  rewrite WL.to_Z_extend_words.
  change (Bar.extend_words (S (Bar.word_shift params))) with
    (WL.extend_words (S (Bar.word_shift params))).
  rewrite WL.get_extend_words_Z by lia.
  rewrite AP.to_Z_shl_one.
  2: {
    unfold Bar.bit_shift, Bar.word_width.
    apply Nat.mod_upper_bound.
    pose proof (Pos2Nat.is_pos Bar.U64.width). lia. }
  replace (0 - 0 * (base width) ^ Z.of_nat (Bar.word_shift params) +
             2 ^ Z.of_nat (Bar.bit_shift params) *
             (base width) ^ Z.of_nat (Bar.word_shift params))
    with (2 ^ Z.of_nat (Bar.bit_shift params) *
          (base width) ^ Z.of_nat (Bar.word_shift params)) by ring.
  replace (base width) with (2 ^ 64).
  2: { unfold base. rewrite Bar.U64.width_is_64. reflexivity. }
  rewrite <- Z.pow_mul_r by lia.
  rewrite <- Z.pow_add_r by lia.
  f_equal.
  unfold Bar.bit_shift, Bar.word_shift, Bar.word_width.
  rewrite Bar.U64.width_is_64.
  change (Pos.to_nat 64) with 64%nat.
  pose proof (Nat.div_mod (Bar.input_bits params) 64 ltac:(lia)) as Hdm.
  unfold Bar.shift.
  replace (Z.of_nat (Bar.input_bits params)) with
    (Z.of_nat
       (64 * (Bar.input_bits params / 64) +
        Bar.input_bits params mod 64)%nat).
  2: { now rewrite <- Hdm. }
  rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
  change (Z.of_nat 64) with 64.
  lia.
Qed.

Lemma numerator_length : forall params,
  length (Bar.numerator params) = Bar.numerator_words params.
Proof.
  intro params.
  unfold Bar.numerator.
  rewrite WL.set_word_length, WL.extend_words_length.
  reflexivity.
Qed.

Lemma udivrem_positive_some : forall M N u v,
  0 < to_Z_words v ->
  exists r, Div.udivrem M N u v = Some r.
Proof.
  intros M N u v Hv_pos.
  unfold Div.udivrem.
  remember (Div.count_significant_words u) as m eqn:Hm.
  remember (Div.count_significant_words v) as n eqn:Hn.
  destruct (Nat.eqb n 0) eqn:Hn_zero.
  - apply Nat.eqb_eq in Hn_zero.
    assert (Hcsw : Div.count_significant_words v = 0%nat).
    { rewrite <- Hn. exact Hn_zero. }
    apply DP.count_significant_words_zero in Hcsw.
    lia.
  - apply Nat.eqb_neq in Hn_zero.
    destruct (Nat.ltb m n) eqn:Hm_lt.
    + eexists. reflexivity.
    + apply Nat.ltb_ge in Hm_lt.
      destruct (Nat.eqb m 1) eqn:Hm_one.
      * apply Nat.eqb_eq in Hm_one.
        subst m.
        assert (Hn_one : n = 1%nat) by lia.
        assert (Hcsw : Div.count_significant_words v = 1%nat).
        { rewrite <- Hn. exact Hn_one. }
        pose proof (DP.count_significant_words_msw_nonzero v) as Hv_msw.
        cbn zeta in Hv_msw.
        rewrite Hcsw in Hv_msw.
        specialize (Hv_msw ltac:(lia)).
        replace (1 - 1)%nat with 0%nat in Hv_msw by lia.
        change (WL.get_word v 0) with (Div.get_word v 0) in Hv_msw.
        destruct (spec_div zero (Div.get_word u 0) (Div.get_word v 0))
          as [q [r [Hdiv _]]].
        -- lia.
        -- rewrite spec_zero. lia.
        -- rewrite Hdiv. eexists. reflexivity.
      * destruct (Nat.eqb n 1).
        -- eexists. reflexivity.
        -- destruct (Div.knuth_div m n
             (Div.shift_left_words (firstn m u)
                (Div.countl_zero (Div.get_word v (n - 1))))
             (firstn n
                (Div.shift_left_words (firstn n v)
                   (Div.countl_zero (Div.get_word v (n - 1))))))
             as [u_after quot].
           eexists. reflexivity.
Qed.

Lemma udivrem_quotient_no_multiplier_exact : forall params d r,
  params_admissible params ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params) (Bar.uint256_to_words d) = Some r ->
  to_Z_words (Div.ud_quot r) =
    Z.div (2 ^ Z.of_nat (Bar.input_bits params)) (to_Z_uint256 d).
Proof.
  intros params d r Hadm Hbits Hvalid Hdiv.
  pose proof (valid_denominator_positive params d Hadm Hvalid) as Hd_pos.
  pose proof (DP.udivrem_correct
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params) (Bar.uint256_to_words d) r) as Hcorr.
  specialize (Hcorr (numerator_length params)).
  assert (Hd_len : length (Bar.uint256_to_words d) = Bar.uint256_num_words).
  { rewrite uint256_to_words_length. unfold Bar.uint256_num_words.
    reflexivity. }
  specialize (Hcorr Hd_len).
  unfold to_Z_uint256 in Hd_pos.
  specialize (Hcorr ltac:(lia) Hdiv).
  destruct Hcorr as [Hvalue Hrem].
  rewrite numerator_no_multiplier_value in Hvalue by exact Hbits.
  unfold to_Z_uint256.
  change (to_Z_words (Div.ud_quot r)) with (to_Z_words (DP.ud_quot r)).
  apply Z.div_unique with (r := to_Z_words (Div.ud_rem r)).
  - left. exact Hrem.
  - rewrite Hvalue. ring.
Qed.

Lemma reciprocal_words_no_multiplier : forall params rmin,
  Bar.multiplier_bits params = 0%nat ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params)
    (Bar.uint256_to_words (Bar.min_denominator params)) = Some rmin ->
  Bar.reciprocal_words params =
    Div.count_significant_words (Div.ud_quot rmin).
Proof.
  intros params rmin Hbits Hdiv.
  unfold Bar.reciprocal_words, Bar.reciprocal_bits.
  rewrite (multiplier_words_zero params Hbits). cbn [Nat.eqb].
  rewrite Hdiv.
  apply min_words_bit_width_words.
Qed.

Lemma reciprocal_quotient_no_multiplier_fits : forall params d r rmin,
  params_admissible params ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params) (Bar.uint256_to_words d) = Some r ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params)
    (Bar.uint256_to_words (Bar.min_denominator params)) = Some rmin ->
  to_Z_words (Div.ud_quot r) < modulus_words (Bar.reciprocal_words params).
Proof.
  intros params d r rmin Hadm Hbits Hvalid Hdiv Hdivmin.
  pose proof (valid_denominator_bounds params d Hvalid) as [Hmin_d _].
  destruct Hadm as [Hmin_pos Hadm_tail].
  assert (Hadm' : params_admissible params) by (repeat split; tauto || lia).
  pose proof
    (udivrem_quotient_no_multiplier_exact
       params d r Hadm' Hbits Hvalid Hdiv) as Hq.
  pose proof
    (udivrem_quotient_no_multiplier_exact
       params (Bar.min_denominator params) rmin Hadm' Hbits
       (min_denominator_valid params Hadm') Hdivmin) as Hqmin.
  assert (Hq_le : to_Z_words (Div.ud_quot r) <=
                  to_Z_words (Div.ud_quot rmin)).
  { rewrite Hq, Hqmin.
    apply Z_div_denominator_anti_nonneg.
    - apply Z.pow_nonneg. lia.
    - exact Hmin_pos.
    - exact Hmin_d. }
  rewrite (reciprocal_words_no_multiplier params rmin Hbits Hdivmin).
  pose proof (to_Z_words_count_significant_bound (Div.ud_quot rmin)).
  lia.
Qed.

Theorem constructor_sound_no_multiplier : forall params d,
  params_admissible params ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  reciprocal_invariant (Bar.reciprocal_of_denominator params d) /\
  denominator_Z (Bar.reciprocal_of_denominator params d) = to_Z_uint256 d /\
  multiplier_Z (Bar.reciprocal_of_denominator params d) = 0.
Proof.
  intros params d Hadm Hbits Hvalid.
  pose proof (valid_denominator_positive params d Hadm Hvalid) as Hd_pos.
  destruct (udivrem_positive_some
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params) (Bar.uint256_to_words d)) as [r Hdiv].
  { unfold to_Z_uint256 in Hd_pos. exact Hd_pos. }
  destruct (udivrem_positive_some
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator params)
    (Bar.uint256_to_words (Bar.min_denominator params))) as [rmin Hdivmin].
  { unfold params_admissible, to_Z_uint256 in Hadm. lia. }
  unfold reciprocal_invariant, denominator_Z, reciprocal_Z, multiplier_Z.
  unfold Bar.reciprocal_of_denominator.
  rewrite Hdiv.
  cbn [Bar.reciprocal_params Bar.denominator_ Bar.multiplier_
       Bar.reciprocal_].
  pose proof (valid_denominator_fits_words params d Hvalid) as Hd_fit.
  pose proof (to_Z_fit_uint256_words_small
    (Bar.max_denominator_words params) d Hd_fit) as Hden.
  pose proof (reciprocal_quotient_no_multiplier_fits
    params d r rmin Hadm Hbits Hvalid Hdiv Hdivmin) as Hq_fit.
  pose proof (to_Z_fit_words_small
    (Bar.reciprocal_words params) (Div.ud_quot r) Hq_fit) as Hq_fit_eq.
  pose proof (udivrem_quotient_no_multiplier_exact
    params d r Hadm Hbits Hvalid Hdiv) as Hq.
  rewrite Hden, Hq_fit_eq.
  unfold reciprocal_scale_factor.
  cbn [Bar.reciprocal_params Bar.multiplier_].
  rewrite (multiplier_words_zero params Hbits). cbn [Nat.eqb].
  unfold Bar.shift in Hq |- *.
  rewrite Hq.
  repeat split; try lia.
  replace (1 * 2 ^ Z.of_nat (Bar.input_bits params)) with
    (2 ^ Z.of_nat (Bar.input_bits params)) by ring.
  reflexivity.
Qed.

Theorem constructor_sound_with_multiplier : forall params y d,
  params_admissible params ->
  (0 < Bar.multiplier_bits params)%nat ->
  uint256_fits_words (Bar.multiplier_words params) y ->
  Bar.valid_denominator params d = true ->
  reciprocal_invariant (Bar.reciprocal_of_multiplier params y d) /\
  denominator_Z (Bar.reciprocal_of_multiplier params y d) = to_Z_uint256 d /\
  multiplier_Z (Bar.reciprocal_of_multiplier params y d) = to_Z_uint256 y.
Admitted.

Theorem estimate_q_sound_no_preshift : forall rec x,
  reciprocal_invariant rec ->
  Bar.pre_product_shift (Bar.reciprocal_params rec) = 0%nat ->
  input_within_bound rec x ->
  let Q := Z.div (online_numerator_Z rec x) (denominator_Z rec) in
  Q - 1 <= estimate_q_Z true rec x <= Q.
Admitted.

Theorem estimate_q_sound_with_preshift : forall rec x,
  reciprocal_invariant rec ->
  (0 < Bar.pre_product_shift (Bar.reciprocal_params rec))%nat ->
  input_within_bound rec x ->
  let Q := Z.div (online_numerator_Z rec x) (denominator_Z rec) in
  Q - 2 <= estimate_q_Z true rec x <= Q.
Admitted.

Theorem low_product_sufficient : forall rec x,
  reciprocal_invariant rec ->
  input_within_bound rec x ->
  let params := Bar.reciprocal_params rec in
  Z.modulo
    (estimate_q_Z false rec x * denominator_Z rec)
    (modulus_words (Bar.max_r_hat_words params)) =
  Z.modulo
    (estimate_q_Z true rec x * denominator_Z rec)
    (modulus_words (Bar.max_r_hat_words params)).
Admitted.

Theorem low_input_product_sufficient : forall rec x,
  reciprocal_invariant rec ->
  (0 < Bar.multiplier_bits (Bar.reciprocal_params rec))%nat ->
  input_within_bound rec x ->
  let params := Bar.reciprocal_params rec in
  Z.modulo
    (online_numerator_Z rec x)
    (modulus_words (Bar.max_r_hat_words params)) =
  Z.modulo
    (to_Z_words
       (Bar.truncating_mul (Bar.max_r_hat_words params)
          (Bar.fit_words (Bar.input_words params) x)
          (Bar.multiplier_ rec)))
    (modulus_words (Bar.max_r_hat_words params)).
Admitted.

Theorem reduce_correct_remainder_only : forall rec x,
  reciprocal_invariant rec ->
  input_within_bound rec x ->
  let result := Bar.reduce false rec x in
  reduce_rem_Z result = Z.modulo (online_numerator_Z rec x) (denominator_Z rec) /\
  0 <= reduce_rem_Z result < denominator_Z rec.
Admitted.

Theorem reduce_correct_with_quotient : forall rec x,
  reciprocal_invariant rec ->
  input_within_bound rec x ->
  let result := Bar.reduce true rec x in
  online_numerator_Z rec x =
    reduce_quot_Z result * denominator_Z rec + reduce_rem_Z result /\
  0 <= reduce_rem_Z result < denominator_Z rec.
Admitted.

Theorem udivrem_correct : forall params d u,
  params_admissible params ->
  Bar.input_bits params = 256%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  let result := Bar.udivrem u rec in
  to_Z_uint256 u =
    to_Z_words (Div.ud_quot result) * denominator_Z rec +
    to_Z_words (Div.ud_rem result) /\
  0 <= to_Z_words (Div.ud_rem result) < denominator_Z rec.
Admitted.

Theorem signed_wrapper_correct : forall params d x denominator_neg,
  params_admissible params ->
  Bar.input_bits params = 256%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  let divisor := signed_divisor_Z denominator_neg rec in
  let result := Bar.sdivrem x denominator_neg rec in
  to_Z_signed_words (Div.ud_quot result) = Z.quot (to_Z_signed_uint256 x) divisor /\
  to_Z_signed_words (Div.ud_rem result) = Z.rem (to_Z_signed_uint256 x) divisor /\
  to_Z_signed_uint256 x =
    to_Z_signed_words (Div.ud_quot result) * divisor +
    to_Z_signed_words (Div.ud_rem result).
Admitted.

Theorem addmod_correct : forall params d x y,
  params_admissible params ->
  (257 <= Bar.input_bits params)%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  to_Z_uint256 (Bar.addmod x y rec) =
    Z.modulo (to_Z_uint256 x + to_Z_uint256 y) (denominator_Z rec).
Admitted.

Theorem mulmod_correct : forall params d x y,
  params_admissible params ->
  (512 <= Bar.input_bits params)%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  to_Z_uint256 (Bar.mulmod x y rec) =
    Z.modulo (to_Z_uint256 x * to_Z_uint256 y) (denominator_Z rec).
Admitted.

Theorem mulmod_const_correct : forall params y d x,
  params_admissible params ->
  (256 <= Bar.input_bits params)%nat ->
  (256 <= Bar.multiplier_bits params)%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_multiplier params y d in
  to_Z_uint256 (Bar.mulmod_const x rec) =
    Z.modulo (to_Z_uint256 x * to_Z_uint256 y) (denominator_Z rec).
Admitted.

End MakeProofs.

Module Type BarrettProofsSig (B : Base.BaseProofSig) (U128 : Uint128)
  (Bridge : UintWiden B.U64 U128)
  (WL : WordsLemmas.WordsLemmasProofSig with Module U64 := B.U64)
  (Div : Division.DivisionProofSig(B)(U128)(Bridge))
  (DP : DivisionProofs.DivisionProofsSig(B)(U128)(Bridge)(Div)(WL))
  (RM : RuntimeMul.RuntimeMulProofSig with Module U64 := B.U64)
  (RMP : RuntimeMulProofs.RuntimeMulProofsSig(B)(RM)(WL))
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM))
  (Bar : Barrett.BarrettSig(B)(U128)(Bridge)(Div)(RM)(Arith)).
Include MakeProofs(B)(U128)(Bridge)(WL)(Div)(DP)(RM)(RMP)(Arith)(Bar).
End BarrettProofsSig.
