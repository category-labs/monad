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

Lemma modulus256_pos : 0 < modulus256.
Proof.
  change modulus256 with AP.modulus256.
  exact AP.modulus256_pos.
Qed.

Lemma modulus256_twice_sign_threshold :
  modulus256 = 2 * sign_threshold256.
Proof.
  unfold sign_threshold256, modulus256, modulus_words, WL.modulus_words, base.
  rewrite width_is_64.
  vm_compute.
  reflexivity.
Qed.

Lemma to_Z_uint256_bounds : forall x,
  0 <= to_Z_uint256 x < modulus256.
Proof.
  intro x.
  unfold to_Z_uint256, modulus256.
  apply WL.to_Z_words_bound.
Qed.

Lemma to_Z_signed_uint256_bounds : forall x,
  - sign_threshold256 <= to_Z_signed_uint256 x < sign_threshold256.
Proof.
  intro x.
  unfold to_Z_signed_uint256.
  pose proof (to_Z_uint256_bounds x) as Hx.
  pose proof modulus256_twice_sign_threshold as Hmod.
  pose proof modulus256_pos as Hpos.
  destruct (Z.ltb_spec0 (to_Z_uint256 x) sign_threshold256); lia.
Qed.

Lemma to_Z_signed_uint256_nonnegative : forall x,
  Arith.is_negative x = false ->
  to_Z_signed_uint256 x = to_Z_uint256 x.
Proof.
  intros x Hneg.
  change (to_Z_signed_uint256 x) with (AP.to_Z_signed_uint256 x).
  change (to_Z_uint256 x) with (AP.to_Z_uint256 x).
  apply AP.to_Z_signed_uint256_nonnegative.
  change (AP.is_negative x) with (Arith.is_negative x).
  exact Hneg.
Qed.

Lemma to_Z_signed_uint256_negative : forall x,
  Arith.is_negative x = true ->
  to_Z_signed_uint256 x = - to_Z_uint256 (Arith.negate_uint256 x).
Proof.
  intros x Hneg.
  change (to_Z_signed_uint256 x) with (AP.to_Z_signed_uint256 x).
  change (to_Z_uint256 (Arith.negate_uint256 x))
    with (AP.to_Z_uint256 (AP.negate_uint256 x)).
  apply AP.to_Z_signed_uint256_negative.
  change (AP.is_negative x) with (Arith.is_negative x).
  exact Hneg.
Qed.

Lemma to_Z_signed_words_nonnegative : forall ws,
  0 <= to_Z_words ws < sign_threshold256 ->
  to_Z_signed_words ws = to_Z_words ws.
Proof.
  intros ws Hws.
  change (to_Z_signed_words ws) with (AP.to_Z_signed_words ws).
  rewrite AP.to_Z_signed_words_wrap.
  - unfold AP.wrap_signed256.
    change AP.modulus256 with modulus256.
    change AP.sign_threshold256 with sign_threshold256.
    rewrite Z.mod_small.
    + destruct (Z.ltb_spec0 (to_Z_words ws) sign_threshold256); lia.
    + pose proof modulus256_twice_sign_threshold.
      pose proof modulus256_pos. lia.
  - change AP.modulus256 with modulus256.
    pose proof modulus256_twice_sign_threshold.
    pose proof modulus256_pos. lia.
Qed.

Lemma to_Z_signed_negate_words_nonpositive : forall ws,
  0 <= to_Z_words ws <= sign_threshold256 ->
  to_Z_signed_words (Arith.negate_words ws) = - to_Z_words ws.
Proof.
  intros ws Hws.
  change (to_Z_signed_words (Arith.negate_words ws))
    with (AP.to_Z_signed_words (AP.negate_words ws)).
  rewrite AP.to_Z_signed_negate_words_wrap.
  - unfold AP.wrap_signed256.
    change AP.modulus256 with modulus256.
    change AP.sign_threshold256 with sign_threshold256.
    pose proof modulus256_twice_sign_threshold as Hmod.
    pose proof modulus256_pos as Hpos.
    destruct (Z.eq_dec (to_Z_words ws) 0) as [Hz|Hz].
    + rewrite Hz, Z.opp_0.
      replace (0 mod modulus256) with 0 by
        (symmetry; apply Z.mod_small; lia).
      destruct (Z.ltb_spec0 0 sign_threshold256); lia.
    + assert (Hneg : (- to_Z_words ws <? 0) = true).
      { apply Z.ltb_lt. lia. }
      pose proof (AP.mod_borrow_decompose modulus256 (- to_Z_words ws)
        ltac:(lia) ltac:(lia)) as Hborrow.
      change AP.modulus256 with modulus256 in Hborrow.
      rewrite Hneg in Hborrow.
      assert (Hmod_eq :
        (- to_Z_words ws) mod modulus256 = modulus256 - to_Z_words ws)
        by lia.
      rewrite Hmod_eq.
      destruct (Z.ltb_spec0
        (modulus256 - to_Z_words ws) sign_threshold256); lia.
  - change AP.modulus256 with modulus256.
    pose proof modulus256_twice_sign_threshold.
    pose proof modulus256_pos. lia.
Qed.

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

Definition reciprocal_admissible (rec : Bar.reciprocal) : Prop :=
  let params := Bar.reciprocal_params rec in
  params_admissible params /\
  length (Bar.reciprocal_ rec) = Bar.reciprocal_words params /\
  length (Bar.denominator_ rec) = Bar.max_denominator_words params /\
  length (Bar.multiplier_ rec) = Bar.multiplier_words params /\
  reciprocal_scale_factor rec <=
    2 ^ Z.of_nat (Bar.multiplier_bits params) /\
  to_Z_uint256 (Bar.min_denominator params) <= denominator_Z rec /\
  denominator_Z rec <= to_Z_uint256 (Bar.max_denominator params) /\
  multiplier_Z rec < modulus_words (Bar.multiplier_words params).

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

Lemma fit_words_idempotent : forall n ws,
  Bar.fit_words n (Bar.fit_words n ws) = Bar.fit_words n ws.
Proof.
  intros n ws.
  unfold Bar.fit_words at 1.
  rewrite firstn_app.
  rewrite fit_words_length.
  replace (n - n)%nat with 0%nat by lia.
  cbn [firstn app].
  rewrite app_nil_r.
  rewrite firstn_all2 by (rewrite fit_words_length; lia).
  reflexivity.
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

Lemma modulus_words_add : forall m n,
  modulus_words (m + n) = modulus_words m * modulus_words n.
Proof.
  intros m n.
  unfold modulus_words.
  rewrite Nat2Z.inj_add.
  rewrite Z.pow_add_r by lia.
  reflexivity.
Qed.

Lemma truncating_mul_full_exact : forall xs ys,
  (0 < length xs)%nat ->
  (0 < length ys)%nat ->
  to_Z_words (Bar.truncating_mul (length xs + length ys) xs ys) =
  to_Z_words xs * to_Z_words ys.
Proof.
  intros xs ys Hxs Hys.
  unfold Bar.truncating_mul.
  pose proof (RMP.truncating_mul_runtime_correct xs ys
    (length xs + length ys) Hxs Hys ltac:(lia) ltac:(lia)) as Hcorr.
  pose proof (RMP.truncating_mul_runtime_length xs ys
    (length xs + length ys) ltac:(lia)) as Hlen.
  pose proof (WL.to_Z_words_bound (RMP.truncating_mul_runtime xs ys
    (length xs + length ys))) as Hres_bound.
  rewrite Hlen in Hres_bound.
  pose proof (WL.to_Z_words_bound xs) as Hxs_bound.
  pose proof (WL.to_Z_words_bound ys) as Hys_bound.
  assert (Hprod_bound :
    0 <= to_Z_words xs * to_Z_words ys <
    modulus_words (length xs + length ys)).
  { rewrite modulus_words_add.
    pose proof (WL.modulus_words_pos (length xs)).
    pose proof (WL.modulus_words_pos (length ys)).
    nia. }
  rewrite Z.mod_small in Hcorr by exact Hres_bound.
  rewrite Z.mod_small in Hcorr by exact Hprod_bound.
  exact Hcorr.
Qed.

Lemma truncating_mul_runtime_correct_general : forall xs ys R,
  (0 < length xs)%nat ->
  (0 < length ys)%nat ->
  (0 < R)%nat ->
  to_Z_words (RMP.truncating_mul_runtime xs ys R) mod modulus_words R =
    (to_Z_words xs * to_Z_words ys) mod modulus_words R.
Proof.
  intros xs ys R Hxs Hys HR.
  destruct ys as [|y ys_tail].
  - simpl in Hys. lia.
  - cbn [RMP.truncating_mul_runtime].
    pose proof (RMP.mul_line_correct R xs y Hxs HR) as Hline.
    pose proof
      (RMP.truncating_mul_runtime_recur_correct
         xs ys_tail (RMP.mul_line R xs y) 1 R Hxs
         (RMP.mul_line_length R xs y)
         (fun j Hj HjR =>
            RMP.mul_line_zero_tail R xs y Hxs HR j Hj HjR))
      as Htail.
    rewrite Htail, Zplus_mod, Hline.
    rewrite <- Zplus_mod.
    cbn [to_Z_words].
    rewrite Z.mul_add_distr_l, Z.mul_assoc, RMP.pow64_modulus_words.
    f_equal.
    change (to_Z y) with (WL.U64.to_Z y).
    unfold modulus_words, base.
    rewrite Bar.U64.width_is_64.
    change (Z.pos 64) with 64.
    change (Z.of_nat 1) with 1.
    rewrite Z.pow_1_r.
    ring.
Qed.

Lemma truncating_mul_exact_small_general : forall xs ys R,
  (0 < length xs)%nat ->
  (0 < R)%nat ->
  to_Z_words xs * to_Z_words ys < modulus_words R ->
  to_Z_words (Bar.truncating_mul R xs ys) = to_Z_words xs * to_Z_words ys.
Proof.
  intros xs ys R Hxs HR Hprod_lt.
  destruct ys as [|y ys_tail].
  - unfold Bar.truncating_mul.
    cbn [RM.truncating_mul_runtime to_Z_words].
    rewrite WL.to_Z_extend_words.
    cbn [to_Z_words]. ring.
  - unfold Bar.truncating_mul.
    pose proof (truncating_mul_runtime_correct_general
      xs (y :: ys_tail) R Hxs ltac:(cbn; lia) HR) as Hcorr.
    pose proof (RMP.truncating_mul_runtime_length
      xs (y :: ys_tail) R HR) as Hlen.
    pose proof (WL.to_Z_words_bound
      (RMP.truncating_mul_runtime xs (y :: ys_tail) R)) as Hres_bound.
    rewrite Hlen in Hres_bound.
    pose proof (WL.to_Z_words_bound xs) as Hxs_bound.
    pose proof (WL.to_Z_words_bound (y :: ys_tail)) as Hys_bound.
    assert (Hprod_bound :
      0 <= to_Z_words xs * to_Z_words (y :: ys_tail) < modulus_words R).
    { split; try exact Hprod_lt. nia. }
    rewrite Z.mod_small in Hcorr by exact Hres_bound.
    rewrite Z.mod_small in Hcorr by exact Hprod_bound.
    exact Hcorr.
Qed.

Lemma truncating_mul_runtime_recur_left_nil : forall ys result I R,
  RM.truncating_mul_runtime_recur [] ys result I R = result.
Proof.
  induction ys as [|y ys IH]; intros result I R.
  - reflexivity.
  - cbn [RM.truncating_mul_runtime_recur RM.mul_add_line].
    apply IH.
Qed.

Lemma truncating_mul_left_nil_value : forall ys R,
  to_Z_words (Bar.truncating_mul R [] ys) = 0.
Proof.
  intros ys R.
  unfold Bar.truncating_mul, RM.truncating_mul_runtime.
  destruct ys as [|y ys].
  - apply WL.to_Z_extend_words.
  - rewrite truncating_mul_runtime_recur_left_nil.
    apply WL.to_Z_extend_words.
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

Lemma countl_zero_lower : forall x,
  0 < to_Z x ->
  2 ^ Z.of_nat (Bar.word_width - S (Div.countl_zero x)) <= to_Z x.
Proof.
  intros x Hx.
  assert (Hpivot_gen : forall pos y,
    to_Z y > 0 ->
    (pos > 0)%nat ->
    to_Z (shr y (pos - S (Div.countl_zero_go y pos))) <> 0).
  { intros pos. induction pos as [|pos' IH]; intros y Hy Hpos; [lia|].
    cbn [Div.countl_zero_go].
    destruct (eqb (shr y pos') zero) eqn:Heq.
    - destruct pos' as [|pos''].
      + exfalso.
        rewrite spec_eqb in Heq. apply Z.eqb_eq in Heq.
        rewrite spec_zero in Heq.
        rewrite spec_shr in Heq. rewrite Z.shiftr_0_r in Heq.
        rewrite Z.mod_small in Heq by
          (pose proof (spec_to_Z y); unfold base in *; lia).
        lia.
      + replace
          (S (S pos'') - S (S (Div.countl_zero_go y (S pos''))))%nat
          with (S pos'' - S (Div.countl_zero_go y (S pos'')))%nat by lia.
        apply IH; lia.
    - rewrite spec_eqb in Heq. apply Z.eqb_neq in Heq.
      rewrite spec_zero in Heq.
      replace (S pos' - S 0)%nat with pos' by lia.
      exact Heq. }
  assert (Hpivot :
    to_Z (shr x (Pos.to_nat width - S (Div.countl_zero x))) <> 0).
  { unfold Div.countl_zero.
    apply (Hpivot_gen (Pos.to_nat width) x); [lia|].
    pose proof (Pos2Nat.is_pos width). lia. }
  destruct (DP.shr_zero_iff x (Pos.to_nat width - S (Div.countl_zero x))
    ltac:(pose proof (DP.countl_zero_bound x ltac:(lia)); lia))
    as [_ Hshr0].
  assert (~ to_Z x < 2 ^ Z.of_nat (Pos.to_nat width - S (Div.countl_zero x))).
  { exact (fun Hlt => Hpivot (Hshr0 Hlt)). }
  unfold Bar.word_width.
  lia.
Qed.

Lemma bit_width_words_lower_bound : forall ws,
  0 < to_Z_words ws ->
  2 ^ Z.of_nat (Bar.bit_width_words ws - 1) <= to_Z_words ws.
Proof.
  intros ws Hpos.
  unfold Bar.bit_width_words.
  destruct (Div.count_significant_words ws) as [|n] eqn:Hn.
  - pose proof (DP.count_significant_words_zero ws Hn). lia.
  - pose proof (DP.count_significant_words_bound ws) as Hcsw_len.
    rewrite Hn in Hcsw_len.
    pose proof (DP.count_significant_words_msw_nonzero ws) as Hmsw_pos.
    cbn zeta in Hmsw_pos.
    rewrite Hn in Hmsw_pos.
    specialize (Hmsw_pos ltac:(lia)).
    replace (S n - 1)%nat with n in Hmsw_pos by lia.
    change (WL.get_word ws n) with (Bar.get_word ws n) in Hmsw_pos.
    pose proof (countl_zero_lower (Bar.get_word ws n) ltac:(lia))
      as Hword_low.
    unfold Bar.word_width in Hword_low.
    rewrite Bar.U64.width_is_64 in Hword_low.
    change (Pos.to_nat 64) with 64%nat in Hword_low.
    unfold Bar.bit_width_word, Bar.word_width.
    rewrite Bar.U64.width_is_64.
    change (Pos.to_nat 64) with 64%nat.
    set (c := Div.countl_zero (Bar.get_word ws n)) in *.
    assert (Hc_lt : (c < 64)%nat).
    { subst c. pose proof
        (DP.countl_zero_bound (Bar.get_word ws n) ltac:(lia)).
      rewrite Bar.U64.width_is_64 in H. exact H. }
    pose proof (WL.to_Z_words_firstn_skipn ws n ltac:(lia)) as Hsplit.
    set (low := to_Z_words (firstn n ws)) in *.
    set (high := to_Z_words (skipn n ws)) in *.
    assert (Hlow_nonneg : 0 <= low).
    { subst low. pose proof (WL.to_Z_words_bound (firstn n ws)); lia. }
    assert (Hmod_pos : 0 < modulus_words n).
    { pose proof (WL.modulus_words_pos n). lia. }
    assert (Hhigh_ge : to_Z (Bar.get_word ws n) <= high).
    { subst high.
      destruct (skipn n ws) as [|w rest] eqn:Hsk.
      - assert (length (skipn n ws) = 0%nat) by
          (rewrite Hsk; reflexivity).
        rewrite length_skipn in H. lia.
      - assert (Hnth : Bar.get_word ws n = w).
        { unfold Bar.get_word.
          replace n with (n + 0)%nat by lia.
          rewrite <- (nth_skipn n ws 0 Bar.U64.zero).
          rewrite Hsk. reflexivity. }
        rewrite Hnth. cbn [to_Z_words].
        pose proof (WL.to_Z_words_bound rest) as Hrest.
        assert (0 <= base WL.U64.width) by
          (unfold base; apply Z.pow_nonneg; lia).
        change (to_Z w) with (WL.U64.to_Z w).
        nia. }
    assert (Hvalue_ge : modulus_words n * to_Z (Bar.get_word ws n) <=
                        to_Z_words ws).
    { rewrite Hsplit.
      change (to_Z_words (firstn n ws)) with low.
      change (to_Z_words (skipn n ws)) with high.
      nia. }
    assert (Hpow_eq :
      2 ^ Z.of_nat (64 * n + (64 - c) - 1) =
      modulus_words n * 2 ^ Z.of_nat (64 - S c)).
    { unfold modulus_words, base.
      rewrite Bar.U64.width_is_64.
      change (Z.pos 64) with 64.
      rewrite <- Z.pow_mul_r by lia.
      rewrite <- Z.pow_add_r by lia.
      f_equal. lia. }
    rewrite Hpow_eq.
    nia.
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

Lemma min_denominator_bits_positive : forall params,
  params_admissible params ->
  (0 < Bar.min_denominator_bits params)%nat.
Proof.
  intros params Hadm.
  destruct Hadm as [Hmin_pos _].
  unfold Bar.min_denominator_bits, Bar.bit_width_uint256, Bar.bit_width_words.
  destruct (Div.count_significant_words
    (Bar.uint256_to_words (Bar.min_denominator params))) eqn:Hn; try lia.
  - pose proof (DP.count_significant_words_zero
      (Bar.uint256_to_words (Bar.min_denominator params)) Hn) as Hz.
    unfold to_Z_uint256 in Hmin_pos. lia.
  - pose proof (DP.count_significant_words_msw_nonzero
      (Bar.uint256_to_words (Bar.min_denominator params))) as Hmsw.
    cbn zeta in Hmsw.
    rewrite Hn in Hmsw.
    specialize (Hmsw ltac:(lia)).
    replace (S n - 1)%nat with n in Hmsw by lia.
    change (WL.get_word
      (Bar.uint256_to_words (Bar.min_denominator params)) n)
      with
      (Bar.get_word (Bar.uint256_to_words (Bar.min_denominator params)) n)
      in Hmsw.
    unfold Bar.bit_width_word, Bar.word_width.
    pose proof (DP.countl_zero_bound
      (Bar.get_word (Bar.uint256_to_words (Bar.min_denominator params)) n)
      Hmsw) as Hcz.
    lia.
Qed.

Lemma min_denominator_value_lower_bound : forall params,
  params_admissible params ->
  2 ^ Z.of_nat (Bar.min_denominator_bits params - 1) <=
    to_Z_uint256 (Bar.min_denominator params).
Proof.
  intros params Hadm.
  destruct Hadm as [Hmin_pos _].
  unfold Bar.min_denominator_bits, Bar.bit_width_uint256, to_Z_uint256.
  apply bit_width_words_lower_bound.
  exact Hmin_pos.
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

Lemma multiplier_words_positive : forall params,
  (0 < Bar.multiplier_bits params)%nat ->
  (0 < Bar.multiplier_words params)%nat.
Proof.
  intros params Hbits.
  unfold Bar.multiplier_words, Bar.min_words, Bar.word_width.
  apply Nat.div_str_pos.
  pose proof (Pos2Nat.is_pos Bar.U64.width).
  lia.
Qed.

Lemma min_words_positive : forall bits,
  (0 < bits)%nat -> (0 < Bar.min_words bits)%nat.
Proof.
  intros bits Hbits.
  unfold Bar.min_words.
  apply Nat.div_str_pos.
  pose proof (Pos2Nat.is_pos Bar.U64.width).
  unfold Bar.word_width.
  lia.
Qed.

Lemma min_words_zero : Bar.min_words 0 = 0%nat.
Proof.
  unfold Bar.min_words, Bar.word_width.
  rewrite Nat.add_0_l.
  apply Nat.div_small.
  pose proof (Pos2Nat.is_pos Bar.U64.width). lia.
Qed.

Lemma min_words_monotone : forall a b,
  (a <= b)%nat -> (Bar.min_words a <= Bar.min_words b)%nat.
Proof.
  intros a b Hab.
  unfold Bar.min_words.
  apply Nat.Div0.div_le_mono.
  lia.
Qed.

Lemma min_words_add_le : forall a b,
  (Bar.min_words (a + b) <= Bar.min_words a + Bar.min_words b)%nat.
Proof.
  intros a b.
  unfold Bar.min_words.
  set (w := Bar.word_width).
  assert (Hw : w <> 0%nat).
  { unfold w, Bar.word_width.
    pose proof (Pos2Nat.is_pos Bar.U64.width).
    lia. }
  assert (Hlt :
    ((a + b + Nat.pred w) / w <
     (a + Nat.pred w) / w + (b + Nat.pred w) / w + 1)%nat).
  { apply Nat.Div0.div_lt_upper_bound.
    pose proof (Nat.div_mod (a + Nat.pred w) w Hw) as Ha.
    pose proof (Nat.div_mod (b + Nat.pred w) w Hw) as Hb.
    pose proof (Nat.mod_upper_bound (a + Nat.pred w) w Hw) as Hamod.
    pose proof (Nat.mod_upper_bound (b + Nat.pred w) w Hw) as Hbmod.
    assert (Hwpos : (0 < w)%nat) by lia.
    replace (Nat.pred w) with (w - 1)%nat in * by lia.
    nia. }
  lia.
Qed.

Lemma pow_le_modulus_min_words : forall bits,
  2 ^ Z.of_nat bits <= modulus_words (Bar.min_words bits).
Proof.
  intro bits.
  unfold Bar.min_words, modulus_words, Bar.word_width, base.
  rewrite Bar.U64.width_is_64.
  change (Pos.to_nat 64) with 64%nat.
  change (Z.pos 64) with 64.
  rewrite <- Z.pow_mul_r by lia.
  apply Z.pow_le_mono_r; try lia.
  pose proof (Nat.div_mod (bits + Nat.pred 64) 64 ltac:(lia)) as Hdm.
  change (Nat.pred 64) with 63%nat.
  change (Nat.pred 64) with 63%nat in Hdm.
  pose proof (Nat.mod_upper_bound (bits + 63) 64 ltac:(lia)) as Hmod.
  lia.
Qed.

Lemma pow_max_quotient_scale_bound : forall I M D,
  (0 < D)%nat ->
  2 ^ Z.of_nat M * 2 ^ Z.of_nat I <=
  2 ^ Z.of_nat (D - 1) * 2 ^ Z.of_nat (I + M - D + 1).
Proof.
  intros I M D HD.
  rewrite <- !Z.pow_add_r by lia.
  apply Z.pow_le_mono_r; lia.
Qed.

Lemma max_r_hat_words_le_product_words : forall params,
  (Bar.max_r_hat_words params <=
   Bar.input_words params + Bar.multiplier_words params)%nat.
Proof.
  intro params.
  unfold Bar.max_r_hat_words, Bar.max_r_hat_bits.
  eapply Nat.le_trans.
  - apply min_words_monotone. apply Nat.le_min_l.
  - unfold Bar.input_words, Bar.multiplier_words.
    apply min_words_add_le.
Qed.

Lemma max_r_hat_words_positive : forall params,
  params_admissible params ->
  (0 < Bar.multiplier_bits params)%nat ->
  (0 < Bar.max_r_hat_words params)%nat.
Proof.
  intros params Hadm Hbits.
  apply min_words_positive.
  unfold Bar.max_r_hat_bits.
  destruct Hadm as [_ [_ Hinput]].
  destruct (Nat.min_spec
    (Bar.input_bits params + Bar.multiplier_bits params)
    (Bar.max_denominator_bits params + 2)) as [[_ ->]|[_ ->]]; lia.
Qed.

Lemma input_bits_aligned : forall params,
  Bar.bit_shift params = 0%nat ->
  Bar.input_bits params =
    (Bar.word_width * Bar.word_shift params)%nat.
Proof.
  intros params Hbit.
  unfold Bar.bit_shift, Bar.word_shift, Bar.word_width, Bar.shift in *.
  pose proof (Nat.div_mod (Bar.input_bits params)
    (Pos.to_nat Bar.U64.width) ltac:(pose proof
      (Pos2Nat.is_pos Bar.U64.width); lia)) as Hdiv.
  rewrite Hbit in Hdiv.
  lia.
Qed.

Lemma numerator_words_with_multiplier_aligned : forall params,
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  Bar.numerator_words params =
    (Bar.word_shift params + Bar.multiplier_words params)%nat.
Proof.
  intros params Hbits Hbit.
  pose proof (multiplier_words_positive params Hbits) as Hmwords_pos.
  unfold Bar.numerator_words.
  replace (Nat.eqb (Bar.multiplier_words params) 0%nat) with false.
  2: { symmetry. apply Nat.eqb_neq. lia. }
  unfold Bar.min_words, Bar.word_width.
  pose proof (input_bits_aligned params Hbit) as Haligned.
  rewrite Haligned.
  rewrite Bar.U64.width_is_64.
  change (Pos.to_nat 64) with 64%nat.
  change Bar.word_width with (Pos.to_nat Bar.U64.width).
  rewrite Bar.U64.width_is_64.
  change (Pos.to_nat 64) with 64%nat.
  symmetry.
  apply Nat.div_unique with (r := 63%nat); lia.
Qed.

Lemma set_segment_start0_same_length : forall ws seg,
  length ws = length seg ->
  Div.set_segment ws 0 seg = seg.
Proof.
  induction ws as [|w ws IH]; intros [|s seg] Hlen;
    cbn [Div.set_segment length app skipn] in *; try lia.
  - reflexivity.
  - rewrite skipn_all2 by lia.
    rewrite app_nil_r. reflexivity.
Qed.

Lemma set_segment_extend_exact : forall start seg,
  Div.set_segment (Bar.extend_words (start + length seg)) start seg =
    repeat zero start ++ seg.
Proof.
  induction start as [|start IH]; intro seg.
  - apply set_segment_start0_same_length.
    rewrite WL.extend_words_length. reflexivity.
  - replace (S start + length seg)%nat with
      (S (start + length seg)) by lia.
    change (Bar.extend_words (S (start + length seg))) with
      (zero :: Bar.extend_words (start + length seg)).
    cbn [Div.set_segment repeat app].
    rewrite IH. reflexivity.
Qed.

Lemma bounded_segment_exact_value : forall start seg,
  to_Z_words (Bar.bounded_segment (start + length seg) start seg) =
    modulus_words start * to_Z_words seg.
Proof.
  intros start seg.
  unfold Bar.bounded_segment.
  replace (start + length seg - start)%nat with (length seg) by lia.
  rewrite firstn_all.
  rewrite set_segment_extend_exact.
  rewrite WL.to_Z_words_app, WL.to_Z_words_repeat_zero.
  rewrite repeat_length. ring.
Qed.

Lemma modulus_words_word_shift_aligned : forall params,
  Bar.bit_shift params = 0%nat ->
  modulus_words (Bar.word_shift params) =
    2 ^ Z.of_nat (Bar.input_bits params).
Proof.
  intros params Hbit.
  unfold modulus_words.
  replace (base width) with (2 ^ 64).
  2: { unfold base. rewrite Bar.U64.width_is_64. reflexivity. }
  rewrite <- Z.pow_mul_r by lia.
  pose proof (input_bits_aligned params Hbit) as Haligned.
  unfold Bar.word_width in Haligned.
  rewrite Bar.U64.width_is_64 in Haligned.
  change (Pos.to_nat 64) with 64%nat in Haligned.
  rewrite Haligned.
  rewrite Nat2Z.inj_mul.
  change (Z.of_nat 64) with 64.
  reflexivity.
Qed.

Lemma numerator_with_multiplier_value_aligned : forall params y,
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  uint256_fits_words (Bar.multiplier_words params) y ->
  to_Z_words
    (Bar.numerator_with_multiplier params (Bar.uint256_to_words y)) =
    to_Z_uint256 y * 2 ^ Z.of_nat (Bar.input_bits params).
Proof.
  intros params y Hbits Hbit Hy_fit.
  unfold Bar.numerator_with_multiplier.
  rewrite Hbit. cbn [Nat.eqb].
  rewrite (numerator_words_with_multiplier_aligned params Hbits Hbit).
  replace (Bar.word_shift params + Bar.multiplier_words params)%nat with
    (Bar.word_shift params +
     length (Bar.fit_words (Bar.multiplier_words params)
       (Bar.uint256_to_words y)))%nat.
  2: { rewrite fit_words_length. reflexivity. }
  rewrite bounded_segment_exact_value.
  rewrite to_Z_fit_uint256_words_small by exact Hy_fit.
  rewrite modulus_words_word_shift_aligned by exact Hbit.
  ring.
Qed.

Lemma numerator_with_multiplier_words_value_aligned : forall params y_words,
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  to_Z_words (Bar.numerator_with_multiplier params y_words) =
    to_Z_words (Bar.fit_words (Bar.multiplier_words params) y_words) *
    2 ^ Z.of_nat (Bar.input_bits params).
Proof.
  intros params y_words Hbits Hbit.
  unfold Bar.numerator_with_multiplier.
  rewrite Hbit. cbn [Nat.eqb].
  rewrite (numerator_words_with_multiplier_aligned params Hbits Hbit).
  replace (Bar.word_shift params + Bar.multiplier_words params)%nat with
    (Bar.word_shift params +
     length (Bar.fit_words (Bar.multiplier_words params) y_words))%nat.
  2: { rewrite fit_words_length. reflexivity. }
  rewrite bounded_segment_exact_value.
  rewrite modulus_words_word_shift_aligned by exact Hbit.
  ring.
Qed.

Lemma to_Z_word_all_ones :
  to_Z (Bar.U64.sub Bar.U64.zero Bar.U64.one) = base width - 1.
Proof.
  change (Bar.U64.sub Bar.U64.zero Bar.U64.one) with (sub zero one).
  rewrite spec_sub, spec_zero, spec_one.
  replace (0 - 1) with (-1) by lia.
  symmetry.
  apply Z.mod_unique_pos with (q := -1).
  - unfold base. rewrite Bar.U64.width_is_64. simpl. lia.
  - ring.
Qed.

Lemma to_Z_all_ones_words : forall n,
  to_Z_words (Bar.all_ones_words n) = modulus_words n - 1.
Proof.
  induction n as [|n IH].
  - unfold Bar.all_ones_words, modulus_words. cbn [repeat to_Z_words].
    lia.
  - unfold Bar.all_ones_words in *.
    cbn [repeat to_Z_words].
    rewrite to_Z_word_all_ones, IH.
    rewrite WL.modulus_words_succ.
    ring.
Qed.

Lemma numerator_with_multiplier_length_aligned : forall params y_words,
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  length (Bar.numerator_with_multiplier params y_words) =
    Bar.numerator_words params.
Proof.
  intros params y_words Hbits Hbit.
  unfold Bar.numerator_with_multiplier.
  rewrite Hbit. cbn [Nat.eqb].
  rewrite (numerator_words_with_multiplier_aligned params Hbits Hbit).
  unfold Bar.bounded_segment.
  rewrite DP.set_segment_length.
  - rewrite WL.extend_words_length. reflexivity.
  - rewrite WL.extend_words_length, length_firstn.
    lia.
Qed.

Lemma udivrem_quotient_with_multiplier_exact : forall params y d r,
  params_admissible params ->
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  uint256_fits_words (Bar.multiplier_words params) y ->
  Bar.valid_denominator params d = true ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
    (Bar.uint256_to_words d) = Some r ->
  to_Z_words (Div.ud_quot r) =
    Z.div (to_Z_uint256 y * 2 ^ Z.of_nat (Bar.input_bits params))
      (to_Z_uint256 d).
Proof.
  intros params y d r Hadm Hbits Hbit Hy_fit Hvalid Hdiv.
  pose proof (valid_denominator_positive params d Hadm Hvalid) as Hd_pos.
  pose proof (DP.udivrem_correct
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
    (Bar.uint256_to_words d) r) as Hcorr.
  specialize (Hcorr (numerator_with_multiplier_length_aligned params
    (Bar.uint256_to_words y) Hbits Hbit)).
  assert (Hd_len : length (Bar.uint256_to_words d) = Bar.uint256_num_words).
  { rewrite uint256_to_words_length. unfold Bar.uint256_num_words.
    reflexivity. }
  specialize (Hcorr Hd_len).
  unfold to_Z_uint256 in Hd_pos.
  specialize (Hcorr ltac:(lia) Hdiv).
  destruct Hcorr as [Hvalue Hrem].
  rewrite numerator_with_multiplier_value_aligned in Hvalue
    by assumption.
  unfold to_Z_uint256 in Hvalue.
  unfold to_Z_uint256.
  change (to_Z_words (Div.ud_quot r)) with (to_Z_words (DP.ud_quot r)).
  apply Z.div_unique with (r := to_Z_words (Div.ud_rem r)).
  - left. exact Hrem.
  - rewrite Hvalue. ring.
Qed.

Lemma udivrem_quotient_with_multiplier_words_exact :
  forall params y_words d r,
  params_admissible params ->
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  Bar.valid_denominator params d = true ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params y_words)
    (Bar.uint256_to_words d) = Some r ->
  to_Z_words (Div.ud_quot r) =
    Z.div
      (to_Z_words (Bar.fit_words (Bar.multiplier_words params) y_words) *
       2 ^ Z.of_nat (Bar.input_bits params))
      (to_Z_uint256 d).
Proof.
  intros params y_words d r Hadm Hbits Hbit Hvalid Hdiv.
  pose proof (valid_denominator_positive params d Hadm Hvalid) as Hd_pos.
  pose proof (DP.udivrem_correct
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params y_words)
    (Bar.uint256_to_words d) r) as Hcorr.
  specialize (Hcorr (numerator_with_multiplier_length_aligned params
    y_words Hbits Hbit)).
  assert (Hd_len : length (Bar.uint256_to_words d) = Bar.uint256_num_words).
  { rewrite uint256_to_words_length. unfold Bar.uint256_num_words.
    reflexivity. }
  specialize (Hcorr Hd_len).
  unfold to_Z_uint256 in Hd_pos.
  specialize (Hcorr ltac:(lia) Hdiv).
  destruct Hcorr as [Hvalue Hrem].
  rewrite numerator_with_multiplier_words_value_aligned in Hvalue
    by assumption.
  unfold to_Z_uint256.
  change (to_Z_words (Div.ud_quot r)) with (to_Z_words (DP.ud_quot r)).
  apply Z.div_unique with (r := to_Z_words (Div.ud_rem r)).
  - left. exact Hrem.
  - rewrite Hvalue. ring.
Qed.

Lemma reciprocal_words_with_multiplier : forall params rmax,
  (0 < Bar.multiplier_bits params)%nat ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params
       (Bar.all_ones_words (Bar.multiplier_words params)))
    (Bar.uint256_to_words (Bar.min_denominator params)) = Some rmax ->
  Bar.reciprocal_words params =
    Div.count_significant_words (Div.ud_quot rmax).
Proof.
  intros params rmax Hbits Hdiv.
  unfold Bar.reciprocal_words, Bar.reciprocal_bits.
  pose proof (multiplier_words_positive params Hbits) as Hmwords_pos.
  replace (Nat.eqb (Bar.multiplier_words params) 0%nat) with false.
  2: { symmetry. apply Nat.eqb_neq. lia. }
  rewrite Hdiv.
  apply min_words_bit_width_words.
Qed.

Lemma to_Z_fit_all_ones_words : forall n,
  to_Z_words (Bar.fit_words n (Bar.all_ones_words n)) =
    modulus_words n - 1.
Proof.
  intro n.
  rewrite to_Z_fit_words_small.
  - apply to_Z_all_ones_words.
  - rewrite to_Z_all_ones_words.
    pose proof (WL.modulus_words_pos n).
    lia.
Qed.

Lemma uint256_fits_words_le_all_ones : forall n y,
  uint256_fits_words n y ->
  to_Z_uint256 y <= modulus_words n - 1.
Proof.
  intros n y Hfits.
  unfold uint256_fits_words in Hfits.
  pose proof (WL.to_Z_words_bound (Bar.uint256_to_words y)) as Hy_bound.
  unfold to_Z_uint256 in *.
  lia.
Qed.

Lemma reciprocal_quotient_with_multiplier_fits : forall params y d r rmax,
  params_admissible params ->
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  uint256_fits_words (Bar.multiplier_words params) y ->
  Bar.valid_denominator params d = true ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
    (Bar.uint256_to_words d) = Some r ->
  Div.udivrem (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params
       (Bar.all_ones_words (Bar.multiplier_words params)))
    (Bar.uint256_to_words (Bar.min_denominator params)) = Some rmax ->
  to_Z_words (Div.ud_quot r) < modulus_words (Bar.reciprocal_words params).
Proof.
  intros params y d r rmax Hadm Hbits Hbit Hy_fit Hvalid Hdiv Hdivmax.
  pose proof (valid_denominator_bounds params d Hvalid) as [Hmin_d _].
  destruct Hadm as [Hmin_pos Hadm_tail].
  assert (Hadm' : params_admissible params) by (repeat split; tauto || lia).
  pose proof
    (udivrem_quotient_with_multiplier_exact
       params y d r Hadm' Hbits Hbit Hy_fit Hvalid Hdiv) as Hq.
  pose proof
    (udivrem_quotient_with_multiplier_words_exact
       params (Bar.all_ones_words (Bar.multiplier_words params))
       (Bar.min_denominator params) rmax Hadm' Hbits Hbit
       (min_denominator_valid params Hadm') Hdivmax) as Hqmax.
  rewrite to_Z_fit_all_ones_words in Hqmax.
  assert (Hq_le : to_Z_words (Div.ud_quot r) <=
                  to_Z_words (Div.ud_quot rmax)).
  { rewrite Hq, Hqmax.
    set (P := 2 ^ Z.of_nat (Bar.input_bits params)).
    assert (HP_nonneg : 0 <= P) by (unfold P; apply Z.pow_nonneg; lia).
    assert (Hy_nonneg : 0 <= to_Z_uint256 y).
    { unfold to_Z_uint256. pose proof
        (WL.to_Z_words_bound (Bar.uint256_to_words y)); lia. }
    assert (Hy_le :
      to_Z_uint256 y <= modulus_words (Bar.multiplier_words params) - 1).
    { apply uint256_fits_words_le_all_ones. exact Hy_fit. }
	    transitivity ((to_Z_uint256 y * P) /
	      to_Z_uint256 (Bar.min_denominator params)).
	    - apply Z_div_denominator_anti_nonneg.
	      + apply Z.mul_nonneg_nonneg; lia.
	      + lia.
	      + lia.
    - apply Z.div_le_mono; try lia.
      nia. }
  rewrite (reciprocal_words_with_multiplier params rmax Hbits Hdivmax).
  pose proof (to_Z_words_count_significant_bound (Div.ud_quot rmax)).
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
  Bar.bit_shift params = 0%nat ->
  uint256_fits_words (Bar.multiplier_words params) y ->
  Bar.valid_denominator params d = true ->
  reciprocal_invariant (Bar.reciprocal_of_multiplier params y d) /\
  denominator_Z (Bar.reciprocal_of_multiplier params y d) = to_Z_uint256 d /\
  multiplier_Z (Bar.reciprocal_of_multiplier params y d) = to_Z_uint256 y.
Proof.
  intros params y d Hadm Hbits Hbit Hy_fit Hvalid.
  pose proof (valid_denominator_positive params d Hadm Hvalid) as Hd_pos.
  destruct (udivrem_positive_some
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
    (Bar.uint256_to_words d)) as [r Hdiv].
  { unfold to_Z_uint256 in Hd_pos. exact Hd_pos. }
  destruct (udivrem_positive_some
    (Bar.numerator_words params) Bar.uint256_num_words
    (Bar.numerator_with_multiplier params
       (Bar.all_ones_words (Bar.multiplier_words params)))
    (Bar.uint256_to_words (Bar.min_denominator params))) as [rmax Hdivmax].
  { unfold params_admissible, to_Z_uint256 in Hadm. lia. }
  unfold reciprocal_invariant, denominator_Z, reciprocal_Z, multiplier_Z.
  unfold Bar.reciprocal_of_multiplier.
  rewrite Hdiv.
  cbn [Bar.reciprocal_params Bar.denominator_ Bar.multiplier_
       Bar.reciprocal_].
  pose proof (valid_denominator_fits_words params d Hvalid) as Hd_fit.
  pose proof (to_Z_fit_uint256_words_small
    (Bar.max_denominator_words params) d Hd_fit) as Hden.
  pose proof (to_Z_fit_uint256_words_small
    (Bar.multiplier_words params) y Hy_fit) as Hmul.
  pose proof (reciprocal_quotient_with_multiplier_fits
    params y d r rmax Hadm Hbits Hbit Hy_fit Hvalid Hdiv Hdivmax)
    as Hq_fit.
  pose proof (to_Z_fit_words_small
    (Bar.reciprocal_words params) (Div.ud_quot r) Hq_fit) as Hq_fit_eq.
  pose proof (udivrem_quotient_with_multiplier_exact
    params y d r Hadm Hbits Hbit Hy_fit Hvalid Hdiv) as Hq.
  rewrite Hden, Hmul, Hq_fit_eq.
  unfold reciprocal_scale_factor.
  cbn [Bar.reciprocal_params Bar.multiplier_].
  replace (Nat.eqb (Bar.multiplier_words params) 0%nat) with false.
  2: { symmetry. apply Nat.eqb_neq.
       pose proof (multiplier_words_positive params Hbits). lia. }
  unfold Bar.shift in Hq |- *.
  rewrite Hq.
  repeat split; try lia.
  unfold multiplier_Z.
  cbn [Bar.multiplier_].
  rewrite Hmul.
  reflexivity.
Qed.

Lemma reciprocal_of_denominator_admissible : forall params d,
  params_admissible params ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  reciprocal_admissible (Bar.reciprocal_of_denominator params d).
Proof.
  intros params d Hadm Hbits Hvalid.
  pose proof (constructor_sound_no_multiplier
    params d Hadm Hbits Hvalid) as [_ [Hden Hmul]].
  pose proof (valid_denominator_bounds params d Hvalid) as [Hmin Hmax].
  destruct Hadm as [Hminpos [Hminmax Hinputpos]].
  unfold reciprocal_admissible.
  change (Bar.reciprocal_params (Bar.reciprocal_of_denominator params d))
    with params.
  repeat split; try lia.
  - unfold Bar.reciprocal_of_denominator.
    destruct (Div.udivrem (Bar.numerator_words params)
      Bar.uint256_num_words (Bar.numerator params) (Bar.uint256_to_words d));
      cbn [Bar.reciprocal_]; apply fit_words_length.
  - unfold Bar.reciprocal_of_denominator.
    destruct (Div.udivrem (Bar.numerator_words params)
      Bar.uint256_num_words (Bar.numerator params) (Bar.uint256_to_words d));
      cbn [Bar.denominator_]; apply fit_words_length.
  - unfold Bar.reciprocal_of_denominator.
    destruct (Div.udivrem (Bar.numerator_words params)
      Bar.uint256_num_words (Bar.numerator params) (Bar.uint256_to_words d));
      cbn [Bar.multiplier_]; apply WL.extend_words_length.
  - unfold reciprocal_scale_factor.
    change (Bar.reciprocal_params
      (Bar.reciprocal_of_denominator params d)) with params.
    rewrite (multiplier_words_zero params Hbits). cbn [Nat.eqb].
    lia.
  - rewrite Hmul.
    pose proof (WL.modulus_words_pos (Bar.multiplier_words params)).
    lia.
Qed.

Lemma reciprocal_of_multiplier_admissible : forall params y d,
  params_admissible params ->
  (0 < Bar.multiplier_bits params)%nat ->
  Bar.bit_shift params = 0%nat ->
  uint256_fits_words (Bar.multiplier_words params) y ->
  to_Z_uint256 y <= 2 ^ Z.of_nat (Bar.multiplier_bits params) ->
  Bar.valid_denominator params d = true ->
  reciprocal_admissible (Bar.reciprocal_of_multiplier params y d).
Proof.
  intros params y d Hadm Hbits Hbit Hy_fit Hy_bits Hvalid.
  pose proof (constructor_sound_with_multiplier
    params y d Hadm Hbits Hbit Hy_fit Hvalid) as [_ [Hden Hmul]].
  pose proof (valid_denominator_bounds params d Hvalid) as [Hmin Hmax].
  destruct Hadm as [Hminpos [Hminmax Hinputpos]].
  unfold reciprocal_admissible.
  change (Bar.reciprocal_params (Bar.reciprocal_of_multiplier params y d))
    with params.
  repeat split; try lia.
  - unfold Bar.reciprocal_of_multiplier.
    destruct (Div.udivrem (Bar.numerator_words params)
      Bar.uint256_num_words
      (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
      (Bar.uint256_to_words d)); cbn [Bar.reciprocal_];
      apply fit_words_length.
  - unfold Bar.reciprocal_of_multiplier.
    destruct (Div.udivrem (Bar.numerator_words params)
      Bar.uint256_num_words
      (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
      (Bar.uint256_to_words d)); cbn [Bar.denominator_];
      apply fit_words_length.
  - unfold Bar.reciprocal_of_multiplier.
    destruct (Div.udivrem (Bar.numerator_words params)
      Bar.uint256_num_words
      (Bar.numerator_with_multiplier params (Bar.uint256_to_words y))
      (Bar.uint256_to_words d)); cbn [Bar.multiplier_];
      apply fit_words_length.
  - unfold reciprocal_scale_factor.
    change (Bar.reciprocal_params
      (Bar.reciprocal_of_multiplier params y d)) with params.
    replace (Nat.eqb (Bar.multiplier_words params) 0%nat) with false.
    2: { symmetry. apply Nat.eqb_neq.
         pose proof (multiplier_words_positive params Hbits). lia. }
    rewrite Hmul. exact Hy_bits.
  - rewrite Hmul.
    exact Hy_fit.
Qed.

Lemma reciprocal_scale_nonneg : forall rec,
  0 <= reciprocal_scale_factor rec.
Proof.
  intro rec.
  unfold reciprocal_scale_factor, multiplier_Z.
  destruct (Nat.eqb (Bar.multiplier_words (Bar.reciprocal_params rec)) 0%nat);
    try lia.
  pose proof (WL.to_Z_words_bound (Bar.multiplier_ rec)). lia.
Qed.

Lemma reciprocal_upper_bound : forall rec,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  reciprocal_Z rec <=
    2 ^ Z.of_nat (Bar.max_quotient_bits (Bar.reciprocal_params rec)).
Proof.
  intros rec Hinv Hadm.
  set (params := Bar.reciprocal_params rec).
  destruct Hinv as [Hd_pos Hr].
  destruct Hadm as [Hadm_params [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  pose proof (min_denominator_bits_positive params Hadm_params) as HDpos.
  pose proof (min_denominator_value_lower_bound params Hadm_params)
    as Hden_min_lower.
  unfold Bar.max_quotient_bits.
  fold params.
  rewrite Hr.
  apply Z.div_le_upper_bound; [exact Hd_pos|].
  unfold Bar.shift.
  eapply Z.le_trans.
  - apply Z.mul_le_mono_nonneg_r.
    + apply Z.pow_nonneg. lia.
    + exact Hscale_bound.
  - change (Bar.reciprocal_params rec) with params.
    transitivity
      (2 ^ Z.of_nat (Bar.min_denominator_bits params - 1) *
       2 ^ Z.of_nat
         (Bar.input_bits params + Bar.multiplier_bits params -
          Bar.min_denominator_bits params + 1)).
    + apply pow_max_quotient_scale_bound.
      exact HDpos.
    + apply Z.mul_le_mono_nonneg_r.
      * apply Z.pow_nonneg. lia.
      * eapply Z.le_trans; [exact Hden_min_lower|exact Hden_min].
Qed.

Lemma pre_product_shift_positive_multiplier_bits_zero : forall params,
  (0 < Bar.pre_product_shift params)%nat ->
  Bar.multiplier_bits params = 0%nat.
Proof.
  intros params Hpre.
  unfold Bar.pre_product_shift in Hpre.
  destruct (Nat.eqb (Bar.multiplier_bits params) 0%nat) eqn:Hm.
  - apply Nat.eqb_eq. exact Hm.
  - lia.
Qed.

Lemma reciprocal_scale_no_multiplier_bits : forall rec,
  Bar.multiplier_bits (Bar.reciprocal_params rec) = 0%nat ->
  reciprocal_scale_factor rec = 1.
Proof.
  intros rec Hbits.
  unfold reciprocal_scale_factor.
  rewrite (multiplier_words_zero (Bar.reciprocal_params rec) Hbits).
  reflexivity.
Qed.

Lemma pre_product_shift_le_pred_min_denominator_bits : forall params,
  (Bar.pre_product_shift params <=
   Nat.pred (Bar.min_denominator_bits params))%nat.
Proof.
  intro params.
  unfold Bar.pre_product_shift.
  destruct (Nat.eqb (Bar.multiplier_bits params) 0%nat); [|lia].
  destruct (Nat.leb
    (Nat.pred (Bar.min_denominator_bits params) mod Bar.word_width)
    (Bar.bit_shift params)); lia.
Qed.

Lemma denominator_ge_pre_shift_pow : forall rec,
  reciprocal_admissible rec ->
  2 ^ Z.of_nat (Bar.pre_product_shift (Bar.reciprocal_params rec)) <=
    denominator_Z rec.
Proof.
  intros rec Hadm.
  set (params := Bar.reciprocal_params rec).
  destruct Hadm as [Hadm_params [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  pose proof (pre_product_shift_le_pred_min_denominator_bits params)
    as Hpre_le.
  pose proof (min_denominator_bits_positive params Hadm_params) as HDpos.
  pose proof (min_denominator_value_lower_bound params Hadm_params)
    as Hmin_low.
  replace (Nat.pred (Bar.min_denominator_bits params)) with
    (Bar.min_denominator_bits params - 1)%nat in Hpre_le by lia.
  eapply Z.le_trans.
  - apply Z.pow_le_mono_r; try lia.
    apply Nat2Z.inj_le. exact Hpre_le.
  - eapply Z.le_trans; [exact Hmin_low|exact Hden_min].
Qed.

Lemma online_numerator_value : forall rec x,
  reciprocal_admissible rec ->
  online_numerator_Z rec x =
    input_value_Z rec x * reciprocal_scale_factor rec.
Proof.
  intros rec x Hadm.
  set (params := Bar.reciprocal_params rec).
  destruct Hadm as [Hadm_params [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  unfold online_numerator_Z, input_value_Z.
  unfold Bar.online_numerator, reciprocal_scale_factor.
  fold params.
  destruct (Nat.eqb_spec (Bar.multiplier_words params) 0%nat) as [Hm0|Hmpos].
  - ring.
  - replace (Nat.eqb (Bar.multiplier_words params) 0%nat) with false.
    2: { symmetry. apply Nat.eqb_neq. exact Hmpos. }
    unfold Bar.wide_mul.
    rewrite truncating_mul_full_exact.
    + unfold multiplier_Z. ring.
    + rewrite fit_words_length. unfold Bar.input_words.
      apply min_words_positive.
      destruct Hadm_params as [_ [_ Hinput]]. exact Hinput.
    + rewrite Hmul_len.
      change (0 < Bar.multiplier_words params)%nat.
      lia.
Qed.

Lemma barrett_floor_no_preshift_bound : forall x k r d S,
  0 <= S ->
  0 <= x < 2 ^ S ->
  0 <= k ->
  0 < d ->
  r = (k * 2 ^ S) / d ->
  let Q := (x * k) / d in
  let qhat := (x * r) / 2 ^ S in
  Q - 1 <= qhat <= Q.
Proof.
  intros x k r d S HS Hx Hk Hd Hr.
  set (P := 2 ^ S) in *.
  assert (HP : 0 < P).
  { unfold P. apply Z.pow_pos_nonneg; lia. }
  assert (Hr_nonneg : 0 <= r).
  { subst r. apply Z.div_pos; nia. }
  assert (Hdr_le : d * r <= k * P).
  { subst r. apply Z.mul_div_le. lia. }
  assert (Hkp_lt : k * P < d * (r + 1)).
  { subst r.
    pose proof (Z.div_mod (k * P) d ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (k * P) d ltac:(lia)) as Hmod.
    nia. }
  assert (Hxr_le : P * ((x * r) / P) <= x * r).
  { apply Z.mul_div_le. lia. }
  assert (Hxr_lt : x * r < P * ((x * r) / P + 1)).
  { pose proof (Z.div_mod (x * r) P ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound (x * r) P ltac:(lia)) as Hmod.
    nia. }
  split.
  - assert (Hxk_lt : x * k < d * ((x * r) / P + 2)).
    { assert (H1 : x * k * P <= d * (x * r + x)) by nia.
      assert (H2 : d * (x * r + x) < d * (x * r + P)).
      { apply Z.mul_lt_mono_pos_l; lia. }
      assert (H3 : d * (x * r + P) <
        d * (P * ((x * r) / P + 2))).
      { apply Z.mul_lt_mono_pos_l; [lia|]. nia. }
      assert (x * k * P < d * (P * ((x * r) / P + 2))) by lia.
      assert (P * (x * k) < P * (d * ((x * r) / P + 2))) by nia.
      nia. }
    pose proof (Z.div_lt_upper_bound
      (x * k) d ((x * r) / P + 2) Hd Hxk_lt).
    lia.
  - assert (Hdq_le : d * ((x * r) / P) <= x * k).
    { assert (P * (d * ((x * r) / P)) <= P * (x * k)) by nia.
      nia. }
    pose proof (Z.div_le_lower_bound
      (x * k) d ((x * r) / P) Hd Hdq_le).
    lia.
Qed.

Lemma barrett_floor_with_preshift_bound : forall x r d I B,
  0 <= I ->
  0 <= B <= I ->
  0 <= x < 2 ^ I ->
  0 < d ->
  2 ^ B <= d ->
  r = 2 ^ I / d ->
  let Q := x / d in
  let qhat := ((x / 2 ^ B) * r) / 2 ^ (I - B) in
  Q - 2 <= qhat <= Q.
Proof.
  intros x r d I B HI HB Hx Hd Hd_ge Hr.
  set (P := 2 ^ B) in *.
  set (S := 2 ^ (I - B)) in *.
  assert (HP : 0 < P) by (subst P; apply Z.pow_pos_nonneg; lia).
  assert (HS : 0 < S) by (subst S; apply Z.pow_pos_nonneg; lia).
  assert (HPI : P * S = 2 ^ I).
  { subst P S. rewrite <- Z.pow_add_r by lia.
    replace (B + (I - B)) with I by lia. reflexivity. }
  assert (Hr_nonneg : 0 <= r).
  { subst r. apply Z.div_pos; [apply Z.pow_nonneg; lia|exact Hd]. }
  assert (Hr_le_S : r <= S).
  { subst r.
    apply Z.div_le_upper_bound; [exact Hd|].
    rewrite <- HPI.
    apply Z.mul_le_mono_nonneg_r; lia. }
  set (xh := x / P).
  set (xl := x mod P).
  assert (Hxl : 0 <= xl < P).
  { subst xl. apply Z.mod_pos_bound. lia. }
  assert (Hx_decomp : x = P * xh + xl).
  { subst xh xl. pose proof (Z.div_mod x P ltac:(lia)) as Hdm. lia. }
  set (q0 := (x * r) / (P * S)).
  set (qhat := (xh * r) / S).
  assert (Hq0_bound : x / d - 1 <= q0 <= x / d).
  { subst q0. rewrite HPI.
    replace (x / d) with ((x * 1) / d) by
      (replace (x * 1) with x by ring; reflexivity).
    replace (x / d) with ((x * 1) / d) by
      (replace (x * 1) with x by ring; reflexivity).
    apply barrett_floor_no_preshift_bound with
      (k := 1) (r := r) (d := d) (S := I); try lia.
    rewrite Hr. replace (1 * 2 ^ I) with (2 ^ I) by ring.
    reflexivity. }
  assert (Hqhat_le_q0 : qhat <= q0).
  { subst qhat q0.
    apply Z.div_le_lower_bound; [nia|].
    rewrite Hx_decomp.
    assert (HSq : S * (xh * r / S) <= xh * r).
    { apply Z.mul_div_le. lia. }
    nia. }
  assert (Hq0_le_qhat_plus1 : q0 <= qhat + 1).
  { assert (Hlt : x * r < P * S * (qhat + 2)).
    { rewrite Hx_decomp.
      assert (Hxh_lt : xh * r < S * (qhat + 1)).
      { subst qhat.
        pose proof (Z.div_mod (xh * r) S ltac:(lia)) as Hdm.
        pose proof (Z.mod_pos_bound (xh * r) S ltac:(lia)) as Hmod.
        nia. }
      assert (Hxlr_lt : xl * r < P * S).
      { assert (H1 : xl * r <= (P - 1) * r) by nia.
        assert (H2 : (P - 1) * r <= (P - 1) * S).
        { apply Z.mul_le_mono_nonneg_l; nia. }
        nia. }
      nia. }
    subst q0.
    pose proof (Z.div_lt_upper_bound (x * r) (P * S) (qhat + 2)
      ltac:(nia) Hlt) as Hdiv_lt.
    lia. }
  split; lia.
Qed.

Lemma barrett_floor_with_preshift_bound_nat : forall x r d I B,
  (B <= I)%nat ->
  0 <= x < 2 ^ Z.of_nat I ->
  0 < d ->
  2 ^ Z.of_nat B <= d ->
  r = 2 ^ Z.of_nat I / d ->
  let Q := x / d in
  let qhat := ((x / 2 ^ Z.of_nat B) * r) / 2 ^ Z.of_nat (I - B) in
  Q - 2 <= qhat <= Q.
Proof.
  intros x r d I B HBI Hx Hd Hd_ge Hr.
  pose proof (barrett_floor_with_preshift_bound
    x r d (Z.of_nat I) (Z.of_nat B) ltac:(lia) ltac:(lia)
    Hx Hd Hd_ge Hr) as H.
  replace (Z.of_nat I - Z.of_nat B) with (Z.of_nat (I - B)) in H by lia.
  exact H.
Qed.

Lemma rshift_aux_zero_skipn : forall rem i ws,
  rem = length (skipn i ws) ->
  Bar.rshift_aux 0 0 i rem ws = skipn i ws.
Proof.
  induction rem as [|rem IH]; intros i ws Hlen.
  - cbn [Bar.rshift_aux].
    symmetry. apply length_zero_iff_nil. lia.
  - cbn [Bar.rshift_aux].
    destruct (skipn i ws) as [|w rest] eqn:Hsk.
    + cbn in Hlen. lia.
    + cbn in Hlen.
      replace (Nat.eqb 0 0) with true by reflexivity.
      assert (Hrest : rest = skipn (S i) ws).
      { change rest with (skipn 1 (w :: rest)).
        rewrite <- Hsk.
        rewrite skipn_skipn.
        replace (1 + i)%nat with (S i) by lia.
        reflexivity. }
      f_equal.
      * unfold Bar.get_word.
        rewrite <- (nth_skipn i ws 0 Bar.U64.zero).
        rewrite Hsk. reflexivity.
      * rewrite IH.
        -- symmetry. exact Hrest.
        -- rewrite <- Hrest. lia.
Qed.

Lemma rshift_aux_length : forall bit word i rem input,
  length (Bar.rshift_aux bit word i rem input) = rem.
Proof.
  intros bit word i rem.
  revert bit word i.
  induction rem as [|rem IH]; intros bit word i input;
    cbn [Bar.rshift_aux length].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma rshift_length : forall bits shift ws,
  length (Bar.rshift bits shift ws) = Bar.min_words (bits - shift).
Proof.
  intros bits shift ws.
  unfold Bar.rshift.
  apply rshift_aux_length.
Qed.

Lemma rshift_value_ge : forall bits shift ws,
  (bits <= shift)%nat ->
  to_Z_words (Bar.rshift bits shift ws) = 0.
Proof.
  intros bits shift ws Hle.
  pose proof (rshift_length bits shift ws) as Hlen.
  replace (bits - shift)%nat with 0%nat in Hlen by lia.
  rewrite min_words_zero in Hlen.
  pose proof (WL.to_Z_words_bound (Bar.rshift bits shift ws)) as Hbound.
  rewrite Hlen in Hbound.
  unfold modulus_words in Hbound. cbn in Hbound. lia.
Qed.

Lemma rshift_zero_value : forall bits ws,
  to_Z_words (Bar.rshift bits 0 ws) =
  to_Z_words (Bar.fit_words (Bar.min_words bits) ws).
Proof.
  intros bits ws.
  unfold Bar.rshift.
  replace (bits - 0)%nat with bits by lia.
  rewrite Nat.Div0.mod_0_l, Nat.Div0.div_0_l.
  rewrite rshift_aux_zero_skipn.
  - rewrite skipn_O. reflexivity.
  - rewrite skipn_O, fit_words_length. reflexivity.
Qed.

Lemma shift_right_words_length : forall ws shift,
  length (Div.shift_right_words ws shift) = length ws.
Proof.
  induction ws as [|w rest IH]; intro shift.
  - reflexivity.
  - cbn [Div.shift_right_words length]. rewrite IH. reflexivity.
Qed.

Lemma to_Z_words_firstn_mod : forall ws n,
  (n <= length ws)%nat ->
  to_Z_words (firstn n ws) = to_Z_words ws mod modulus_words n.
Proof.
  intros ws n Hn.
  pose proof (WL.to_Z_words_firstn_skipn ws n Hn) as Hsplit.
  pose proof (WL.to_Z_words_bound (firstn n ws)) as Hlow.
  rewrite firstn_length_le in Hlow by lia.
  rewrite Hsplit.
  rewrite Z.add_mod by (pose proof (WL.modulus_words_pos n); lia).
  replace (modulus_words n * to_Z_words (skipn n ws)) with
    (to_Z_words (skipn n ws) * modulus_words n) by ring.
  rewrite Z.mod_mul by (pose proof (WL.modulus_words_pos n); lia).
  rewrite Z.add_0_r.
  rewrite (Z.mod_small (to_Z_words (firstn n ws)) (modulus_words n))
    by exact Hlow.
  rewrite (Z.mod_small (to_Z_words (firstn n ws)) (modulus_words n))
    by exact Hlow.
  reflexivity.
Qed.

Lemma rshift_aux_shift_right_prefix_value : forall bit word i rem input,
  (bit < Bar.word_width)%nat ->
  (i + word + rem <= length input)%nat ->
  to_Z_words (Bar.rshift_aux bit word i rem input) =
  to_Z_words
    (firstn rem (Div.shift_right_words (skipn (i + word) input) bit)).
Proof.
  intros bit word i rem.
  revert bit word i.
  induction rem as [|rem IH]; intros bit word i input Hbit Hlen.
  - reflexivity.
  - cbn [Bar.rshift_aux].
    cbn [to_Z_words].
    rewrite IH by (try exact Hbit; lia).
    replace (S i + word)%nat with (S (i + word)) by lia.
    destruct (skipn (i + word) input) as [|lo rest] eqn:Hsk.
    + exfalso.
      assert (length (skipn (i + word) input) = 0%nat)
        by (rewrite Hsk; reflexivity).
      rewrite length_skipn in H. lia.
    + assert (Hlo : Bar.get_word input (i + word) = lo).
      { unfold Bar.get_word.
        replace (i + word)%nat with (i + word + 0)%nat by lia.
        rewrite <- (nth_skipn (i + word) input 0 Bar.U64.zero).
        rewrite Hsk. reflexivity. }
      assert (Hhigh : Bar.get_word input (i + S word) = hd Bar.U64.zero rest).
      { unfold Bar.get_word.
        replace (i + S word)%nat with (i + word + 1)%nat by lia.
        rewrite <- (nth_skipn (i + word) input 1 Bar.U64.zero).
        rewrite Hsk. destruct rest; reflexivity. }
      assert (Htail : skipn (S (i + word)) input = rest).
      { change rest with (skipn 1 (lo :: rest)).
        rewrite <- Hsk.
        rewrite skipn_skipn.
        replace (1 + (i + word))%nat with (S (i + word)) by lia.
        reflexivity. }
      rewrite Hlo, Hhigh, Htail.
      cbn [Div.shift_right_words firstn to_Z_words].
      destruct (Nat.eqb_spec bit 0%nat) as [Hbit0|Hbitnz].
      * subst bit.
        rewrite DP.shrd64_spec.
        2: { pose proof (Pos2Nat.is_pos WL.U64.width). lia. }
        cbn [Z.of_nat].
        replace (2 ^ (Z.pos width - 0)) with (base width).
        2: { unfold base. reflexivity. }
        rewrite Z.mod_mul by
          (unfold base; pose proof (Pos2Z.is_pos width); lia).
        change (2 ^ 0) with 1.
        rewrite Z.div_1_r.
        ring.
      * reflexivity.
Qed.

Lemma min_words_sub_shift_bound : forall bits shift,
  (shift <= bits)%nat ->
  (Nat.div shift Bar.word_width + Bar.min_words (bits - shift) <=
   Bar.min_words bits)%nat.
Proof.
  intros bits shift Hle.
  unfold Bar.min_words.
  set (w := Bar.word_width).
  assert (Hw : w <> 0%nat).
  { unfold w, Bar.word_width.
    pose proof (Pos2Nat.is_pos Bar.U64.width). lia. }
  pose proof (Nat.div_mod shift w Hw) as Hshift.
  set (q := Nat.div shift w) in *.
  set (r := Nat.modulo shift w) in *.
  assert (Hr : (r < w)%nat).
  { unfold r. apply Nat.mod_upper_bound. exact Hw. }
  replace bits with (q * w + (r + (bits - shift)))%nat at 2 by lia.
  replace (q * w + (r + (bits - shift)) + Nat.pred w)%nat with
    (q * w + (r + (bits - shift) + Nat.pred w))%nat by lia.
  rewrite Nat.div_add_l by exact Hw.
  apply Nat.add_le_mono_l.
  apply Nat.Div0.div_le_mono.
  lia.
Qed.

Lemma word_bit_div : forall low high MW p,
  0 < MW ->
  0 < p ->
  0 <= low < MW ->
  0 <= high ->
  (low + MW * high) / (MW * p) = high / p.
Proof.
  intros low high MW p HMW Hp Hlow Hhigh.
  pose proof (Z.div_mod high p ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound high p ltac:(lia)) as Hmod.
  rewrite Hdm at 1.
  replace (low + MW * (p * (high / p) + high mod p)) with
    (high / p * (MW * p) + (low + MW * (high mod p))) by ring.
  rewrite Z.div_add_l by nia.
  replace ((low + MW * (high mod p)) / (MW * p)) with 0 by
    (symmetry; apply Z.div_small; split; nia).
  lia.
Qed.

Lemma rshift_value_small : forall bits shift ws,
  (shift <= bits)%nat ->
  0 <= to_Z_words (Bar.fit_words (Bar.min_words bits) ws) <
    2 ^ Z.of_nat bits ->
  to_Z_words (Bar.rshift bits shift ws) =
    to_Z_words (Bar.fit_words (Bar.min_words bits) ws) /
    2 ^ Z.of_nat shift.
Proof.
  intros bits shift ws Hle Hbound.
  unfold Bar.rshift.
  set (R := Bar.min_words (bits - shift)).
  set (N := Bar.min_words bits).
  set (input0 := Bar.fit_words N ws).
  assert (Hinput0_bound :
    0 <= to_Z_words input0 < 2 ^ Z.of_nat bits).
  { subst input0 N. exact Hbound. }
  set (bit := (shift mod Bar.word_width)%nat).
  set (word := (shift / Bar.word_width)%nat).
  assert (Hbit : (bit < Bar.word_width)%nat).
  { subst bit. apply Nat.mod_upper_bound.
    unfold Bar.word_width. pose proof (Pos2Nat.is_pos Bar.U64.width).
    lia. }
  assert (Hlen_input0 : length input0 = N).
  { subst input0 N. apply fit_words_length. }
  assert (Hword_R : (word + R <= N)%nat).
  { subst word R N. apply min_words_sub_shift_bound. exact Hle. }
  rewrite (rshift_aux_shift_right_prefix_value bit word 0 R input0 Hbit).
  2: { rewrite Hlen_input0. lia. }
  set (shifted := Div.shift_right_words (skipn (0 + word) input0) bit).
  assert (HR_shifted : (R <= length shifted)%nat).
  { subst shifted. rewrite shift_right_words_length, length_skipn. lia. }
  rewrite (to_Z_words_firstn_mod shifted R HR_shifted).
  subst shifted.
  rewrite DP.shift_right_words_correct.
  2: { unfold Bar.word_width in Hbit. exact Hbit. }
  replace (0 + word)%nat with word by lia.
  pose proof (WL.to_Z_words_firstn_skipn input0 word
    ltac:(rewrite Hlen_input0; lia)) as Hsplit.
  set (low := to_Z_words (firstn word input0)).
  set (high := to_Z_words (skipn word input0)).
  assert (Hlow_bound : 0 <= low < modulus_words word).
  { subst low. pose proof (WL.to_Z_words_bound (firstn word input0)) as H.
    rewrite firstn_length_le in H by (rewrite Hlen_input0; lia). exact H. }
  assert (Hhigh_nonneg : 0 <= high).
  { subst high. pose proof (WL.to_Z_words_bound (skipn word input0)). lia. }
  assert (Hinput_decomp : to_Z_words input0 = low + modulus_words word * high).
  { subst low high. exact Hsplit. }
  assert (Hpow_shift :
    2 ^ Z.of_nat shift = modulus_words word * 2 ^ Z.of_nat bit).
  { subst word bit.
    unfold Bar.word_width in *.
    rewrite Bar.U64.width_is_64 in *.
    change (Pos.to_nat 64) with 64%nat in *.
    pose proof (Nat.div_mod shift 64 ltac:(lia)) as Hdm.
    rewrite Hdm at 1.
    rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
    rewrite Z.pow_add_r by lia.
    rewrite RMP.pow64_modulus_words.
    reflexivity. }
  assert (Hdiv_eq :
    high / 2 ^ Z.of_nat bit = to_Z_words input0 / 2 ^ Z.of_nat shift).
  { rewrite Hinput_decomp, Hpow_shift.
    symmetry.
    apply word_bit_div.
    - pose proof (WL.modulus_words_pos word). lia.
    - apply Z.pow_pos_nonneg; lia.
    - exact Hlow_bound.
    - exact Hhigh_nonneg. }
  rewrite Hdiv_eq.
  apply Z.mod_small.
  assert (Hquot_bound :
    0 <= to_Z_words input0 / 2 ^ Z.of_nat shift <
      2 ^ Z.of_nat (bits - shift)).
  { split.
    - apply Z.div_pos; [lia|apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + replace (2 ^ Z.of_nat shift * 2 ^ Z.of_nat (bits - shift)) with
          (2 ^ Z.of_nat bits).
        * exact (proj2 Hinput0_bound).
        * rewrite <- Z.pow_add_r by lia.
          replace (Z.of_nat shift + Z.of_nat (bits - shift))
            with (Z.of_nat bits) by lia.
          reflexivity. }
  split; [exact (proj1 Hquot_bound)|].
  eapply Z.lt_le_trans; [exact (proj2 Hquot_bound)|].
  subst R. apply pow_le_modulus_min_words.
Qed.

Lemma estimate_q_no_preshift_value : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  Bar.pre_product_shift (Bar.reciprocal_params rec) = 0%nat ->
  input_within_bound rec x ->
  estimate_q_Z true rec x =
    (input_value_Z rec x * reciprocal_Z rec) /
    2 ^ Z.of_nat (Bar.input_bits (Bar.reciprocal_params rec)).
Proof.
  intros rec x Hinv Hadm Hpre Hinput.
  set (params := Bar.reciprocal_params rec).
  assert (Hpre_params : Bar.pre_product_shift params = 0%nat).
  { subst params. exact Hpre. }
  destruct Hadm as [Hadm_params0 [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  destruct Hadm_params0 as [Hmin_pos [Hmin_le_max Hinput_pos]].
  assert (Hadm_params : params_admissible params).
  { repeat split; assumption. }
  set (Qbits := Bar.max_quotient_bits params).
  set (Pbits := (Qbits + Bar.input_bits params)%nat).
  set (R := Bar.min_words Pbits).
  set (x_shift := Bar.rshift (Bar.input_bits params)
    (Bar.pre_product_shift params) x).
  set (prod := Bar.truncating_mul R x_shift (Bar.reciprocal_ rec)).
  assert (Hx_shift_val : to_Z_words x_shift = input_value_Z rec x).
  { subst x_shift. rewrite Hpre_params. rewrite rshift_zero_value.
    unfold input_value_Z. fold params. reflexivity. }
  assert (Hx_shift_len : length x_shift = Bar.input_words params).
  { subst x_shift. rewrite rshift_length.
    rewrite Hpre_params.
    replace (Bar.input_bits params - 0)%nat with
      (Bar.input_bits params) by lia.
    unfold Bar.input_words. reflexivity. }
  assert (Hx_shift_pos : (0 < length x_shift)%nat).
  { rewrite Hx_shift_len. unfold Bar.input_words.
    apply min_words_positive.
    change (Bar.input_bits params) with
      (Bar.input_bits (Bar.reciprocal_params rec)).
    exact Hinput_pos. }
  assert (HR_pos : (0 < R)%nat).
  { subst R Pbits Qbits. apply min_words_positive.
    change (Bar.input_bits params) with
      (Bar.input_bits (Bar.reciprocal_params rec)).
    lia. }
  assert (Hadm_rec : reciprocal_admissible rec).
  { repeat split; try exact Hadm_params; assumption. }
  pose proof (reciprocal_upper_bound rec Hinv Hadm_rec) as Hrec_upper.
  assert (Hrec_nonneg : 0 <= reciprocal_Z rec).
  { unfold reciprocal_Z. pose proof (WL.to_Z_words_bound (Bar.reciprocal_ rec)).
    lia. }
  assert (Hprod_bits_bound :
    input_value_Z rec x * reciprocal_Z rec < 2 ^ Z.of_nat Pbits).
  { subst Pbits Qbits.
    rewrite Nat2Z.inj_add.
    rewrite Z.pow_add_r by lia.
    destruct Hinput as [Hx_nonneg Hx_lt].
    change (Bar.input_bits (Bar.reciprocal_params rec)) with
      (Bar.input_bits params) in Hx_lt.
    change (Bar.max_quotient_bits (Bar.reciprocal_params rec)) with
      (Bar.max_quotient_bits params) in Hrec_upper.
    pose proof (Z.pow_nonneg 2 (Z.of_nat (Bar.input_bits params))
      ltac:(lia)).
    pose proof (Z.pow_nonneg 2 (Z.of_nat (Bar.max_quotient_bits params))
      ltac:(lia)).
    nia. }
  assert (Hprod_exact :
    to_Z_words prod = input_value_Z rec x * reciprocal_Z rec).
  { subst prod R.
    rewrite <- Hx_shift_val.
    unfold reciprocal_Z.
    apply truncating_mul_exact_small_general.
    - exact Hx_shift_pos.
    - exact HR_pos.
    - rewrite Hx_shift_val.
      fold (reciprocal_Z rec).
      eapply Z.lt_le_trans; [exact Hprod_bits_bound|].
      apply pow_le_modulus_min_words. }
  unfold estimate_q_Z, Bar.estimate_q.
  fold params.
  rewrite Hpre_params.
  unfold Bar.post_product_shift, Bar.shift.
  rewrite Hpre_params.
  replace (Bar.input_bits params - 0)%nat with
    (Bar.input_bits params) by lia.
  change (Bar.max_quotient_bits params) with Qbits.
  change (Qbits + Bar.input_bits params)%nat with Pbits.
  change (Bar.min_words Pbits) with R.
  replace (Bar.rshift (Bar.input_bits params) 0 x) with x_shift.
  2: { subst x_shift. rewrite Hpre_params. reflexivity. }
  change (Bar.truncating_mul R x_shift (Bar.reciprocal_ rec)) with prod.
  rewrite rshift_value_small.
  - rewrite to_Z_fit_words_small.
    + rewrite Hprod_exact. reflexivity.
    + rewrite Hprod_exact.
      eapply Z.lt_le_trans; [exact Hprod_bits_bound|].
      apply pow_le_modulus_min_words.
  - subst Pbits Qbits. lia.
  - rewrite to_Z_fit_words_small.
    + rewrite Hprod_exact.
      split.
      * destruct Hinput as [Hx_nonneg _].
        apply Z.mul_nonneg_nonneg; assumption.
      * exact Hprod_bits_bound.
    + rewrite Hprod_exact.
      eapply Z.lt_le_trans; [exact Hprod_bits_bound|].
      apply pow_le_modulus_min_words.
Qed.

Theorem estimate_q_sound_no_preshift : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  Bar.pre_product_shift (Bar.reciprocal_params rec) = 0%nat ->
  input_within_bound rec x ->
  let Q := Z.div (online_numerator_Z rec x) (denominator_Z rec) in
  Q - 1 <= estimate_q_Z true rec x <= Q.
Proof.
  intros rec x Hinv Hadm Hpre Hinput.
  rewrite (estimate_q_no_preshift_value rec x Hinv Hadm Hpre Hinput).
  rewrite (online_numerator_value rec x Hadm).
  set (params := Bar.reciprocal_params rec).
  destruct Hinv as [Hd_pos Hr].
  unfold reciprocal_invariant in Hr.
  fold params in Hr.
  unfold Bar.shift in Hr.
  rewrite Hr.
  apply barrett_floor_no_preshift_bound.
  - lia.
  - exact Hinput.
  - apply reciprocal_scale_nonneg.
  - exact Hd_pos.
  - reflexivity.
Qed.

Lemma estimate_q_with_preshift_value_small : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  (Bar.pre_product_shift (Bar.reciprocal_params rec) <
   Bar.input_bits (Bar.reciprocal_params rec))%nat ->
  input_within_bound rec x ->
  estimate_q_Z true rec x =
    ((input_value_Z rec x /
      2 ^ Z.of_nat (Bar.pre_product_shift (Bar.reciprocal_params rec))) *
     reciprocal_Z rec) /
    2 ^ Z.of_nat (Bar.post_product_shift (Bar.reciprocal_params rec)).
Proof.
  intros rec x Hinv Hadm Hpre_lt Hinput.
  set (params := Bar.reciprocal_params rec).
  assert (Hpre_lt_params :
    (Bar.pre_product_shift params < Bar.input_bits params)%nat).
  { subst params. exact Hpre_lt. }
  destruct Hadm as [Hadm_params0 [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  destruct Hadm_params0 as [Hmin_pos [Hmin_le_max Hinput_pos]].
  assert (Hadm_params : params_admissible params).
  { repeat split; assumption. }
  set (B := Bar.pre_product_shift params).
  set (T := Bar.post_product_shift params).
  set (Qbits := Bar.max_quotient_bits params).
  set (Pbits := (Qbits + T)%nat).
  set (R := Bar.min_words Pbits).
  set (x_shift := Bar.rshift (Bar.input_bits params) B x).
  set (prod := Bar.truncating_mul R x_shift (Bar.reciprocal_ rec)).
  assert (HT : T = (Bar.input_bits params - B)%nat).
  { subst T B. unfold Bar.post_product_shift, Bar.shift. reflexivity. }
  assert (Hx_shift_val :
    to_Z_words x_shift = input_value_Z rec x / 2 ^ Z.of_nat B).
  { subst x_shift B. apply rshift_value_small.
    - lia.
    - exact Hinput. }
  assert (Hx_shift_len : length x_shift =
    Bar.min_words (Bar.input_bits params - B)).
  { subst x_shift B. apply rshift_length. }
  assert (Hx_shift_pos : (0 < length x_shift)%nat).
  { rewrite Hx_shift_len.
    apply min_words_positive. lia. }
  assert (HR_pos : (0 < R)%nat).
  { subst R Pbits Qbits T. apply min_words_positive. lia. }
  assert (Hadm_rec : reciprocal_admissible rec).
  { repeat split; try exact Hadm_params; assumption. }
  pose proof (reciprocal_upper_bound rec Hinv Hadm_rec) as Hrec_upper.
  assert (Hrec_nonneg : 0 <= reciprocal_Z rec).
  { unfold reciprocal_Z. pose proof (WL.to_Z_words_bound (Bar.reciprocal_ rec)).
    lia. }
  assert (Hx_shift_bound :
    0 <= input_value_Z rec x / 2 ^ Z.of_nat B < 2 ^ Z.of_nat T).
  { rewrite HT.
    destruct Hinput as [Hx_nonneg Hx_lt].
    split.
    - apply Z.div_pos; [exact Hx_nonneg|apply Z.pow_pos_nonneg; lia].
    - apply Z.div_lt_upper_bound.
      + apply Z.pow_pos_nonneg; lia.
      + replace (2 ^ Z.of_nat B *
          2 ^ Z.of_nat (Bar.input_bits params - B)) with
          (2 ^ Z.of_nat (Bar.input_bits params)).
        * exact Hx_lt.
        * rewrite <- Z.pow_add_r by lia.
          replace (Z.of_nat B + Z.of_nat (Bar.input_bits params - B))
            with (Z.of_nat (Bar.input_bits params)) by lia.
          reflexivity. }
  assert (Hprod_bits_bound :
    (input_value_Z rec x / 2 ^ Z.of_nat B) * reciprocal_Z rec <
      2 ^ Z.of_nat Pbits).
  { subst Pbits Qbits.
    rewrite Nat2Z.inj_add.
    rewrite Z.pow_add_r by lia.
    destruct Hx_shift_bound as [Hx_nonneg Hx_lt].
    change (Bar.max_quotient_bits (Bar.reciprocal_params rec)) with
      (Bar.max_quotient_bits params) in Hrec_upper.
    pose proof (Z.pow_nonneg 2 (Z.of_nat T) ltac:(lia)).
    pose proof (Z.pow_nonneg 2 (Z.of_nat (Bar.max_quotient_bits params))
      ltac:(lia)).
    nia. }
  assert (Hprod_exact :
    to_Z_words prod =
      (input_value_Z rec x / 2 ^ Z.of_nat B) * reciprocal_Z rec).
  { subst prod R.
    rewrite <- Hx_shift_val.
    unfold reciprocal_Z.
    apply truncating_mul_exact_small_general.
    - exact Hx_shift_pos.
    - exact HR_pos.
    - rewrite Hx_shift_val.
      fold (reciprocal_Z rec).
      eapply Z.lt_le_trans; [exact Hprod_bits_bound|].
      apply pow_le_modulus_min_words. }
  unfold estimate_q_Z, Bar.estimate_q.
  fold params.
  change (Bar.pre_product_shift params) with B.
  change (Bar.post_product_shift params) with T.
  change (Bar.max_quotient_bits params) with Qbits.
  change (Qbits + T)%nat with Pbits.
  change (Bar.min_words Pbits) with R.
  change (Bar.rshift (Bar.input_bits params) B x) with x_shift.
  change (Bar.truncating_mul R x_shift (Bar.reciprocal_ rec)) with prod.
  rewrite rshift_value_small.
  - rewrite to_Z_fit_words_small.
    + rewrite Hprod_exact. reflexivity.
    + rewrite Hprod_exact.
      eapply Z.lt_le_trans; [exact Hprod_bits_bound|].
      apply pow_le_modulus_min_words.
  - subst Pbits Qbits T. lia.
  - rewrite to_Z_fit_words_small.
    + rewrite Hprod_exact.
      split.
      * destruct Hx_shift_bound as [Hx_nonneg _].
        apply Z.mul_nonneg_nonneg; assumption.
      * exact Hprod_bits_bound.
    + rewrite Hprod_exact.
      eapply Z.lt_le_trans; [exact Hprod_bits_bound|].
      apply pow_le_modulus_min_words.
Qed.

Lemma estimate_q_preshift_ge_zero : forall rec x,
  (Bar.input_bits (Bar.reciprocal_params rec) <=
   Bar.pre_product_shift (Bar.reciprocal_params rec))%nat ->
  estimate_q_Z true rec x = 0.
Proof.
  intros rec x Hge.
  set (params := Bar.reciprocal_params rec).
  assert (Hge_params :
    (Bar.input_bits params <= Bar.pre_product_shift params)%nat).
  { subst params. exact Hge. }
  unfold estimate_q_Z, Bar.estimate_q.
  fold params.
  set (x_shift := Bar.rshift (Bar.input_bits params)
    (Bar.pre_product_shift params) x).
  assert (Hx_shift_nil : x_shift = []).
  { apply length_zero_iff_nil.
    subst x_shift. rewrite rshift_length.
    replace (Bar.input_bits params - Bar.pre_product_shift params)%nat
      with 0%nat by lia.
    apply min_words_zero. }
  rewrite Hx_shift_nil.
  unfold Bar.post_product_shift, Bar.shift.
  replace (Bar.input_bits params - Bar.pre_product_shift params)%nat
    with 0%nat by lia.
  set (R := Bar.min_words (Bar.max_quotient_bits params + 0)).
  set (prod := Bar.truncating_mul R [] (Bar.reciprocal_ rec)).
  change (Bar.truncating_mul R [] (Bar.reciprocal_ rec)) with prod.
  rewrite rshift_zero_value.
  rewrite to_Z_fit_words_small.
  - subst prod. apply truncating_mul_left_nil_value.
  - subst prod. rewrite truncating_mul_left_nil_value.
    pose proof (WL.modulus_words_pos
      (Bar.min_words (Bar.max_quotient_bits params + 0))).
    lia.
Qed.

Theorem estimate_q_sound_with_preshift : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  (0 < Bar.pre_product_shift (Bar.reciprocal_params rec))%nat ->
  input_within_bound rec x ->
  let Q := Z.div (online_numerator_Z rec x) (denominator_Z rec) in
  Q - 2 <= estimate_q_Z true rec x <= Q.
Proof.
  intros rec x Hinv Hadm Hpre_pos Hinput.
  set (params := Bar.reciprocal_params rec).
  set (B := Bar.pre_product_shift params).
  set (I := Bar.input_bits params).
  assert (Hbits0 : Bar.multiplier_bits params = 0%nat).
  { subst B I params. apply pre_product_shift_positive_multiplier_bits_zero.
    exact Hpre_pos. }
  assert (Hscale1 : reciprocal_scale_factor rec = 1).
  { subst params. apply reciprocal_scale_no_multiplier_bits. exact Hbits0. }
  assert (Honline : online_numerator_Z rec x = input_value_Z rec x).
  { rewrite online_numerator_value by exact Hadm. rewrite Hscale1. ring. }
  destruct (Nat.lt_ge_cases B I) as [HBlt|HBge].
  - rewrite (estimate_q_with_preshift_value_small rec x Hinv Hadm).
    2: { subst B I params. exact HBlt. }
    2: { exact Hinput. }
    rewrite Honline.
    destruct Hinv as [Hd_pos Hr].
    unfold reciprocal_invariant in Hr.
    fold params in Hr.
    unfold Bar.shift in Hr.
    rewrite Hscale1 in Hr.
    rewrite Hr.
    change (Bar.pre_product_shift (Bar.reciprocal_params rec)) with B.
    replace (Bar.post_product_shift (Bar.reciprocal_params rec)) with
      (I - B)%nat.
    2: { subst I B params. unfold Bar.post_product_shift, Bar.shift.
         reflexivity. }
    change (Bar.input_bits params) with I.
    replace (1 * 2 ^ Z.of_nat I / denominator_Z rec) with
      (2 ^ Z.of_nat I / denominator_Z rec).
    2: { replace (1 * 2 ^ Z.of_nat I) with (2 ^ Z.of_nat I) by ring.
         reflexivity. }
    apply barrett_floor_with_preshift_bound_nat.
    + lia.
    + exact Hinput.
    + exact Hd_pos.
    + subst B params. apply denominator_ge_pre_shift_pow.
      exact Hadm.
    + reflexivity.
  - rewrite (estimate_q_preshift_ge_zero rec x).
    2: { subst B I params. exact HBge. }
    rewrite Honline.
    assert (HQ0 : input_value_Z rec x / denominator_Z rec = 0).
    { destruct Hinput as [Hx_nonneg Hx_lt].
      apply Z.div_small.
      split; [exact Hx_nonneg|].
      eapply Z.lt_le_trans; [exact Hx_lt|].
      subst I B.
      eapply Z.le_trans.
      - apply Z.pow_le_mono_r; try lia.
        apply Nat2Z.inj_le. exact HBge.
      - subst params. apply denominator_ge_pre_shift_pow. exact Hadm. }
    rewrite HQ0. lia.
Qed.

Theorem low_product_sufficient : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
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
  reciprocal_admissible rec ->
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
Proof.
  intros rec x _ Hadm Hbits _.
  set (params := Bar.reciprocal_params rec).
  destruct Hadm as [Hadm_params [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  pose proof (multiplier_words_positive params Hbits) as Hmwords_pos.
  pose proof (max_r_hat_words_positive params Hadm_params Hbits) as HR_pos.
  pose proof (max_r_hat_words_le_product_words params) as HR_le.
  set (xs := Bar.fit_words (Bar.input_words params) x).
  set (ys := Bar.multiplier_ rec).
  set (R := Bar.max_r_hat_words params).
  assert (Hxs_len : length xs = Bar.input_words params).
  { subst xs. apply fit_words_length. }
  assert (Hys_len : length ys = Bar.multiplier_words params).
  { subst ys. exact Hmul_len. }
  assert (Hxs_pos : (0 < length xs)%nat).
  { rewrite Hxs_len. unfold Bar.input_words. apply min_words_positive.
    destruct Hadm_params as [_ [_ Hinput]]. exact Hinput. }
  assert (Hys_pos : (0 < length ys)%nat).
  { rewrite Hys_len. exact Hmwords_pos. }
  assert (HR_le_sum : (R <= length xs + length ys)%nat).
  { subst R. rewrite Hxs_len, Hys_len. exact HR_le. }
  unfold online_numerator_Z, Bar.online_numerator.
  fold params xs ys R.
  replace (Nat.eqb (Bar.multiplier_words params) 0%nat) with false.
  2: { symmetry. apply Nat.eqb_neq. lia. }
  unfold Bar.wide_mul, Bar.truncating_mul.
  fold xs ys R.
  change (RM.truncating_mul_runtime xs ys (length xs + length ys)) with
    (Bar.truncating_mul (length xs + length ys) xs ys).
  rewrite truncating_mul_full_exact by assumption.
  pose proof (RMP.truncating_mul_runtime_correct xs ys R
    Hxs_pos Hys_pos HR_pos HR_le_sum) as Hlow.
  rewrite Hlow.
  reflexivity.
Qed.

Fixpoint word_window_value (R i : nat) (ws : Bar.words) : Z :=
  match R with
  | O => 0
  | S R' =>
      to_Z (Bar.get_word ws i) +
      base width * word_window_value R' (S i) ws
  end.

Lemma word_window_value_firstn_skipn : forall R ws i,
  word_window_value R i ws =
  to_Z_words (firstn R (skipn i ws)).
Proof.
  induction R as [|R IH]; intros ws i.
  - reflexivity.
  - cbn [word_window_value].
    destruct (skipn i ws) as [|w rest] eqn:Hskip.
    + assert (Hget : Bar.get_word ws i = Bar.U64.zero).
      { unfold Bar.get_word.
        apply nth_overflow.
        assert (Hlen_skip : length (skipn i ws) = 0%nat) by
          (rewrite Hskip; reflexivity).
        rewrite length_skipn in Hlen_skip. lia. }
      assert (HskipS : skipn (S i) ws = []).
      { apply skipn_all2.
        assert (Hlen_skip : length (skipn i ws) = 0%nat) by
          (rewrite Hskip; reflexivity).
        rewrite length_skipn in Hlen_skip. lia. }
      rewrite Hget, spec_zero.
      rewrite IH, HskipS.
      repeat rewrite firstn_nil.
      change (to_Z_words []) with 0.
      ring.
    + assert (Hget : Bar.get_word ws i = w).
      { unfold Bar.get_word.
        replace i with (i + 0)%nat by lia.
        rewrite <- (nth_skipn i ws 0 Bar.U64.zero).
        rewrite Hskip. reflexivity. }
      assert (HskipS : skipn (S i) ws = rest).
      { replace (S i) with (1 + i)%nat by lia.
        rewrite <- skipn_skipn.
        rewrite Hskip. reflexivity. }
      rewrite Hget, IH, HskipS.
      cbn [firstn to_Z_words]. reflexivity.
Qed.

Lemma to_Z_words_firstn_mod_total : forall R ws,
  to_Z_words (firstn R ws) = to_Z_words ws mod modulus_words R.
Proof.
  intros R ws.
  destruct (Nat.leb_spec0 R (length ws)) as [HR|HR].
  - apply to_Z_words_firstn_mod. exact HR.
  - rewrite firstn_all2 by lia.
    symmetry.
    apply Z.mod_small.
    pose proof (WL.to_Z_words_bound ws) as Hws.
    pose proof (WL.modulus_words_le (length ws) R ltac:(lia)).
    lia.
Qed.

Lemma word_window_value_mod : forall R ws,
  word_window_value R 0 ws = to_Z_words ws mod modulus_words R.
Proof.
  intros R ws.
  rewrite word_window_value_firstn_skipn.
  cbn [skipn].
  apply to_Z_words_firstn_mod_total.
Qed.

Lemma word_window_value_bound : forall R i ws,
  0 <= word_window_value R i ws < modulus_words R.
Proof.
  intros R i ws.
  rewrite word_window_value_firstn_skipn.
  pose proof (WL.to_Z_words_bound (firstn R (skipn i ws))) as Hbound.
  assert (Hlen : (length (firstn R (skipn i ws)) <= R)%nat).
  { rewrite length_firstn. lia. }
  pose proof (WL.modulus_words_le
    (length (firstn R (skipn i ws))) R Hlen) as Hmod_le.
  lia.
Qed.

Lemma subb_words_aux_length : forall R i lhs rhs borrow,
  length (fst (Bar.subb_words_aux R i lhs rhs borrow)) = R.
Proof.
  induction R as [|R IH]; intros i lhs rhs borrow.
  - reflexivity.
  - cbn [Bar.subb_words_aux fst].
    destruct (Bar.subb_words_aux R (S i) lhs rhs
      (Bar.carry64
         (Bar.subb64 (Bar.get_word lhs i) (Bar.get_word rhs i) borrow)))
      as [rest borrow'] eqn:Hrec.
    cbn [fst length].
    rewrite <- (IH (S i) lhs rhs
      (Bar.carry64
         (Bar.subb64 (Bar.get_word lhs i) (Bar.get_word rhs i) borrow))).
    rewrite Hrec. reflexivity.
Qed.

Lemma subb_words_aux_full_correct : forall R i lhs rhs borrow,
  let '(result, borrow') := Bar.subb_words_aux R i lhs rhs borrow in
  to_Z_words result - (if borrow' then modulus_words R else 0) =
  word_window_value R i lhs - word_window_value R i rhs -
  (if borrow then 1 else 0).
Proof.
  induction R as [|R IH]; intros i lhs rhs borrow.
  - cbn [Bar.subb_words_aux to_Z_words word_window_value].
    rewrite WL.modulus_words_0.
    destruct borrow; ring.
  - cbn [Bar.subb_words_aux word_window_value].
    set (step :=
      Bar.subb64 (Bar.get_word lhs i) (Bar.get_word rhs i) borrow).
    destruct (Bar.subb_words_aux R (S i) lhs rhs (Bar.carry64 step))
      as [rest borrow'] eqn:Hrec.
    cbn [to_Z_words].
    rewrite WL.modulus_words_succ.
    specialize (IH (S i) lhs rhs (Bar.carry64 step)).
    rewrite Hrec in IH.
    pose proof (AP.subb64_full_correct_word
      (Bar.get_word lhs i) (Bar.get_word rhs i) borrow) as Hstep.
    change (AP.value64 (AP.subb64 (Bar.get_word lhs i)
              (Bar.get_word rhs i) borrow))
      with (Bar.value64 step) in Hstep.
    change (AP.carry64 (AP.subb64 (Bar.get_word lhs i)
              (Bar.get_word rhs i) borrow))
      with (Bar.carry64 step) in Hstep.
    destruct (Bar.carry64 step); destruct borrow'; nia.
Qed.

Lemma subb_truncating_length : forall R lhs rhs,
  length (Bar.value_words (Bar.subb_truncating R lhs rhs)) = R.
Proof.
  intros R lhs rhs.
  unfold Bar.subb_truncating.
  destruct (Bar.subb_words_aux R 0 lhs rhs false) as [result borrow] eqn:H.
  cbn [Bar.value_words].
  pose proof (subb_words_aux_length R 0 lhs rhs false) as Hlen.
  rewrite H in Hlen. cbn [fst] in Hlen. exact Hlen.
Qed.

Lemma subb_truncating_value_mod : forall R lhs rhs,
  to_Z_words (Bar.value_words (Bar.subb_truncating R lhs rhs)) =
  (to_Z_words lhs - to_Z_words rhs) mod modulus_words R.
Proof.
  intros R lhs rhs.
  unfold Bar.subb_truncating.
  destruct (Bar.subb_words_aux R 0 lhs rhs false) as [result borrow] eqn:H.
  cbn [Bar.value_words Bar.carry_words].
  pose proof (subb_words_aux_full_correct R 0 lhs rhs false) as Hfull.
  rewrite H in Hfull. cbn [word_window_value] in Hfull.
  assert (Hres_bound : 0 <= to_Z_words result < modulus_words R).
  { pose proof (WL.to_Z_words_bound result) as Hbound.
    pose proof (subb_words_aux_length R 0 lhs rhs false) as Hlen.
    rewrite H in Hlen. cbn [fst] in Hlen.
    rewrite Hlen in Hbound. exact Hbound. }
  rewrite !word_window_value_mod in Hfull.
  rewrite <- (Z.mod_small (to_Z_words result) (modulus_words R))
    by exact Hres_bound.
  replace (to_Z_words result mod modulus_words R) with
    ((to_Z_words result - (if borrow then modulus_words R else 0)) mod
     modulus_words R).
  2: {
    destruct borrow.
    - replace (to_Z_words result - modulus_words R) with
        (to_Z_words result + (-1) * modulus_words R) by ring.
      rewrite Z.mod_add by (pose proof (WL.modulus_words_pos R); lia).
      reflexivity.
    - replace (to_Z_words result - 0) with (to_Z_words result) by ring.
      reflexivity. }
  rewrite Hfull.
  rewrite Z.sub_0_r.
  rewrite <- Zminus_mod by (pose proof (WL.modulus_words_pos R); lia).
  reflexivity.
Qed.

Lemma subb_truncating_borrow_correct : forall R lhs rhs,
  Bar.carry_words (Bar.subb_truncating R lhs rhs) =
  Z.ltb (to_Z_words lhs mod modulus_words R)
        (to_Z_words rhs mod modulus_words R).
Proof.
  intros R lhs rhs.
  unfold Bar.subb_truncating.
  destruct (Bar.subb_words_aux R 0 lhs rhs false) as [result borrow] eqn:H.
  cbn [Bar.value_words Bar.carry_words].
  pose proof (subb_words_aux_full_correct R 0 lhs rhs false) as Hfull.
  rewrite H in Hfull. cbn [word_window_value] in Hfull.
  rewrite !word_window_value_mod in Hfull.
  pose proof (WL.to_Z_words_bound result) as Hres_bound0.
  pose proof (subb_words_aux_length R 0 lhs rhs false) as Hlen.
  rewrite H in Hlen. cbn [fst] in Hlen.
  rewrite Hlen in Hres_bound0.
  pose proof (Z.mod_pos_bound (to_Z_words lhs) (modulus_words R)
    ltac:(pose proof (WL.modulus_words_pos R); lia)) as Hlhs.
  pose proof (Z.mod_pos_bound (to_Z_words rhs) (modulus_words R)
    ltac:(pose proof (WL.modulus_words_pos R); lia)) as Hrhs.
  destruct borrow.
  - symmetry. apply Z.ltb_lt. lia.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma subb_zx_borrow_correct : forall lhs rhs,
  Bar.carry_words (Bar.subb_zx lhs rhs) =
  Z.ltb (to_Z_words lhs) (to_Z_words rhs).
Proof.
  intros lhs rhs.
  unfold Bar.subb_zx.
  rewrite subb_truncating_borrow_correct.
  set (R := Nat.max (length lhs) (length rhs)).
  pose proof (WL.to_Z_words_bound lhs) as Hlhs.
  pose proof (WL.to_Z_words_bound rhs) as Hrhs.
  pose proof (WL.modulus_words_le (length lhs) R ltac:(subst R; lia))
    as Hlhs_mod.
  pose proof (WL.modulus_words_le (length rhs) R ltac:(subst R; lia))
    as Hrhs_mod.
  rewrite Z.mod_small by lia.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma subb_zx_value_no_borrow : forall lhs rhs,
  to_Z_words rhs <= to_Z_words lhs ->
  to_Z_words (Bar.value_words (Bar.subb_zx lhs rhs)) =
  to_Z_words lhs - to_Z_words rhs.
Proof.
  intros lhs rhs Hle.
  unfold Bar.subb_zx.
  rewrite subb_truncating_value_mod.
  set (R := Nat.max (length lhs) (length rhs)).
  apply Z.mod_small.
  pose proof (WL.to_Z_words_bound lhs) as Hlhs.
  pose proof (WL.to_Z_words_bound rhs) as Hrhs.
  pose proof (WL.modulus_words_le (length lhs) R ltac:(subst R; lia))
    as Hlhs_mod.
  lia.
Qed.

Lemma addc_words_aux_length : forall R i lhs rhs carry,
  length (fst (Bar.addc_words_aux R i lhs rhs carry)) = R.
Proof.
  induction R as [|R IH]; intros i lhs rhs carry.
  - reflexivity.
  - cbn [Bar.addc_words_aux fst].
    destruct (Bar.addc_words_aux R (S i) lhs rhs
      (Bar.carry64
         (Bar.addc64 (Bar.get_word lhs i) (Bar.get_word rhs i) carry)))
      as [rest carry'] eqn:Hrec.
    cbn [fst length].
    rewrite <- (IH (S i) lhs rhs
      (Bar.carry64
         (Bar.addc64 (Bar.get_word lhs i) (Bar.get_word rhs i) carry))).
    rewrite Hrec. reflexivity.
Qed.

Lemma addc_words_aux_full_correct : forall R i lhs rhs carry,
  let '(result, carry') := Bar.addc_words_aux R i lhs rhs carry in
  to_Z_words result + (if carry' then modulus_words R else 0) =
  word_window_value R i lhs + word_window_value R i rhs +
  (if carry then 1 else 0).
Proof.
  induction R as [|R IH]; intros i lhs rhs carry.
  - cbn [Bar.addc_words_aux to_Z_words word_window_value].
    rewrite WL.modulus_words_0.
    destruct carry; ring.
  - cbn [Bar.addc_words_aux word_window_value].
    set (step :=
      Bar.addc64 (Bar.get_word lhs i) (Bar.get_word rhs i) carry).
    destruct (Bar.addc_words_aux R (S i) lhs rhs (Bar.carry64 step))
      as [rest carry'] eqn:Hrec.
    cbn [to_Z_words].
    rewrite WL.modulus_words_succ.
    specialize (IH (S i) lhs rhs (Bar.carry64 step)).
    rewrite Hrec in IH.
    pose proof (AP.addc64_full_correct_word
      (Bar.get_word lhs i) (Bar.get_word rhs i) carry) as Hstep.
    change (AP.value64 (AP.addc64 (Bar.get_word lhs i)
              (Bar.get_word rhs i) carry))
      with (Bar.value64 step) in Hstep.
    change (AP.carry64 (AP.addc64 (Bar.get_word lhs i)
              (Bar.get_word rhs i) carry))
      with (Bar.carry64 step) in Hstep.
    destruct (Bar.carry64 step); destruct carry'; nia.
Qed.

Lemma addc_words_length : forall lhs rhs,
  length (Bar.value_words (Bar.addc_words lhs rhs)) =
  Nat.max (length lhs) (length rhs).
Proof.
  intros lhs rhs.
  unfold Bar.addc_words.
  destruct (Bar.addc_words_aux (Nat.max (length lhs) (length rhs)) 0
    lhs rhs false) as [result carry] eqn:H.
  cbn [Bar.value_words].
  pose proof (addc_words_aux_length
    (Nat.max (length lhs) (length rhs)) 0 lhs rhs false) as Hlen.
  rewrite H in Hlen. cbn [fst] in Hlen. exact Hlen.
Qed.

Lemma addc_words_value_mod : forall lhs rhs,
  to_Z_words (Bar.value_words (Bar.addc_words lhs rhs)) =
  (to_Z_words lhs + to_Z_words rhs) mod
  modulus_words (Nat.max (length lhs) (length rhs)).
Proof.
  intros lhs rhs.
  unfold Bar.addc_words.
  set (R := Nat.max (length lhs) (length rhs)).
  destruct (Bar.addc_words_aux R 0 lhs rhs false)
    as [result carry] eqn:H.
  cbn [Bar.value_words Bar.carry_words].
  pose proof (addc_words_aux_full_correct R 0 lhs rhs false) as Hfull.
  rewrite H in Hfull. cbn [word_window_value] in Hfull.
  assert (Hres_bound : 0 <= to_Z_words result < modulus_words R).
  { pose proof (WL.to_Z_words_bound result) as Hbound.
    pose proof (addc_words_aux_length R 0 lhs rhs false) as Hlen.
    rewrite H in Hlen. cbn [fst] in Hlen.
    rewrite Hlen in Hbound. exact Hbound. }
  rewrite !word_window_value_mod in Hfull.
  rewrite <- (Z.mod_small (to_Z_words result) (modulus_words R))
    by exact Hres_bound.
  replace (to_Z_words result mod modulus_words R) with
    ((to_Z_words result + (if carry then modulus_words R else 0)) mod
     modulus_words R).
  2: {
    destruct carry.
    - replace (to_Z_words result + modulus_words R) with
        (to_Z_words result + 1 * modulus_words R) by ring.
      rewrite Z.mod_add by (pose proof (WL.modulus_words_pos R); lia).
      reflexivity.
    - replace (to_Z_words result + 0) with (to_Z_words result) by ring.
      reflexivity. }
  rewrite Hfull.
  rewrite Z.add_0_r.
  rewrite <- Zplus_mod by (pose proof (WL.modulus_words_pos R); lia).
  subst R. reflexivity.
Qed.

Lemma small_const_words_value : forall n c,
  (0 < n)%nat ->
  to_Z_words (Bar.small_const_words n c) = to_Z c.
Proof.
  intros n c Hn.
  unfold Bar.small_const_words.
  rewrite WL.to_Z_words_set_word.
  2: { rewrite WL.extend_words_length. lia. }
  rewrite WL.to_Z_extend_words.
  change (WL.get_word (WL.extend_words n) 0) with
    (Bar.get_word (Bar.extend_words n) 0).
  rewrite WL.get_extend_words_Z by lia.
  change (base WL.U64.width ^ Z.of_nat 0) with 1.
  ring.
Qed.

Lemma small_const_words_length : forall n c,
  length (Bar.small_const_words n c) = n.
Proof.
  intros n c.
  unfold Bar.small_const_words.
  rewrite WL.set_word_length, WL.extend_words_length.
  reflexivity.
Qed.

Lemma addc_words_small_const_exact : forall ws c,
  to_Z_words ws + to_Z c < modulus_words (length ws) ->
  to_Z_words
    (Bar.value_words
       (Bar.addc_words ws (Bar.small_const_words (length ws) c))) =
  to_Z_words ws + to_Z c.
Proof.
  intros ws c Hlt.
  rewrite addc_words_value_mod.
  rewrite small_const_words_length.
  replace (Nat.max (length ws) (length ws)) with (length ws) by lia.
  destruct (length ws) as [|n] eqn:Hlen.
  - rewrite WL.modulus_words_0 in Hlt.
    pose proof (WL.to_Z_words_bound ws) as Hws.
    rewrite Hlen, WL.modulus_words_0 in Hws.
    pose proof (spec_to_Z c) as Hc.
    assert (Hws0 : to_Z_words ws = 0) by lia.
    assert (Hc0 : to_Z c = 0) by lia.
    change (Bar.small_const_words 0 c) with ([] : Bar.words).
    change (to_Z_words []) with 0.
    rewrite WL.modulus_words_0.
    rewrite Hws0, Hc0. reflexivity.
  - rewrite small_const_words_value by lia.
    apply Z.mod_small.
    pose proof (WL.to_Z_words_bound ws) as Hws.
    pose proof (spec_to_Z c) as Hc.
    lia.
Qed.

Lemma bit_width_words_upper_bound : forall ws,
  to_Z_words ws < 2 ^ Z.of_nat (Bar.bit_width_words ws).
Proof.
  intro ws.
  unfold Bar.bit_width_words.
  destruct (Div.count_significant_words ws) as [|n] eqn:Hn.
  - pose proof (DP.count_significant_words_zero ws Hn) as Hz.
    rewrite Hz. reflexivity.
  - rewrite <- (DP.count_significant_words_preserves_value ws).
    rewrite Hn.
    pose proof (DP.count_significant_words_bound ws) as Hcsw_len.
    rewrite Hn in Hcsw_len.
    set (prefix := firstn (S n) ws).
    assert (Hprefix_len : length prefix = S n).
    { subst prefix. rewrite firstn_length_le by exact Hcsw_len.
      reflexivity. }
    pose proof (WL.to_Z_words_firstn_skipn prefix n ltac:(lia))
      as Hsplit.
    pose proof (WL.to_Z_words_bound (firstn n prefix)) as Hlow.
    rewrite firstn_length_le in Hlow by (rewrite Hprefix_len; lia).
    assert (Hskip : exists top, skipn n prefix = [top] /\
      top = Bar.get_word ws n).
    { destruct (skipn n prefix) as [|top rest] eqn:Hskip.
      - exfalso.
        assert (Hlen_skip : length (skipn n prefix) = 1%nat) by
          (rewrite length_skipn, Hprefix_len; lia).
        rewrite Hskip in Hlen_skip. cbn in Hlen_skip. lia.
      - destruct rest as [|r rest].
        + exists top. split; [reflexivity|].
          unfold Bar.get_word.
          pose proof (f_equal (fun xs => nth 0 xs Bar.U64.zero) Hskip)
            as Hnth.
          cbn [nth] in Hnth.
          rewrite nth_skipn in Hnth.
          subst prefix.
          rewrite nth_firstn in Hnth by lia.
          rewrite Nat.add_0_r in Hnth.
          replace (n <? S n)%nat with true in Hnth by
            (symmetry; apply Nat.ltb_lt; lia).
          cbn in Hnth.
          symmetry. exact Hnth.
        + exfalso.
          assert (Hlen_skip : length (skipn n prefix) = 1%nat) by
            (rewrite length_skipn, Hprefix_len; lia).
          rewrite Hskip in Hlen_skip. cbn in Hlen_skip. lia. }
    destruct Hskip as [top [Hskip Htop]].
    rewrite Hsplit, Hskip.
    cbn [to_Z_words].
    pose proof (DP.count_significant_words_msw_nonzero ws) as Hmsw.
    cbn zeta in Hmsw.
    rewrite Hn in Hmsw.
    specialize (Hmsw ltac:(lia)).
    replace (S n - 1)%nat with n in Hmsw by lia.
    change (WL.get_word ws n) with (Bar.get_word ws n) in Hmsw.
    rewrite Htop.
    pose proof (DP.countl_zero_upper top) as Htop_upper.
    rewrite <- Htop in Hmsw.
    pose proof (DP.countl_zero_bound top Hmsw) as Hcz.
    unfold Bar.bit_width_word, Bar.word_width.
    rewrite Bar.U64.width_is_64 in *.
    change (Pos.to_nat 64) with 64%nat in *.
    set (c := Div.countl_zero top) in *.
    rewrite <- Htop.
    rewrite Z.mul_0_r, Z.add_0_r.
    change (Div.countl_zero top) with c.
    assert (Hpow :
      modulus_words n * 2 ^ Z.of_nat (64 - c) =
      2 ^ Z.of_nat (64 * n + (64 - c))).
    { unfold modulus_words, base.
      rewrite Bar.U64.width_is_64.
      change (Z.pos 64) with 64.
      rewrite <- Z.pow_mul_r by lia.
      rewrite <- Z.pow_add_r by lia.
      f_equal. lia. }
    rewrite <- Hpow.
    pose proof (WL.modulus_words_pos n) as Hmod_pos.
    nia.
Qed.

Lemma max_denominator_value_upper_bound : forall params,
  to_Z_uint256 (Bar.max_denominator params) <
  2 ^ Z.of_nat (Bar.max_denominator_bits params).
Proof.
  intro params.
  unfold Bar.max_denominator_bits, Bar.bit_width_uint256, to_Z_uint256.
  apply bit_width_words_upper_bound.
Qed.

Lemma denominator_lt_max_denominator_bits : forall rec,
  reciprocal_admissible rec ->
  denominator_Z rec <
  2 ^ Z.of_nat (Bar.max_denominator_bits (Bar.reciprocal_params rec)).
Proof.
  intros rec Hadm.
  destruct Hadm as [_ [_ [_ [_ [_ [_ [Hden_max _]]]]]]].
  eapply Z.le_lt_trans; [exact Hden_max|].
  apply max_denominator_value_upper_bound.
Qed.

Lemma denominator_lt_modulus256 : forall rec,
  reciprocal_admissible rec ->
  denominator_Z rec < modulus_words 4%nat.
Proof.
  intros rec Hadm.
  destruct Hadm as [Hadm_params [_ [_ [_ [_ [_ [Hden_max _]]]]]]].
  eapply Z.le_lt_trans; [exact Hden_max|].
  unfold to_Z_uint256.
  pose proof (WL.to_Z_words_bound
    (Bar.uint256_to_words
       (Bar.max_denominator (Bar.reciprocal_params rec)))) as Hbound.
  rewrite uint256_to_words_length in Hbound.
  exact (proj2 Hbound).
Qed.

Lemma online_numerator_bound : forall rec x,
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  0 <= online_numerator_Z rec x <
  2 ^ Z.of_nat
    (Bar.input_bits (Bar.reciprocal_params rec) +
     Bar.multiplier_bits (Bar.reciprocal_params rec)).
Proof.
  intros rec x Hadm Hinput.
  rewrite online_numerator_value by exact Hadm.
  destruct Hinput as [Hx_nonneg Hx_lt].
  destruct Hadm as [_ [_ [_ [_ [Hscale_bound _]]]]].
  pose proof (reciprocal_scale_nonneg rec) as Hscale_nonneg.
  rewrite Nat2Z.inj_add, Z.pow_add_r by lia.
  split.
  - apply Z.mul_nonneg_nonneg; assumption.
  - pose proof (Z.pow_pos_nonneg 2
      (Z.of_nat (Bar.input_bits (Bar.reciprocal_params rec))) ltac:(lia))
      as HIpos.
    pose proof (Z.pow_pos_nonneg 2
      (Z.of_nat (Bar.multiplier_bits (Bar.reciprocal_params rec)))
      ltac:(lia)) as HMpos.
    nia.
Qed.

Lemma input_value_fit_input_words : forall rec x,
  let params := Bar.reciprocal_params rec in
  input_value_Z rec (Bar.fit_words (Bar.input_words params) x) =
  input_value_Z rec x.
Proof.
  intros rec x.
  unfold input_value_Z.
  rewrite fit_words_idempotent.
  reflexivity.
Qed.

Lemma input_within_bound_fit_input_words : forall rec x,
  input_within_bound rec x ->
  let params := Bar.reciprocal_params rec in
  input_within_bound rec (Bar.fit_words (Bar.input_words params) x).
Proof.
  intros rec x Hinput.
  unfold input_within_bound in *.
  rewrite input_value_fit_input_words.
  exact Hinput.
Qed.

Lemma online_numerator_fit_input_words : forall rec x,
  let params := Bar.reciprocal_params rec in
  online_numerator_Z rec (Bar.fit_words (Bar.input_words params) x) =
  online_numerator_Z rec x.
Proof.
  intros rec x.
  unfold online_numerator_Z, Bar.online_numerator.
  rewrite fit_words_idempotent.
  reflexivity.
Qed.

Lemma quotient_upper_bound : forall rec x,
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  online_numerator_Z rec x / denominator_Z rec <
  2 ^ Z.of_nat (Bar.max_quotient_bits (Bar.reciprocal_params rec)).
Proof.
  intros rec x Hadm Hinput.
  set (params := Bar.reciprocal_params rec).
  pose proof (online_numerator_bound rec x Hadm Hinput) as HN.
  destruct Hadm as [Hadm_params [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  destruct Hadm_params as [Hmin_pos [Hmin_le_max Hinput_pos]].
  assert (Hadm_params' : params_admissible params).
  { repeat split; assumption. }
  pose proof (min_denominator_bits_positive params Hadm_params') as HDpos.
  pose proof (min_denominator_value_lower_bound params Hadm_params')
    as Hmin_pow.
  assert (Hd_pos : 0 < denominator_Z rec) by lia.
  apply Z.div_lt_upper_bound; [exact Hd_pos|].
  destruct HN as [_ HN_lt].
  rewrite Nat2Z.inj_add, Z.pow_add_r in HN_lt by lia.
  unfold Bar.max_quotient_bits.
  fold params.
  set (I := Bar.input_bits params).
  set (M := Bar.multiplier_bits params).
  set (D := Bar.min_denominator_bits params).
  set (K := 2 ^ Z.of_nat (I + M - D + 1)).
  assert (Hscale :
    2 ^ Z.of_nat M * 2 ^ Z.of_nat I <=
    2 ^ Z.of_nat (D - 1) * K).
  { subst K I M D. apply pow_max_quotient_scale_bound. exact HDpos. }
  assert (Hden_pow : 2 ^ Z.of_nat (D - 1) <= denominator_Z rec).
  { subst D params. lia. }
  assert (Hpow_le :
    2 ^ Z.of_nat I * 2 ^ Z.of_nat M <= denominator_Z rec * K).
  { rewrite Z.mul_comm.
    eapply Z.le_trans; [exact Hscale|].
    apply Z.mul_le_mono_nonneg_r.
    - subst K. apply Z.pow_nonneg. lia.
    - exact Hden_pow. }
  eapply Z.lt_le_trans; [exact HN_lt|].
  subst K. exact Hpow_le.
Qed.

Lemma max_denominator_bits_positive : forall params,
  params_admissible params ->
  (0 < Bar.max_denominator_bits params)%nat.
Proof.
  intros params Hadm.
  destruct Hadm as [Hmin_pos [Hmin_le_max _]].
  pose proof (max_denominator_value_upper_bound params) as Hupper.
  destruct (Bar.max_denominator_bits params).
  - change (2 ^ Z.of_nat 0) with 1 in Hupper. lia.
  - lia.
Qed.

Lemma max_denominator_words_positive : forall params,
  params_admissible params ->
  (0 < Bar.max_denominator_words params)%nat.
Proof.
  intros params Hadm.
  unfold Bar.max_denominator_words.
  apply min_words_positive.
  now apply max_denominator_bits_positive.
Qed.

Lemma denominator_words_positive : forall rec,
  reciprocal_admissible rec ->
  (0 < length (Bar.denominator_ rec))%nat.
Proof.
  intros rec Hadm.
  destruct Hadm as [Hadm_params [_ [Hden_len _]]].
  rewrite Hden_len.
  apply max_denominator_words_positive.
  exact Hadm_params.
Qed.

Lemma max_r_hat_words_positive_admissible : forall params,
  params_admissible params ->
  (0 < Bar.max_r_hat_words params)%nat.
Proof.
  intros params Hadm.
  pose proof (max_denominator_bits_positive params Hadm) as Hmax_pos.
  apply min_words_positive.
  unfold Bar.max_r_hat_bits.
  destruct Hadm as [_ [_ Hinput_pos]].
  destruct (Nat.min_spec
    (Bar.input_bits params + Bar.multiplier_bits params)
    (Bar.max_denominator_bits params + 2)) as [[_ ->]|[_ ->]]; lia.
Qed.

Lemma estimate_q_true_length : forall rec x,
  length (Bar.estimate_q true rec x) =
  Bar.max_quotient_words (Bar.reciprocal_params rec).
Proof.
  intros rec x.
  unfold Bar.estimate_q.
  rewrite rshift_length.
  unfold Bar.max_quotient_words.
  replace
    (Bar.max_quotient_bits (Bar.reciprocal_params rec) +
       Bar.post_product_shift (Bar.reciprocal_params rec) -
       Bar.post_product_shift (Bar.reciprocal_params rec))%nat
    with (Bar.max_quotient_bits (Bar.reciprocal_params rec)) by lia.
  reflexivity.
Qed.

Lemma estimate_q_true_bound : forall rec x,
  0 <= estimate_q_Z true rec x <
  modulus_words (Bar.max_quotient_words (Bar.reciprocal_params rec)).
Proof.
  intros rec x.
  unfold estimate_q_Z.
  pose proof (WL.to_Z_words_bound (Bar.estimate_q true rec x)) as Hbound.
  rewrite estimate_q_true_length in Hbound.
  exact Hbound.
Qed.

Lemma estimate_q_sound_true : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  let Q := online_numerator_Z rec x / denominator_Z rec in
  Q - 2 <= estimate_q_Z true rec x <= Q.
Proof.
  intros rec x Hinv Hadm Hinput.
  destruct (Nat.eq_dec
    (Bar.pre_product_shift (Bar.reciprocal_params rec)) 0) as [Hpre|Hpre].
  - pose proof
      (estimate_q_sound_no_preshift rec x Hinv Hadm Hpre Hinput) as H.
    cbn zeta in H. lia.
  - assert (Hpre_pos :
      (0 < Bar.pre_product_shift (Bar.reciprocal_params rec))%nat) by lia.
    apply estimate_q_sound_with_preshift; assumption.
Qed.

Lemma truncating_mul_value_mod_positive_rhs : forall R xs ys,
  (0 < R)%nat ->
  (0 < length ys)%nat ->
  to_Z_words (Bar.truncating_mul R xs ys) =
  (to_Z_words xs * to_Z_words ys) mod modulus_words R.
Proof.
  intros R xs ys HR Hys.
  destruct xs as [|x xs].
  - rewrite truncating_mul_left_nil_value.
    cbn [to_Z_words].
    symmetry.
    apply Z.mod_0_l.
    pose proof (WL.modulus_words_pos R). lia.
  - unfold Bar.truncating_mul.
    pose proof (truncating_mul_runtime_correct_general
      (x :: xs) ys R ltac:(cbn; lia) Hys HR) as Hcorr.
    pose proof (RMP.truncating_mul_runtime_length (x :: xs) ys R HR)
      as Hlen.
    pose proof (WL.to_Z_words_bound
      (RMP.truncating_mul_runtime (x :: xs) ys R)) as Hbound.
    rewrite Hlen in Hbound.
    rewrite Z.mod_small in Hcorr by exact Hbound.
    exact Hcorr.
Qed.

Lemma q_times_denominator_low_value : forall rec q R,
  reciprocal_admissible rec ->
  (0 < R)%nat ->
  to_Z_words (Bar.truncating_mul R q (Bar.denominator_ rec)) =
  (to_Z_words q * denominator_Z rec) mod modulus_words R.
Proof.
  intros rec q R Hadm HR.
  unfold denominator_Z.
  apply truncating_mul_value_mod_positive_rhs.
  - exact HR.
  - now apply denominator_words_positive.
Qed.

Lemma copy_uint256_words_value_small : forall ws,
  to_Z_words ws < modulus_words 4%nat ->
  to_Z_words (Bar.copy_uint256_words ws) = to_Z_words ws.
Proof.
  intros ws Hsmall.
  unfold Bar.copy_uint256_words.
  apply to_Z_fit_words_small.
  exact Hsmall.
Qed.

Lemma to_Z_word_two :
  to_Z (Bar.U64.add Bar.U64.one Bar.U64.one) = 2.
Proof.
  rewrite spec_add, !spec_one.
  rewrite Z.mod_small.
  - reflexivity.
  - unfold base. rewrite width_is_64. cbn. lia.
Qed.

Lemma reduce_residual_bound : forall rec x q,
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  q <= online_numerator_Z rec x / denominator_Z rec ->
  online_numerator_Z rec x / denominator_Z rec - q <= 2 ->
  0 <= q ->
  0 <= online_numerator_Z rec x - q * denominator_Z rec <
  modulus_words (Bar.max_r_hat_words (Bar.reciprocal_params rec)).
Proof.
  intros rec x q Hadm Hinput Hq_le Hdelta_le Hq_nonneg.
  set (params := Bar.reciprocal_params rec).
  set (N := online_numerator_Z rec x).
  set (d := denominator_Z rec).
  set (Q := N / d).
  set (r := N mod d).
  assert (Hadm_rec : reciprocal_admissible rec) by exact Hadm.
  destruct Hadm as [Hadm_params [Hrec_len [Hden_len [Hmul_len
    [Hscale_bound [Hden_min [Hden_max Hmul_fit]]]]]]].
  assert (Hd_pos : 0 < d).
  { subst d. destruct Hadm_params as [Hmin_pos _]. lia. }
  pose proof (online_numerator_bound rec x Hadm_rec Hinput) as HN_bound.
  pose proof (denominator_lt_max_denominator_bits rec Hadm_rec) as Hd_bits.
  pose proof (Z.div_mod N d ltac:(subst d; lia)) as Hdivmod.
  pose proof (Z.mod_pos_bound N d ltac:(subst d; exact Hd_pos)) as Hr_bound.
  assert (Hres_eq :
    N - q * d = (Q - q) * d + r).
  { subst Q r. rewrite Hdivmod at 1. ring. }
  assert (Hdelta_bound : 0 <= Q - q <= 2) by (subst Q N d; lia).
  assert (Hres_nonneg : 0 <= N - q * d).
  { rewrite Hres_eq. nia. }
  assert (Hres_lt_input :
    N - q * d <
    2 ^ Z.of_nat (Bar.input_bits params + Bar.multiplier_bits params)).
  { destruct HN_bound as [_ HN_lt].
    eapply Z.le_lt_trans; [|exact HN_lt].
    subst N d. nia. }
  assert (Hres_lt_den :
    N - q * d <
    2 ^ Z.of_nat (Bar.max_denominator_bits params + 2)).
  { rewrite Hres_eq.
    replace (2 ^ Z.of_nat (Bar.max_denominator_bits params + 2)) with
      (4 * 2 ^ Z.of_nat (Bar.max_denominator_bits params)).
    2: {
      rewrite Nat2Z.inj_add.
      replace (Z.of_nat 2) with 2 by reflexivity.
      rewrite Z.pow_add_r by lia.
      change (2 ^ 2) with 4. ring. }
    change (Bar.max_denominator_bits params) with
      (Bar.max_denominator_bits (Bar.reciprocal_params rec)) in Hd_bits.
    change (denominator_Z rec) with d in Hd_bits.
    assert (Hd_lt_pow :
      d < 2 ^ Z.of_nat (Bar.max_denominator_bits params)).
    { subst params. exact Hd_bits. }
    assert (Hpow_pos :
      0 < 2 ^ Z.of_nat (Bar.max_denominator_bits params)).
    { apply Z.pow_pos_nonneg; lia. }
    assert (N - q * d < 3 * d) by (rewrite Hres_eq; nia).
    assert (3 * d <
      4 * 2 ^ Z.of_nat (Bar.max_denominator_bits params)) by nia.
    lia. }
  assert (Hres_lt_bits :
    N - q * d < 2 ^ Z.of_nat (Bar.max_r_hat_bits params)).
  { unfold Bar.max_r_hat_bits.
    destruct (Nat.min_spec
      (Bar.input_bits params + Bar.multiplier_bits params)
      (Bar.max_denominator_bits params + 2)) as [[_ ->]|[_ ->]];
      assumption. }
  split; [exact Hres_nonneg|].
  eapply Z.lt_le_trans; [exact Hres_lt_bits|].
  unfold Bar.max_r_hat_words.
  apply pow_le_modulus_min_words.
Qed.

Lemma reduce_initial_residual_value : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  let params := Bar.reciprocal_params rec in
  Bar.fit_words (Bar.input_words params) x = x ->
  let q_hat := Bar.estimate_q true rec x in
  let R := Bar.max_r_hat_words params in
  let qv := Bar.truncating_mul R q_hat (Bar.denominator_ rec) in
  let r_hat :=
    if Nat.eqb (Bar.multiplier_bits params) 0%nat
    then Bar.value_words (Bar.subb_truncating R x qv)
    else
      let xy := Bar.truncating_mul R x (Bar.multiplier_ rec) in
      Bar.value_words (Bar.subb_truncating R xy qv)
  in
  to_Z_words r_hat =
  online_numerator_Z rec x - to_Z_words q_hat * denominator_Z rec.
Proof.
  intros rec x Hinv Hadm Hinput.
  set (params := Bar.reciprocal_params rec).
  cbn zeta.
  intros Hfit.
  set (q_hat := Bar.estimate_q true rec x).
  set (q := to_Z_words q_hat).
  set (R := Bar.max_r_hat_words params).
  set (M := modulus_words R).
  set (d := denominator_Z rec).
  set (N := online_numerator_Z rec x).
  assert (Hadm_params : params_admissible params).
  { subst params. exact (proj1 Hadm). }
  assert (HR_pos : (0 < R)%nat).
  { subst R. apply max_r_hat_words_positive_admissible.
    exact Hadm_params. }
  assert (Hq_bounds : N / d - 2 <= q <= N / d).
  { subst q N d q_hat.
    apply estimate_q_sound_true; assumption. }
  assert (Hq_nonneg : 0 <= q).
  { subst q q_hat.
    destruct (estimate_q_true_bound rec x) as [H _].
    exact H. }
  assert (Hres_bound : 0 <= N - q * d < M).
  { subst M N d.
    apply reduce_residual_bound; try assumption; lia. }
  set (qv := Bar.truncating_mul R q_hat (Bar.denominator_ rec)).
  assert (Hqv : to_Z_words qv = (q * d) mod M).
  { subst qv q d M R. apply q_times_denominator_low_value;
      assumption. }
  cbn zeta.
  destruct (Nat.eqb (Bar.multiplier_bits params) 0%nat) eqn:Hbits.
  - apply Nat.eqb_eq in Hbits.
    pose proof (multiplier_words_zero params Hbits) as Hmwords.
    assert (HN_value : N = to_Z_words x).
    { subst N.
      unfold online_numerator_Z, Bar.online_numerator.
      fold params.
      rewrite Hmwords. cbn [Nat.eqb].
      rewrite Hfit. reflexivity. }
    rewrite subb_truncating_value_mod.
    rewrite Hqv.
    change (modulus_words R) with M.
    rewrite Zminus_mod_idemp_r.
    rewrite <- HN_value.
    rewrite Z.mod_small by exact Hres_bound.
    subst q d. reflexivity.
  - apply Nat.eqb_neq in Hbits.
    assert (Hbits_pos : (0 < Bar.multiplier_bits params)%nat) by lia.
    set (xy := Bar.truncating_mul R x (Bar.multiplier_ rec)).
    pose proof (low_input_product_sufficient rec x Hinv Hadm
      Hbits_pos Hinput) as Hxy_low.
    fold params in Hxy_low.
    assert (Hxy_mod : N mod M = to_Z_words xy mod M).
    { subst xy M R N.
      cbn zeta in Hxy_low.
      rewrite Hfit in Hxy_low.
      exact Hxy_low. }
    rewrite subb_truncating_value_mod.
    rewrite Hqv.
    change (modulus_words R) with M.
    rewrite Zminus_mod_idemp_r.
    rewrite <- Zminus_mod_idemp_l.
    rewrite <- Hxy_mod.
    rewrite Zminus_mod_idemp_l.
    rewrite Z.mod_small by exact Hres_bound.
    subst q d N. reflexivity.
Qed.

Theorem reduce_correct_remainder_only : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  let result := Bar.reduce false rec x in
  reduce_rem_Z result = Z.modulo (online_numerator_Z rec x) (denominator_Z rec) /\
  0 <= reduce_rem_Z result < denominator_Z rec.
Admitted.

Theorem reduce_correct_with_quotient : forall rec x,
  reciprocal_invariant rec ->
  reciprocal_admissible rec ->
  input_within_bound rec x ->
  let result := Bar.reduce true rec x in
  online_numerator_Z rec x =
    reduce_quot_Z result * denominator_Z rec + reduce_rem_Z result /\
  0 <= reduce_rem_Z result < denominator_Z rec.
Proof.
  intros rec x Hinv Hadm Hinput.
  set (params := Bar.reciprocal_params rec).
  set (x_words := Bar.fit_words (Bar.input_words params) x).
  set (q_hat := Bar.estimate_q true rec x_words).
  set (R := Bar.max_r_hat_words params).
  set (qv := Bar.truncating_mul R q_hat (Bar.denominator_ rec)).
  set (r_hat :=
    if Nat.eqb (Bar.multiplier_bits params) 0%nat
    then Bar.value_words (Bar.subb_truncating R x_words qv)
    else
      let xy := Bar.truncating_mul R x_words (Bar.multiplier_ rec) in
      Bar.value_words (Bar.subb_truncating R xy qv)).
  set (r_1 := Bar.subb_zx r_hat (Bar.denominator_ rec)).
  set (q_1 := Bar.value_words
    (Bar.addc_words q_hat
       (Bar.small_const_words (length q_hat) Bar.U64.one))).
  set (r_2 := Bar.subb_zx (Bar.value_words r_1) (Bar.denominator_ rec)).
  set (q_2 := Bar.value_words
    (Bar.addc_words q_hat
       (Bar.small_const_words (length q_hat)
          (Bar.U64.add Bar.U64.one Bar.U64.one)))).
  assert (Hinput_words : input_within_bound rec x_words) by
    (subst x_words params;
     apply input_within_bound_fit_input_words; exact Hinput).
  assert (Honline_words :
    online_numerator_Z rec x_words = online_numerator_Z rec x) by
    (subst x_words params; apply online_numerator_fit_input_words).
  unfold Bar.reduce.
  fold params x_words q_hat R qv r_hat r_1 q_1 r_2 q_2.
  cbn [reduce_quot_Z reduce_rem_Z Bar.reduce_quot Bar.reduce_rem].
  set (q := to_Z_words q_hat).
  set (d := denominator_Z rec).
  set (N := online_numerator_Z rec x_words).
  set (Q := N / d).
  set (rem := N mod d).
  assert (Hrhat_value : to_Z_words r_hat = N - q * d) by
    (subst r_hat qv R q q_hat d N params;
     apply reduce_initial_residual_value; try assumption;
     apply fit_words_idempotent).
  assert (Hd_pos : 0 < d) by (subst d; exact (proj1 Hinv)).
  assert (Hq_bounds : Q - 2 <= q <= Q) by
    (subst Q q d N q_hat; apply estimate_q_sound_true; assumption).
  assert (Hq_nonneg : 0 <= q) by
    (subst q; pose proof (WL.to_Z_words_bound q_hat); lia).
  assert (Hrem_bounds : 0 <= rem < d) by
    (subst rem; apply Z.mod_pos_bound; lia).
  assert (HN_div : N = Q * d + rem) by
    (subst Q rem; rewrite (Z.div_mod N d ltac:(lia)) at 1; ring).
  assert (Hres_decomp : N - q * d = (Q - q) * d + rem) by
    (rewrite HN_div; ring).
  assert (Hdelta_bounds : 0 <= Q - q <= 2) by lia.
  assert (Hden_lt256 : d < modulus_words 4%nat) by
    (subst d; apply denominator_lt_modulus256; exact Hadm).
  assert (Hquot_bound : Q < modulus_words (length q_hat)) by
    (subst Q N d q_hat;
     pose proof (quotient_upper_bound rec x_words Hadm Hinput_words) as HQ;
     rewrite estimate_q_true_length;
     eapply Z.lt_le_trans; [exact HQ|];
     unfold Bar.max_quotient_words;
     apply pow_le_modulus_min_words).
  destruct (Bar.carry_words r_1) eqn:Hr1_borrow.
  - assert (Hr1_cmp :=
      subb_zx_borrow_correct r_hat (Bar.denominator_ rec)).
    fold r_1 in Hr1_cmp.
    change (to_Z_words (Bar.denominator_ rec)) with d in Hr1_cmp.
    rewrite Hr1_borrow in Hr1_cmp.
    symmetry in Hr1_cmp.
    apply Z.ltb_lt in Hr1_cmp.
    rewrite Hrhat_value in Hr1_cmp.
    assert (Hdelta0 : Q - q = 0) by nia.
    assert (Hres_rem : N - q * d = rem) by nia.
    unfold reduce_quot_Z, reduce_rem_Z.
    cbn [Bar.reduce_quot Bar.reduce_rem Bar.quotient_output].
    rewrite copy_uint256_words_value_small.
    2: { rewrite Hrhat_value, Hres_rem. lia. }
    rewrite Hrhat_value, Hres_rem.
    rewrite <- Honline_words.
    change (online_numerator_Z rec x_words) with N.
    change (to_Z_words q_hat) with q.
    split; lia.
  - assert (Hr1_cmp :=
      subb_zx_borrow_correct r_hat (Bar.denominator_ rec)).
    fold r_1 in Hr1_cmp.
    change (to_Z_words (Bar.denominator_ rec)) with d in Hr1_cmp.
    rewrite Hr1_borrow in Hr1_cmp.
    symmetry in Hr1_cmp.
    apply Z.ltb_ge in Hr1_cmp.
    assert (Hr1_value :
      to_Z_words (Bar.value_words r_1) = N - q * d - d).
    { subst r_1.
      rewrite subb_zx_value_no_borrow.
      - change (to_Z_words (Bar.denominator_ rec)) with d.
        rewrite Hrhat_value. ring.
      - change (to_Z_words (Bar.denominator_ rec)) with d.
        exact Hr1_cmp. }
    rewrite Hrhat_value in Hr1_cmp.
    destruct (Nat.eqb (Bar.pre_product_shift params) 0%nat) eqn:Hpre.
    + apply Nat.eqb_eq in Hpre.
      assert (Hq_no : Q - 1 <= q <= Q).
      { subst Q q d N q_hat params.
        apply estimate_q_sound_no_preshift; assumption. }
      assert (Hdelta1 : Q - q = 1) by nia.
      assert (Hr1_rem : to_Z_words (Bar.value_words r_1) = rem) by nia.
      assert (Hq1_value : to_Z_words q_1 = q + 1).
      { subst q_1.
        rewrite addc_words_small_const_exact.
        - rewrite spec_one. change (to_Z_words q_hat) with q. ring.
        - rewrite spec_one. assert (q + 1 = Q) by lia. lia. }
      unfold reduce_quot_Z, reduce_rem_Z.
      cbn [Bar.reduce_quot Bar.reduce_rem Bar.quotient_output].
      rewrite copy_uint256_words_value_small.
      2: { rewrite Hr1_rem. lia. }
      rewrite Hq1_value, Hr1_rem.
      rewrite <- Honline_words.
      change (online_numerator_Z rec x_words) with N.
      split; lia.
    + destruct (negb (Bar.carry_words r_2)) eqn:Hr2_neg.
      * apply negb_true_iff in Hr2_neg.
        assert (Hr2_cmp := subb_zx_borrow_correct
          (Bar.value_words r_1) (Bar.denominator_ rec)).
        fold r_2 in Hr2_cmp.
        change (to_Z_words (Bar.denominator_ rec)) with d in Hr2_cmp.
        rewrite Hr2_neg in Hr2_cmp.
        symmetry in Hr2_cmp.
        apply Z.ltb_ge in Hr2_cmp.
        assert (Hr2_value :
          to_Z_words (Bar.value_words r_2) = N - q * d - d - d).
        { subst r_2.
          rewrite subb_zx_value_no_borrow.
          - change (to_Z_words (Bar.denominator_ rec)) with d.
            rewrite Hr1_value. ring.
          - change (to_Z_words (Bar.denominator_ rec)) with d.
            exact Hr2_cmp. }
        assert (Hdelta2 : Q - q = 2) by nia.
        assert (Hr2_rem : to_Z_words (Bar.value_words r_2) = rem)
          by nia.
        assert (Hq2_value : to_Z_words q_2 = q + 2).
        { subst q_2.
          rewrite addc_words_small_const_exact.
          - rewrite to_Z_word_two. change (to_Z_words q_hat) with q.
            ring.
          - rewrite to_Z_word_two. assert (q + 2 = Q) by lia. lia. }
        unfold reduce_quot_Z, reduce_rem_Z.
        cbn [Bar.reduce_quot Bar.reduce_rem Bar.quotient_output].
        rewrite copy_uint256_words_value_small.
        2: { rewrite Hr2_rem. lia. }
        rewrite Hq2_value, Hr2_rem.
        rewrite <- Honline_words.
        change (online_numerator_Z rec x_words) with N.
        split; lia.
      * apply negb_false_iff in Hr2_neg.
        assert (Hr2_cmp := subb_zx_borrow_correct
          (Bar.value_words r_1) (Bar.denominator_ rec)).
        fold r_2 in Hr2_cmp.
        change (to_Z_words (Bar.denominator_ rec)) with d in Hr2_cmp.
        rewrite Hr2_neg in Hr2_cmp.
        symmetry in Hr2_cmp.
        apply Z.ltb_lt in Hr2_cmp.
        rewrite Hr1_value in Hr2_cmp.
        assert (Hdelta1 : Q - q = 1) by nia.
        assert (Hr1_rem : to_Z_words (Bar.value_words r_1) = rem)
          by nia.
        assert (Hq1_value : to_Z_words q_1 = q + 1).
        { subst q_1.
          rewrite addc_words_small_const_exact.
          - rewrite spec_one. change (to_Z_words q_hat) with q. ring.
          - rewrite spec_one. assert (q + 1 = Q) by lia. lia. }
        unfold reduce_quot_Z, reduce_rem_Z.
        cbn [Bar.reduce_quot Bar.reduce_rem Bar.quotient_output].
        rewrite copy_uint256_words_value_small.
        2: { rewrite Hr1_rem. lia. }
        rewrite Hq1_value, Hr1_rem.
        rewrite <- Honline_words.
        change (online_numerator_Z rec x_words) with N.
        split; lia.
Qed.

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
Proof.
  intros params d u Hadm Hinput_bits Hmul_bits Hvalid.
  set (rec := Bar.reciprocal_of_denominator params d).
  pose proof (constructor_sound_no_multiplier params d Hadm Hmul_bits Hvalid)
    as [Hinv [Hden Hmul]].
  pose proof (reciprocal_of_denominator_admissible
    params d Hadm Hmul_bits Hvalid) as Hadm_rec.
  set (x := Bar.uint256_to_words u).
  assert (Hu_bound : 0 <= to_Z_uint256 u < 2 ^ Z.of_nat 256).
  { unfold to_Z_uint256.
    pose proof (WL.to_Z_words_bound (Bar.uint256_to_words u)) as Hu.
    rewrite uint256_to_words_length in Hu.
    unfold modulus_words, base in Hu.
    rewrite width_is_64 in Hu.
    cbn in Hu. exact Hu. }
  assert (Hu_fit4 : uint256_fits_words 4%nat u).
  { unfold uint256_fits_words, to_Z_uint256.
    pose proof (WL.to_Z_words_bound (Bar.uint256_to_words u)) as Hu.
    rewrite uint256_to_words_length in Hu.
    exact (proj2 Hu). }
  assert (Hinput : input_within_bound rec x).
  { unfold input_within_bound, input_value_Z.
    subst x rec.
    change (Bar.reciprocal_params (Bar.reciprocal_of_denominator params d))
      with params.
    unfold Bar.input_words, Bar.min_words, Bar.word_width.
    rewrite Hinput_bits, width_is_64.
    cbn.
    rewrite to_Z_fit_uint256_words_small by exact Hu_fit4.
    exact Hu_bound. }
  set (rr := Bar.reduce true rec x).
  pose proof (reduce_correct_with_quotient rec x Hinv Hadm_rec Hinput) as Hred.
  fold rr in Hred.
  unfold Bar.udivrem.
  fold x rr.
  cbn [Div.ud_quot Div.ud_rem].
  cbn zeta in Hred.
  destruct Hred as [Hdecomp Hrem_bounds].
  assert (Honline : online_numerator_Z rec x = to_Z_uint256 u).
  { subst x.
    unfold online_numerator_Z, Bar.online_numerator.
    change (Bar.reciprocal_params rec) with params.
    rewrite (multiplier_words_zero params Hmul_bits). cbn [Nat.eqb].
    unfold Bar.input_words, Bar.min_words, Bar.word_width.
    rewrite Hinput_bits, width_is_64. cbn.
    rewrite to_Z_fit_uint256_words_small by exact Hu_fit4.
    reflexivity. }
  assert (Hd_pos : 0 < denominator_Z rec).
  { change (reciprocal_invariant rec) in Hinv. exact (proj1 Hinv). }
  assert (Hden_lt : denominator_Z rec < modulus_words 4%nat).
  { apply denominator_lt_modulus256. exact Hadm_rec. }
  assert (Hrem_copy :
    to_Z_words (Bar.copy_uint256_words (Bar.reduce_rem rr)) =
    reduce_rem_Z rr).
  { unfold reduce_rem_Z. apply copy_uint256_words_value_small.
    change (to_Z_words (Bar.reduce_rem rr)) with (reduce_rem_Z rr).
    lia. }
  assert (Hquot_nonneg : 0 <= reduce_quot_Z rr).
  { unfold reduce_quot_Z.
    pose proof (WL.to_Z_words_bound (Bar.reduce_quot rr)); lia. }
  assert (Hquot_lt : reduce_quot_Z rr < modulus_words 4%nat).
  { rewrite Honline in Hdecomp.
    unfold uint256_fits_words in Hu_fit4.
    nia. }
  assert (Hquot_copy :
    to_Z_words (Bar.copy_uint256_words (Bar.reduce_quot rr)) =
    reduce_quot_Z rr).
  { unfold reduce_quot_Z. apply copy_uint256_words_value_small.
    exact Hquot_lt. }
  rewrite Hquot_copy, Hrem_copy.
  rewrite <- Honline.
  split; assumption.
Qed.

Theorem signed_wrapper_correct : forall params d x denominator_neg,
  params_admissible params ->
  Bar.input_bits params = 256%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  ~ (to_Z_signed_uint256 x = - sign_threshold256 /\
     denominator_neg = true /\
     denominator_Z rec = 1) ->
  let divisor := signed_divisor_Z denominator_neg rec in
  let result := Bar.sdivrem x denominator_neg rec in
  to_Z_signed_words (Div.ud_quot result) = Z.quot (to_Z_signed_uint256 x) divisor /\
  to_Z_signed_words (Div.ud_rem result) = Z.rem (to_Z_signed_uint256 x) divisor /\
  to_Z_signed_uint256 x =
    to_Z_signed_words (Div.ud_quot result) * divisor +
    to_Z_signed_words (Div.ud_rem result).
Proof.
  intros params d x denominator_neg Hadm Hinput_bits Hmul_bits Hvalid.
  set (rec := Bar.reciprocal_of_denominator params d).
  cbn zeta.
  intros Hno_overflow.
  pose proof (constructor_sound_no_multiplier params d Hadm Hmul_bits Hvalid)
    as [Hinv [Hden_value Hmul_value]].
  pose proof (reciprocal_of_denominator_admissible
    params d Hadm Hmul_bits Hvalid) as Hadm_rec.
  set (x_neg := Arith.is_negative x).
  set (x_abs := if x_neg then Arith.negate_uint256 x else x).
  set (ures := Bar.udivrem x_abs rec).
  pose proof (udivrem_correct params d x_abs Hadm Hinput_bits Hmul_bits
    Hvalid) as Hudiv.
  fold rec in Hudiv.
  fold ures in Hudiv.
  destruct Hudiv as [Hdiv Hrem].
  fold ures in Hdiv, Hrem.
  set (q := to_Z_words (Div.ud_quot ures)).
  set (r := to_Z_words (Div.ud_rem ures)).
  set (den := denominator_Z rec).
  fold q in Hdiv.
  fold r in Hdiv.
  fold den in Hdiv.
  fold r in Hrem.
  fold den in Hrem.
  assert (Hd_pos : 0 < den).
  { subst den. change (reciprocal_invariant rec) in Hinv.
    exact (proj1 Hinv). }
  assert (Hq_nonneg : 0 <= q).
  { subst q. pose proof (WL.to_Z_words_bound (Div.ud_quot ures)); lia. }
  assert (Hq_div : q = to_Z_uint256 x_abs / den).
  { apply Z.div_unique_pos with (r := r).
    - exact Hrem.
    - rewrite Hdiv. ring. }
  assert (Hr_mod : r = to_Z_uint256 x_abs mod den).
  { apply Z.mod_unique_pos with (q := q).
    - exact Hrem.
    - rewrite Hdiv. ring. }
  assert (Hq_quot_abs : q = to_Z_uint256 x_abs ÷ den).
  { rewrite Z.quot_div_nonneg by lia. exact Hq_div. }
  assert (Hr_rem_abs : r = Z.rem (to_Z_uint256 x_abs) den).
  { rewrite (proj2 (Zquotrem_Zdiv_eucl_pos (to_Z_uint256 x_abs) den
      ltac:(lia) ltac:(lia))).
    exact Hr_mod. }
  subst x_neg.
  destruct (Arith.is_negative x) eqn:Hxneg;
    destruct denominator_neg eqn:Hdenneg;
    subst x_abs;
    unfold Bar.sdivrem;
    rewrite Hxneg;
    change (Bar.reciprocal_of_denominator params d) with rec;
    fold ures;
    cbn [xorb Div.ud_quot Div.ud_rem signed_divisor_Z].
  - assert (Hsx : to_Z_signed_uint256 x =
        - to_Z_uint256 (Arith.negate_uint256 x)).
    { apply to_Z_signed_uint256_negative. exact Hxneg. }
    assert (Habs_bound :
      to_Z_uint256 (Arith.negate_uint256 x) <= sign_threshold256).
    { pose proof (to_Z_signed_uint256_bounds x). lia. }
    assert (Hq_le_thr : q <= sign_threshold256) by nia.
    assert (Hr_le_thr : r <= sign_threshold256) by nia.
    assert (Hq_lt_thr : q < sign_threshold256).
    { destruct (Z.eq_dec q sign_threshold256) as [Hqeq|Hqneq].
      - exfalso.
        pose proof modulus256_twice_sign_threshold.
        pose proof modulus256_pos.
        assert (Habs_eq :
          to_Z_uint256 (Arith.negate_uint256 x) = sign_threshold256) by nia.
        assert (Hden_eq : den = 1) by nia.
        apply Hno_overflow.
        split.
        + rewrite Hsx. lia.
        + split; [reflexivity|].
          change (denominator_Z rec) with den. exact Hden_eq.
      - lia. }
    assert (Hq_signed : to_Z_signed_words (Div.ud_quot ures) = q).
    { apply to_Z_signed_words_nonnegative.
      change (to_Z_words (Div.ud_quot ures)) with q. lia. }
    assert (Hr_signed :
      to_Z_signed_words (Arith.negate_words (Div.ud_rem ures)) = - r).
    { apply to_Z_signed_negate_words_nonpositive.
      change (to_Z_words (Div.ud_rem ures)) with r. lia. }
    rewrite Hq_signed, Hr_signed, Hsx.
    change (denominator_Z rec) with den.
    split.
    + rewrite Z.quot_opp_opp by lia. exact Hq_quot_abs.
    + split.
      * rewrite Z.rem_opp_opp by lia. rewrite <- Hr_rem_abs. reflexivity.
      * rewrite Hdiv. ring.
  - assert (Hsx : to_Z_signed_uint256 x =
        - to_Z_uint256 (Arith.negate_uint256 x)).
    { apply to_Z_signed_uint256_negative. exact Hxneg. }
    assert (Habs_bound :
      to_Z_uint256 (Arith.negate_uint256 x) <= sign_threshold256).
    { pose proof (to_Z_signed_uint256_bounds x). lia. }
    assert (Hq_le_thr : q <= sign_threshold256) by nia.
    assert (Hr_le_thr : r <= sign_threshold256) by nia.
    assert (Hq_signed :
      to_Z_signed_words (Arith.negate_words (Div.ud_quot ures)) = - q).
    { apply to_Z_signed_negate_words_nonpositive.
      change (to_Z_words (Div.ud_quot ures)) with q. lia. }
    assert (Hr_signed :
      to_Z_signed_words (Arith.negate_words (Div.ud_rem ures)) = - r).
    { apply to_Z_signed_negate_words_nonpositive.
      change (to_Z_words (Div.ud_rem ures)) with r. lia. }
    rewrite Hq_signed, Hr_signed, Hsx.
    change (denominator_Z rec) with den.
    split.
    + rewrite Z.quot_opp_l by lia. rewrite <- Hq_quot_abs. reflexivity.
    + split.
      * rewrite Z.rem_opp_l by lia. rewrite <- Hr_rem_abs. reflexivity.
      * rewrite Hdiv. ring.
  - assert (Hsx : to_Z_signed_uint256 x = to_Z_uint256 x).
    { apply to_Z_signed_uint256_nonnegative. exact Hxneg. }
    assert (Habs_bound : to_Z_uint256 x < sign_threshold256).
    { pose proof (to_Z_signed_uint256_bounds x). lia. }
    assert (Hq_lt_thr : q < sign_threshold256) by nia.
    assert (Hr_lt_thr : r < sign_threshold256) by nia.
    assert (Hq_signed :
      to_Z_signed_words (Arith.negate_words (Div.ud_quot ures)) = - q).
    { apply to_Z_signed_negate_words_nonpositive.
      change (to_Z_words (Div.ud_quot ures)) with q. lia. }
    assert (Hr_signed : to_Z_signed_words (Div.ud_rem ures) = r).
    { apply to_Z_signed_words_nonnegative.
      change (to_Z_words (Div.ud_rem ures)) with r. lia. }
    rewrite Hq_signed, Hr_signed, Hsx.
    change (denominator_Z rec) with den.
    split.
    + rewrite Z.quot_opp_r by lia. rewrite <- Hq_quot_abs. reflexivity.
    + split.
      * rewrite Z.rem_opp_r by lia. rewrite <- Hr_rem_abs. reflexivity.
      * rewrite Hdiv. ring.
  - assert (Hsx : to_Z_signed_uint256 x = to_Z_uint256 x).
    { apply to_Z_signed_uint256_nonnegative. exact Hxneg. }
    assert (Habs_bound : to_Z_uint256 x < sign_threshold256).
    { pose proof (to_Z_signed_uint256_bounds x). lia. }
    assert (Hq_lt_thr : q < sign_threshold256) by nia.
    assert (Hr_lt_thr : r < sign_threshold256) by nia.
    assert (Hq_signed : to_Z_signed_words (Div.ud_quot ures) = q).
    { apply to_Z_signed_words_nonnegative.
      change (to_Z_words (Div.ud_quot ures)) with q. lia. }
    assert (Hr_signed : to_Z_signed_words (Div.ud_rem ures) = r).
    { apply to_Z_signed_words_nonnegative.
      change (to_Z_words (Div.ud_rem ures)) with r. lia. }
    rewrite Hq_signed, Hr_signed, Hsx.
    change (denominator_Z rec) with den.
    split.
    + exact Hq_quot_abs.
    + split.
      * exact Hr_rem_abs.
      * exact Hdiv.
Qed.

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
  Bar.bit_shift params = 0%nat ->
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
