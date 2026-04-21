From Stdlib Require Import ZArith Zquot Lia List Bool.
From Uint256 Require Import Uint Base Words WordsLemmas RuntimeMul Division Arithmetic Barrett.

Import ListNotations.

Module MakeProofs (B : Base.BaseProofSig) (U128 : Uint128)
  (Bridge : UintWiden B.U64 U128)
  (WL : WordsLemmas.WordsLemmasProofSig with Module U64 := B.U64)
  (Div : Division.DivisionProofSig(B)(U128)(Bridge))
  (RM : RuntimeMul.RuntimeMulProofSig with Module U64 := B.U64)
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM))
  (Bar : Barrett.BarrettSig(B)(U128)(Bridge)(Div)(RM)(Arith)).
Import B.U64.

Open Scope Z_scope.

Local Notation to_Z_words := WL.to_Z_words.
Local Notation modulus_words := WL.modulus_words.

Definition modulus256 : Z := modulus_words 4%nat.
Definition sign_threshold256 : Z := modulus256 / 2.

Definition to_Z_uint256 (x : Bar.uint256) : Z :=
  to_Z_words (Bar.uint256_to_words x).

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

Theorem constructor_sound_no_multiplier : forall params d,
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  reciprocal_invariant (Bar.reciprocal_of_denominator params d) /\
  denominator_Z (Bar.reciprocal_of_denominator params d) = to_Z_uint256 d /\
  multiplier_Z (Bar.reciprocal_of_denominator params d) = 0.
Admitted.

Theorem constructor_sound_with_multiplier : forall params y d,
  (0 < Bar.multiplier_bits params)%nat ->
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
  (257 <= Bar.input_bits params)%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  to_Z_uint256 (Bar.addmod x y rec) =
    Z.modulo (to_Z_uint256 x + to_Z_uint256 y) (denominator_Z rec).
Admitted.

Theorem mulmod_correct : forall params d x y,
  (512 <= Bar.input_bits params)%nat ->
  Bar.multiplier_bits params = 0%nat ->
  Bar.valid_denominator params d = true ->
  let rec := Bar.reciprocal_of_denominator params d in
  to_Z_uint256 (Bar.mulmod x y rec) =
    Z.modulo (to_Z_uint256 x * to_Z_uint256 y) (denominator_Z rec).
Admitted.

Theorem mulmod_const_correct : forall params y d x,
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
  (RM : RuntimeMul.RuntimeMulProofSig with Module U64 := B.U64)
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM))
  (Bar : Barrett.BarrettSig(B)(U128)(Bridge)(Div)(RM)(Arith)).
Include MakeProofs(B)(U128)(Bridge)(WL)(Div)(RM)(Arith)(Bar).
End BarrettProofsSig.
