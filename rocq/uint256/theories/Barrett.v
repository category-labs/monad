From Stdlib Require Import List Bool PeanoNat Lia PArith.
From Uint256 Require Import Uint Base Words RuntimeMul Division Arithmetic.
Import ListNotations.

Module Make (B : Base.BaseSig) (U128 : Uint128Ops)
  (Bridge : UintWidenOps B.U64 U128)
  (Div : Division.DivisionSig(B)(U128)(Bridge))
  (RM : RuntimeMul.RuntimeMulSig with Module U64 := B.U64)
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM)).
Include B.
Import U64.
Include UintNotations(U64).

Open Scope uint_scope.

Definition uint256_num_words : nat := 4%nat.
Definition word_width : nat := Pos.to_nat U64.width.

Record BarrettParams := mk_BarrettParams {
  min_denominator : uint256;
  max_denominator : uint256;
  input_bits : nat;
  multiplier_bits : nat
}.

Record reciprocal := mk_reciprocal {
  reciprocal_params : BarrettParams;
  reciprocal_ : words;
  denominator_ : words;
  multiplier_ : words
}.

Record words_with_carry := mk_words_with_carry {
  value_words : words;
  carry_words : bool
}.

Record reduce_result := mk_reduce_result {
  reduce_quot : words;
  reduce_rem : words
}.

Fixpoint of_nat_word (n : nat) : t :=
  match n with
  | O => 0
  | S n' => of_nat_word n' + 1
  end.

Definition uint256_of_nat (n : nat) : uint256 :=
  mk_uint256 (of_nat_word n) 0 0 0.

Definition min_words (bits : nat) : nat :=
  Nat.div (bits + Nat.pred word_width) word_width.

Definition bit_width_word (x : t) : nat :=
  (word_width - Div.countl_zero x)%nat.

Definition bit_width_words (ws : words) : nat :=
  let n := Div.count_significant_words ws in
  match n with
  | O => O
  | S n' => (word_width * n' + bit_width_word (get_word ws n'))%nat
  end.

Definition bit_width_uint256 (x : uint256) : nat :=
  bit_width_words (uint256_to_words x).

Definition leb_uint256 (x y : uint256) : bool :=
  negb (Arith.ltb_uint256 y x).

Definition valid_denominator (params : BarrettParams) (d : uint256) : bool :=
  (leb_uint256 (min_denominator params) d &&
   leb_uint256 d (max_denominator params))%bool.

Definition params_well_formed (params : BarrettParams) : Prop :=
  Arith.ltb_uint256 zero_uint256 (min_denominator params) = true /\
  leb_uint256 (min_denominator params) (max_denominator params) = true /\
  (0 < input_bits params)%nat.

Definition min_denominator_bits (params : BarrettParams) : nat :=
  bit_width_uint256 (min_denominator params).

Definition max_denominator_bits (params : BarrettParams) : nat :=
  bit_width_uint256 (max_denominator params).

Definition max_denominator_words (params : BarrettParams) : nat :=
  min_words (max_denominator_bits params).

Definition input_words (params : BarrettParams) : nat :=
  min_words (input_bits params).

Definition multiplier_words (params : BarrettParams) : nat :=
  min_words (multiplier_bits params).

Definition max_quotient_bits (params : BarrettParams) : nat :=
  (input_bits params + multiplier_bits params - min_denominator_bits params + 1)%nat.

Definition max_quotient_words (params : BarrettParams) : nat :=
  min_words (max_quotient_bits params).

Definition shift (params : BarrettParams) : nat :=
  input_bits params.

Definition word_shift (params : BarrettParams) : nat :=
  Nat.div (shift params) word_width.

Definition bit_shift (params : BarrettParams) : nat :=
  Nat.modulo (shift params) word_width.

Definition numerator_words (params : BarrettParams) : nat :=
  if Nat.eqb (multiplier_words params) 0%nat
  then S (word_shift params)
  else min_words (word_width * multiplier_words params + input_bits params).

Definition quotient_words_for (params : BarrettParams) (need_quotient : bool) : nat :=
  if need_quotient
  then max_quotient_words params
  else min_words (Nat.min (max_quotient_bits params)
                     (Nat.min (input_bits params + multiplier_bits params)
                        (max_denominator_bits params + 2))).

Definition max_r_hat_bits (params : BarrettParams) : nat :=
  Nat.min (input_bits params + multiplier_bits params)
          (max_denominator_bits params + 2).

Definition max_r_hat_words (params : BarrettParams) : nat :=
  min_words (max_r_hat_bits params).

Definition relevant_quotient_bits (params : BarrettParams) : nat :=
  Nat.min (max_quotient_bits params) (max_r_hat_bits params).

Definition relevant_quotient_words (params : BarrettParams) : nat :=
  min_words (relevant_quotient_bits params).

Definition all_ones_words (n : nat) : words :=
  repeat (0 - 1) n.

Definition small_const_words (n : nat) (c : t) : words :=
  set_word (extend_words n) 0 c.

Definition bounded_segment (total start : nat) (seg : words) : words :=
  Div.set_segment (extend_words total) start (firstn (total - start) seg).

Definition numerator (params : BarrettParams) : words :=
  set_word (extend_words (numerator_words params))
           (word_shift params) (shl 1 (bit_shift params)).

Definition numerator_with_multiplier (params : BarrettParams) (y : words) : words :=
  let y_words := fit_words (multiplier_words params) y in
  let shifted :=
    if Nat.eqb (bit_shift params) 0
    then y_words
    else Div.shift_left_words y_words (bit_shift params)
  in
  bounded_segment (numerator_words params) (word_shift params) shifted.

Definition reciprocal_bits (params : BarrettParams) : nat :=
  let max_q :=
    if Nat.eqb (multiplier_words params) 0
    then
      match Div.udivrem (numerator_words params) uint256_num_words
              (numerator params) (uint256_to_words (min_denominator params)) with
      | Some r => Div.ud_quot r
      | None => extend_words (numerator_words params)
      end
    else
      match Div.udivrem (numerator_words params) uint256_num_words
              (numerator_with_multiplier params
                 (all_ones_words (multiplier_words params)))
              (uint256_to_words (min_denominator params)) with
      | Some r => Div.ud_quot r
      | None => extend_words (numerator_words params)
      end
  in
  bit_width_words max_q.

Definition reciprocal_words (params : BarrettParams) : nat :=
  min_words (reciprocal_bits params).

Definition pre_product_shift (params : BarrettParams) : nat :=
  if Nat.eqb (multiplier_bits params) 0%nat
  then
    let max_pre := Nat.pred (min_denominator_bits params) in
    let max_pre_mod := Nat.modulo max_pre word_width in
    let shift_mod := bit_shift params in
    if Nat.leb max_pre_mod shift_mod
    then max_pre
    else (max_pre - (max_pre_mod - shift_mod))%nat
  else 0%nat.

Definition pre_product_word_shift (params : BarrettParams) : nat :=
  Nat.div (pre_product_shift params) word_width.

Definition pre_product_bit_shift (params : BarrettParams) : nat :=
  Nat.modulo (pre_product_shift params) word_width.

Definition post_product_shift (params : BarrettParams) : nat :=
  (shift params - pre_product_shift params)%nat.

Definition post_product_word_shift (params : BarrettParams) : nat :=
  Nat.div (post_product_shift params) word_width.

Definition post_product_bit_shift (params : BarrettParams) : nat :=
  Nat.modulo (post_product_shift params) word_width.

Fixpoint rshift_aux (bit_shift0 word_shift0 i remaining : nat) (input : words)
    : words :=
  match remaining with
  | O => []
  | S remaining' =>
      let lo := get_word input (i + word_shift0) in
      let wi :=
        if Nat.eqb bit_shift0 0
        then lo
        else shrd64 (get_word input (i + S word_shift0)) lo bit_shift0
      in
      wi :: rshift_aux bit_shift0 word_shift0 (S i) remaining' input
  end.

Definition rshift (input_bits0 shift0 : nat) (input : words) : words :=
  let result_words := min_words (input_bits0 - shift0) in
  let input_words0 := min_words input_bits0 in
  rshift_aux (Nat.modulo shift0 word_width) (Nat.div shift0 word_width)
             0 result_words (fit_words input_words0 input).

Definition truncating_mul (R : nat) (xs ys : words) : words :=
  RM.truncating_mul_runtime xs ys R.

Definition wide_mul (xs ys : words) : words :=
  truncating_mul (length xs + length ys) xs ys.

Fixpoint subb_words_aux (R i : nat) (lhs rhs : words) (borrow : bool)
    : words * bool :=
  match R with
  | O => ([], borrow)
  | S R' =>
      let step := subb64 (get_word lhs i) (get_word rhs i) borrow in
      let '(rest, borrow') :=
        subb_words_aux R' (S i) lhs rhs (carry64 step)
      in
      (value64 step :: rest, borrow')
  end.

Definition subb_truncating (R : nat) (lhs rhs : words) : words_with_carry :=
  let '(result, borrow) := subb_words_aux R 0 lhs rhs false in
  mk_words_with_carry result borrow.

Definition subb_zx (lhs rhs : words) : words_with_carry :=
  let R := Nat.max (length lhs) (length rhs) in
  subb_truncating R lhs rhs.

Fixpoint addc_words_aux (R i : nat) (lhs rhs : words) (carry : bool)
    : words * bool :=
  match R with
  | O => ([], carry)
  | S R' =>
      let step := addc64 (get_word lhs i) (get_word rhs i) carry in
      let '(rest, carry') :=
        addc_words_aux R' (S i) lhs rhs (carry64 step)
      in
      (value64 step :: rest, carry')
  end.

Definition addc_words (lhs rhs : words) : words_with_carry :=
  let R := Nat.max (length lhs) (length rhs) in
  let '(result, carry) := addc_words_aux R 0 lhs rhs false in
  mk_words_with_carry result carry.

Definition copy_uint256_words (src : words) : words :=
  fit_words uint256_num_words src.

Definition quotient_output (need_quotient : bool) (quot : words) : words :=
  if need_quotient then quot else [].

Definition reciprocal_of_denominator (params : BarrettParams) (d : uint256)
    : reciprocal :=
  let quot :=
    match Div.udivrem (numerator_words params) uint256_num_words
            (numerator params) (uint256_to_words d) with
    | Some r => Div.ud_quot r
    | None => extend_words (numerator_words params)
    end
  in
  mk_reciprocal params
    (fit_words (reciprocal_words params) quot)
    (fit_words (max_denominator_words params) (uint256_to_words d))
    (extend_words (multiplier_words params)).

Definition reciprocal_of_multiplier (params : BarrettParams)
    (y d : uint256) : reciprocal :=
  let quot :=
    match Div.udivrem (numerator_words params) uint256_num_words
            (numerator_with_multiplier params (uint256_to_words y))
            (uint256_to_words d) with
    | Some r => Div.ud_quot r
    | None => extend_words (numerator_words params)
    end
  in
  mk_reciprocal params
    (fit_words (reciprocal_words params) quot)
    (fit_words (max_denominator_words params) (uint256_to_words d))
    (fit_words (multiplier_words params) (uint256_to_words y)).

Definition online_numerator (rec : reciprocal) (x : words) : words :=
  let params := reciprocal_params rec in
  let x_words := fit_words (input_words params) x in
  if Nat.eqb (multiplier_words params) 0
  then x_words
  else wide_mul x_words (multiplier_ rec).

Definition estimate_q (need_quotient : bool) (rec : reciprocal) (x : words)
    : words :=
  let params := reciprocal_params rec in
  let x_shift := rshift (input_bits params) (pre_product_shift params) x in
  let prod_bits :=
    Nat.add
      (if need_quotient
       then max_quotient_bits params
       else relevant_quotient_bits params)
      (post_product_shift params) in
  let prod_words := min_words prod_bits in
  let prod := truncating_mul prod_words x_shift (reciprocal_ rec) in
  rshift prod_bits (post_product_shift params) prod.

Definition reduce (need_quotient : bool) (rec : reciprocal) (x : words)
    : reduce_result :=
  let params := reciprocal_params rec in
  let x_words := fit_words (input_words params) x in
  let q_hat := estimate_q need_quotient rec x_words in
  let qv := truncating_mul (max_r_hat_words params) q_hat (denominator_ rec) in
  let r_hat :=
    if Nat.eqb (multiplier_bits params) 0
    then value_words (subb_truncating (max_r_hat_words params) x_words qv)
    else
      let xy := truncating_mul (max_r_hat_words params) x_words (multiplier_ rec) in
      value_words (subb_truncating (max_r_hat_words params) xy qv)
  in
  let r_1 := subb_zx r_hat (denominator_ rec) in
  if carry_words r_1 then
    mk_reduce_result
      (quotient_output need_quotient q_hat)
      (copy_uint256_words r_hat)
  else if Nat.eqb (pre_product_shift params) 0 then
    let q_1 :=
      value_words
        (addc_words q_hat
           (small_const_words (length q_hat) 1))
    in
    mk_reduce_result
      (quotient_output need_quotient q_1)
      (copy_uint256_words (value_words r_1))
  else
    let r_2 := subb_zx (value_words r_1) (denominator_ rec) in
    if negb (carry_words r_2) then
      let q_2 :=
        value_words
          (addc_words q_hat
             (small_const_words (length q_hat) (1 + 1)))
      in
      mk_reduce_result
        (quotient_output need_quotient q_2)
        (copy_uint256_words (value_words r_2))
    else
      let q_1 :=
        value_words
          (addc_words q_hat
             (small_const_words (length q_hat) 1))
      in
      mk_reduce_result
        (quotient_output need_quotient q_1)
        (copy_uint256_words (value_words r_1)).

Definition reciprocal_for_range (min_bits cutoff_bits input_bits0
    multiplier_bits0 : nat) : BarrettParams :=
  mk_BarrettParams
    (Arith.shift_left_uint256 Arith.one_uint256 (uint256_of_nat min_bits))
    (Arith.value256
       (Arith.subb
          (Arith.shift_left_uint256 Arith.one_uint256
             (uint256_of_nat cutoff_bits))
          Arith.one_uint256))
    input_bits0
    multiplier_bits0.

Definition reciprocal_interval_0 : nat := 65%nat.
Definition reciprocal_interval_1 : nat := 129%nat.
Definition reciprocal_interval_2 : nat := 193%nat.

Definition udivrem_reciprocal_for_range (min_bits cutoff_bits : nat)
    : BarrettParams :=
  reciprocal_for_range min_bits cutoff_bits 256%nat 0%nat.

Definition udivrem_reciprocal_1_65 : BarrettParams :=
  udivrem_reciprocal_for_range 1 reciprocal_interval_0.
Definition udivrem_reciprocal_65_129 : BarrettParams :=
  udivrem_reciprocal_for_range reciprocal_interval_0 reciprocal_interval_1.
Definition udivrem_reciprocal_129_193 : BarrettParams :=
  udivrem_reciprocal_for_range reciprocal_interval_1 reciprocal_interval_2.
Definition udivrem_reciprocal_193_256 : BarrettParams :=
  udivrem_reciprocal_for_range reciprocal_interval_2 256.
Definition udivrem_reciprocal : BarrettParams :=
  udivrem_reciprocal_for_range 1 256.

Definition addmod_reciprocal_for_range (min_bits cutoff_bits : nat)
    : BarrettParams :=
  reciprocal_for_range min_bits cutoff_bits 257%nat 0%nat.

Definition addmod_reciprocal_1_65 : BarrettParams :=
  addmod_reciprocal_for_range 1 reciprocal_interval_0.
Definition addmod_reciprocal_65_129 : BarrettParams :=
  addmod_reciprocal_for_range reciprocal_interval_0 reciprocal_interval_1.
Definition addmod_reciprocal_129_193 : BarrettParams :=
  addmod_reciprocal_for_range reciprocal_interval_1 reciprocal_interval_2.
Definition addmod_reciprocal_193_256 : BarrettParams :=
  addmod_reciprocal_for_range reciprocal_interval_2 256.
Definition addmod_reciprocal : BarrettParams :=
  addmod_reciprocal_for_range 1 256.

Definition mulmod_reciprocal_for_range (min_bits cutoff_bits : nat)
    : BarrettParams :=
  reciprocal_for_range min_bits cutoff_bits 512%nat 0%nat.

Definition mulmod_reciprocal_1_65 : BarrettParams :=
  mulmod_reciprocal_for_range 1 reciprocal_interval_0.
Definition mulmod_reciprocal_65_129 : BarrettParams :=
  mulmod_reciprocal_for_range reciprocal_interval_0 reciprocal_interval_1.
Definition mulmod_reciprocal_129_193 : BarrettParams :=
  mulmod_reciprocal_for_range reciprocal_interval_1 reciprocal_interval_2.
Definition mulmod_reciprocal_193_256 : BarrettParams :=
  mulmod_reciprocal_for_range reciprocal_interval_2 256.
Definition mulmod_reciprocal : BarrettParams :=
  mulmod_reciprocal_for_range 1 256.

Definition mulmod_const_reciprocal_for_range (min_bits cutoff_bits : nat)
    : BarrettParams :=
  reciprocal_for_range min_bits cutoff_bits 256%nat 256%nat.

Definition mulmod_const_reciprocal_1_65 : BarrettParams :=
  mulmod_const_reciprocal_for_range 1 reciprocal_interval_0.
Definition mulmod_const_reciprocal_65_129 : BarrettParams :=
  mulmod_const_reciprocal_for_range reciprocal_interval_0 reciprocal_interval_1.
Definition mulmod_const_reciprocal_129_193 : BarrettParams :=
  mulmod_const_reciprocal_for_range reciprocal_interval_1 reciprocal_interval_2.
Definition mulmod_const_reciprocal_193_256 : BarrettParams :=
  mulmod_const_reciprocal_for_range reciprocal_interval_2 256.
Definition mulmod_const_reciprocal : BarrettParams :=
  mulmod_const_reciprocal_for_range 1 256.

Definition udivrem (u : uint256) (rec : reciprocal) : Div.udivrem_result :=
  let result := reduce true rec (uint256_to_words u) in
  Div.mk_udivrem_result
    (copy_uint256_words (reduce_quot result))
    (copy_uint256_words (reduce_rem result)).

Definition sdivrem (x : uint256) (denominator_neg : bool) (rec : reciprocal)
    : Div.udivrem_result :=
  let x_neg := Arith.is_negative x in
  let x_abs := if x_neg then Arith.negate_uint256 x else x in
  let quot_neg := xorb x_neg denominator_neg in
  let result := udivrem x_abs rec in
  Div.mk_udivrem_result
    (if quot_neg then Arith.negate_words (Div.ud_quot result)
     else Div.ud_quot result)
    (if x_neg then Arith.negate_words (Div.ud_rem result)
     else Div.ud_rem result).

Definition addmod (x y : uint256) (rec : reciprocal) : uint256 :=
  let sum_result := Arith.addc x y in
  let sum :=
    uint256_to_words (Arith.value256 sum_result)
    ++ [of_bool (Arith.carry256 sum_result)]
  in
  words_to_uint256 (reduce_rem (reduce false rec sum)).

Definition mulmod (x y : uint256) (rec : reciprocal) : uint256 :=
  let xy := wide_mul (uint256_to_words x) (uint256_to_words y) in
  words_to_uint256 (reduce_rem (reduce false rec xy)).

Definition mulmod_const (x : uint256) (rec : reciprocal) : uint256 :=
  words_to_uint256 (reduce_rem (reduce false rec (uint256_to_words x))).

End Make.

Module Type BarrettSig (B : Base.BaseSig) (U128 : Uint128Ops)
  (Bridge : UintWidenOps B.U64 U128)
  (Div : Division.DivisionSig(B)(U128)(Bridge))
  (RM : RuntimeMul.RuntimeMulSig with Module U64 := B.U64)
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM)).
Include Make(B)(U128)(Bridge)(Div)(RM)(Arith).
End BarrettSig.

Module MakeLegacy (Word64 : Uint64Ops) (U128 : Uint128Ops)
  (Bridge : UintWidenOps Word64 U128).
Module B := Base.Make(Word64).
Module Div := Division.Make(B)(U128)(Bridge).
Module RM := RuntimeMul.Make(B).
Module Arith := Arithmetic.Make(B)(U128)(Bridge)(Div)(RM).
Include Make(B)(U128)(Bridge)(Div)(RM)(Arith).
End MakeLegacy.

Module MakeOn := Make.
