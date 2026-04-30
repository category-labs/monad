From Stdlib Require Import ZArith List.
From Uint256 Require Import UintZ Barrett.

Import ListNotations.
Open Scope Z_scope.

(** Executable checks for candidate Barrett semantic discrepancies.

    This file uses the executable [UintZ] stack rather than the abstract proof
    functors, so [vm_compute] evaluates the actual model definitions. *)

Module Bar := Barrett.MakeLegacy
  (UintZ.ZUint64)
  (UintZ.ZUint128)
  (UintZ.ZBridge).

Module RemainderOnlyQuotientTruncationAttempt.

Definition wzero := UintZ.ZUint64.zero.
Definition wone := UintZ.ZUint64.one.
Definition wall := UintZ.ZUint64.sub wzero wone.
Definition wtwo := UintZ.ZUint64.add wone wone.
Definition word_2_3 := UintZ.ZUint64.shl wone 3.
Definition word_2_4 := UintZ.ZUint64.shl wone 4.

(** This is the concrete instance documented in
    [docs/barrett-semantic-discrepancies.org]:

    - min_denominator = 2
    - max_denominator = 2^65 - 1
    - input_bits = 256
    - multiplier_bits = 0
    - d = 2
    - x = 2^68
*)
Definition params : Bar.BarrettParams :=
  Bar.mk_BarrettParams
    (Bar.mk_uint256 wtwo wzero wzero wzero)
    (Bar.mk_uint256 wall wone wzero wzero)
    256
    0.

Definition d : Bar.uint256 :=
  Bar.mk_uint256 wtwo wzero wzero wzero.

Definition x : Bar.words :=
  [wzero; word_2_4; wzero; wzero].

Definition rec : Bar.reciprocal :=
  Bar.reciprocal_of_denominator params d.

Definition q_false : Bar.words :=
  Bar.estimate_q false rec x.

Definition q_true : Bar.words :=
  Bar.estimate_q true rec x.

Definition R : nat :=
  Bar.max_r_hat_words params.

Definition prod_false : Bar.words :=
  Bar.truncating_mul R q_false (Bar.denominator_ rec).

Definition prod_true : Bar.words :=
  Bar.truncating_mul R q_true (Bar.denominator_ rec).

Example max_r_hat_words_is_two :
  R = 2%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example false_quotient_keeps_two_words :
  q_false = [wzero; word_2_3].
Proof.
  vm_compute. reflexivity.
Qed.

Example true_quotient_has_only_zero_trailing_words :
  q_true = [wzero; word_2_3; wzero; wzero].
Proof.
  vm_compute. reflexivity.
Qed.

Example quotient_words_differ_only_by_trailing_zeroes :
  q_false <> q_true.
Proof.
  vm_compute. discriminate.
Qed.

Example documented_products_are_equal :
  prod_false = prod_true.
Proof.
  vm_compute. reflexivity.
Qed.

Example documented_product_value :
  prod_false = [wzero; word_2_4] /\
  prod_true = [wzero; word_2_4].
Proof.
  vm_compute. split; reflexivity.
Qed.

End RemainderOnlyQuotientTruncationAttempt.

Module UnalignedPostProductShift.

Definition wzero := UintZ.ZUint64.zero.
Definition wone := UintZ.ZUint64.one.
Definition wtwo := UintZ.ZUint64.add wone wone.
Definition wthree := UintZ.ZUint64.add wtwo wone.
Definition word_2_34 := UintZ.ZUint64.shl wone 34.
Definition word_2_34_minus_1 := UintZ.ZUint64.sub word_2_34 wone.

(** A deliberately generic, non-exported parameter choice with
    [post_product_bit_shift <> 0].  It demonstrates why the generic theorem
    [low_product_sufficient] carries the word-alignment hypothesis. *)
Definition params : Bar.BarrettParams :=
  Bar.mk_BarrettParams
    (Bar.mk_uint256 wtwo wzero wzero wzero)
    (Bar.mk_uint256 wthree wzero wzero wzero)
    34
    0.

Definition d : Bar.uint256 :=
  Bar.mk_uint256 wtwo wzero wzero wzero.

Definition x : Bar.words :=
  [word_2_34_minus_1].

Definition rec : Bar.reciprocal :=
  Bar.reciprocal_of_denominator params d.

Definition R : nat :=
  Bar.max_r_hat_words params.

Definition prod_false : Bar.words :=
  Bar.truncating_mul R (Bar.estimate_q false rec x) (Bar.denominator_ rec).

Definition prod_true : Bar.words :=
  Bar.truncating_mul R (Bar.estimate_q true rec x) (Bar.denominator_ rec).

Example post_product_shift_is_not_word_aligned :
  Bar.post_product_bit_shift params = 33%nat.
Proof.
  vm_compute. reflexivity.
Qed.

Example unaligned_low_products_differ :
  prod_false <> prod_true.
Proof.
  vm_compute. discriminate.
Qed.

End UnalignedPostProductShift.
