From Uint256 Require Import UintZ Barrett.

(** Compile-time checks mirroring the C++ [static_assert]s for the exported
    Barrett reciprocal aliases. *)

Module Bar := Barrett.MakeLegacy
  (UintZ.ZUint64)
  (UintZ.ZUint128)
  (UintZ.ZBridge).

Ltac static_check := vm_compute; reflexivity.

Module Udivrem.

Example reciprocal_1_65_bits :
  Bar.reciprocal_bits Bar.udivrem_reciprocal_1_65 = 256%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_max_denominator_bits :
  Bar.max_denominator_bits Bar.udivrem_reciprocal_1_65 = 65%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.udivrem_reciprocal_1_65 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_bits :
  Bar.reciprocal_bits Bar.udivrem_reciprocal_65_129 = 192%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_max_denominator_bits :
  Bar.max_denominator_bits Bar.udivrem_reciprocal_65_129 = 129%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.udivrem_reciprocal_65_129 = 1%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_bits :
  Bar.reciprocal_bits Bar.udivrem_reciprocal_129_193 = 128%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_max_denominator_bits :
  Bar.max_denominator_bits Bar.udivrem_reciprocal_129_193 = 193%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.udivrem_reciprocal_129_193 = 2%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_bits :
  Bar.reciprocal_bits Bar.udivrem_reciprocal_193_256 = 64%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_max_denominator_bits :
  Bar.max_denominator_bits Bar.udivrem_reciprocal_193_256 = 256%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.udivrem_reciprocal_193_256 = 3%nat.
Proof. static_check. Qed.

Example reciprocal_bits :
  Bar.reciprocal_bits Bar.udivrem_reciprocal = 256%nat.
Proof. static_check. Qed.

Example reciprocal_max_denominator_bits :
  Bar.max_denominator_bits Bar.udivrem_reciprocal = 256%nat.
Proof. static_check. Qed.

Example reciprocal_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.udivrem_reciprocal = 0%nat.
Proof. static_check. Qed.

End Udivrem.

Module Addmod.

Example reciprocal_1_65_bits :
  Bar.reciprocal_bits Bar.addmod_reciprocal_1_65 = 257%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_max_denominator_bits :
  Bar.max_denominator_bits Bar.addmod_reciprocal_1_65 = 65%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.addmod_reciprocal_1_65 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.addmod_reciprocal_1_65 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_bits :
  Bar.reciprocal_bits Bar.addmod_reciprocal_65_129 = 193%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_max_denominator_bits :
  Bar.max_denominator_bits Bar.addmod_reciprocal_65_129 = 129%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.addmod_reciprocal_65_129 = 1%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.addmod_reciprocal_65_129 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_bits :
  Bar.reciprocal_bits Bar.addmod_reciprocal_129_193 = 129%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_max_denominator_bits :
  Bar.max_denominator_bits Bar.addmod_reciprocal_129_193 = 193%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.addmod_reciprocal_129_193 = 2%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.addmod_reciprocal_129_193 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_bits :
  Bar.reciprocal_bits Bar.addmod_reciprocal_193_256 = 65%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_max_denominator_bits :
  Bar.max_denominator_bits Bar.addmod_reciprocal_193_256 = 256%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.addmod_reciprocal_193_256 = 3%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.addmod_reciprocal_193_256 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_bits :
  Bar.reciprocal_bits Bar.addmod_reciprocal = 257%nat.
Proof. static_check. Qed.

Example reciprocal_max_denominator_bits :
  Bar.max_denominator_bits Bar.addmod_reciprocal = 256%nat.
Proof. static_check. Qed.

Example reciprocal_input_words :
  Bar.input_words Bar.addmod_reciprocal = 5%nat.
Proof. static_check. Qed.

Example reciprocal_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.addmod_reciprocal = 0%nat.
Proof. static_check. Qed.

End Addmod.

Module Mulmod.

Example reciprocal_1_65_bits :
  Bar.reciprocal_bits Bar.mulmod_reciprocal_1_65 = 512%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_reciprocal_1_65 = 65%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_reciprocal_1_65 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_bits :
  Bar.reciprocal_bits Bar.mulmod_reciprocal_65_129 = 448%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_reciprocal_65_129 = 129%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_reciprocal_65_129 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_bits :
  Bar.reciprocal_bits Bar.mulmod_reciprocal_129_193 = 384%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_reciprocal_129_193 = 193%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_reciprocal_129_193 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_bits :
  Bar.reciprocal_bits Bar.mulmod_reciprocal_193_256 = 320%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_reciprocal_193_256 = 256%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_reciprocal_193_256 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_bits :
  Bar.reciprocal_bits Bar.mulmod_reciprocal = 512%nat.
Proof. static_check. Qed.

Example reciprocal_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_reciprocal = 256%nat.
Proof. static_check. Qed.

Example reciprocal_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.mulmod_reciprocal = 0%nat.
Proof. static_check. Qed.

Example reciprocal_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_reciprocal = 0%nat.
Proof. static_check. Qed.

End Mulmod.

Module MulmodConst.

Example reciprocal_1_65_bits :
  Bar.reciprocal_bits Bar.mulmod_const_reciprocal_1_65 = 511%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_const_reciprocal_1_65 = 65%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_bit_shift :
  Bar.bit_shift Bar.mulmod_const_reciprocal_1_65 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_1_65_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_const_reciprocal_1_65 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_bits :
  Bar.reciprocal_bits Bar.mulmod_const_reciprocal_65_129 = 447%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_const_reciprocal_65_129 = 129%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_bit_shift :
  Bar.bit_shift Bar.mulmod_const_reciprocal_65_129 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_65_129_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_const_reciprocal_65_129 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_bits :
  Bar.reciprocal_bits Bar.mulmod_const_reciprocal_129_193 = 383%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_const_reciprocal_129_193 = 193%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_bit_shift :
  Bar.bit_shift Bar.mulmod_const_reciprocal_129_193 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_129_193_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_const_reciprocal_129_193 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_bits :
  Bar.reciprocal_bits Bar.mulmod_const_reciprocal_193_256 = 319%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_const_reciprocal_193_256 = 256%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_bit_shift :
  Bar.bit_shift Bar.mulmod_const_reciprocal_193_256 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_193_256_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_const_reciprocal_193_256 = 0%nat.
Proof. static_check. Qed.

Example reciprocal_bits :
  Bar.reciprocal_bits Bar.mulmod_const_reciprocal = 511%nat.
Proof. static_check. Qed.

Example reciprocal_max_denominator_bits :
  Bar.max_denominator_bits Bar.mulmod_const_reciprocal = 256%nat.
Proof. static_check. Qed.

Example reciprocal_pre_product_word_shift :
  Bar.pre_product_word_shift Bar.mulmod_const_reciprocal = 0%nat.
Proof. static_check. Qed.

Example reciprocal_bit_shift :
  Bar.bit_shift Bar.mulmod_const_reciprocal = 0%nat.
Proof. static_check. Qed.

Example reciprocal_post_product_bit_shift :
  Bar.post_product_bit_shift Bar.mulmod_const_reciprocal = 0%nat.
Proof. static_check. Qed.

End MulmodConst.
