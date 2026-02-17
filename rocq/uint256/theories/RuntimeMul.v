(** * Runtime Multiplication Model

    Models the C++ truncating_mul_runtime function which uses inline
    assembly primitives (mulx, adc_2, adc_3) for performance.
    This is the interpreter's runtime multiplication path, used for
    MULMOD, EXP, and decimal string parsing.

    This file contains only definitions. Proofs will be in RuntimeMulProofs.v.

    The runtime multiplication differs from the constexpr version:
    - Uses mul_line for the first row (no accumulation)
    - Uses mul_add_line for subsequent rows (multiply-accumulate)
    - mul_add_line uses a 2-word carry (c_hi, c_lo) for efficiency
    - All loop unrolling is done at compile time via template recursion

    We axiomatize three inline assembly primitives (mulx, adc_2, adc_3)
    and model everything else structurally.

    C++ reference: uint256.hpp, lines 750-985
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives Words.
Import ListNotations.
Open Scope Z_scope.

(** ** Axiomatized Inline Assembly Primitives *)

(** Note: mulx is already defined as mulx64 in Primitives.v.
    The runtime mulx_intrinsic (BMI2 MULX instruction) produces
    the same result as mulx_constexpr. We reuse the existing definition. *)

(** *** adc_2: 2-word add-with-carry *)

(** Overload 1: adc_2(x_1, x_0, y_0, r_1, r_0)
    Assembly: addq y_0, x_0; adcq $0, x_1
    Computes: (r_1, r_0) where r_1 * 2^64 + r_0 = x_1 * 2^64 + x_0 + y_0

    Note: the result is the exact 128-bit sum (no truncation) when
    x_1 <= 2^64 - 2 (e.g., x_1 = hi(mulx64 a b)), because then
    x_1 * 2^64 + x_0 + y_0 <= (2^64-2)*2^64 + 2*(2^64-1) = 2^128 - 2. *)
Definition adc_2_short (x_1 x_0 y_0 : uint64) : uint64 * uint64 :=
  let sum := x_1 * modulus64 + x_0 + y_0 in
  (sum / modulus64, sum mod modulus64).

(** Overload 2: adc_2(x_1, x_0, y_1, y_0, r_1, r_0)
    Assembly: addq y_0, x_0; adcq y_1, x_1
    Computes: (r_1, r_0) where r_1 * 2^64 + r_0
              = (x_1 * 2^64 + x_0 + y_1 * 2^64 + y_0) mod 2^128

    Note: this CAN overflow 128 bits (the top carry is discarded). *)
Definition adc_2_full (x_1 x_0 y_1 y_0 : uint64) : uint64 * uint64 :=
  let sum := x_1 * modulus64 + x_0 + y_1 * modulus64 + y_0 in
  let sum_mod := sum mod (modulus64 * modulus64) in
  (sum_mod / modulus64, sum_mod mod modulus64).

(** *** adc_3: 3-word add-with-carry *)

(** adc_3(x_2, x_1, x_0, y_1, y_0, r_2, r_1, r_0)
    Assembly: addq y_0, x_0; adcq y_1, x_1; adcq $0, x_2
    Computes: (r_2, r_1, r_0) where
      r_2 * 2^128 + r_1 * 2^64 + r_0
      = x_2 * 2^128 + x_1 * 2^64 + x_0 + y_1 * 2^64 + y_0

    The 192-bit sum is exact (no overflow) when x_2 < 2^64 - 1,
    because the maximum carry into x_2 is 1. *)
Definition adc_3 (x_2 x_1 x_0 y_1 y_0 : uint64)
    : uint64 * uint64 * uint64 :=
  let sum := x_2 * modulus64 * modulus64
           + x_1 * modulus64 + x_0
           + y_1 * modulus64 + y_0 in
  (sum / (modulus64 * modulus64),
   (sum mod (modulus64 * modulus64)) / modulus64,
   sum mod modulus64).

(** ** mul_line: First Row of Multiplication *)

(** mul_line_recur models the template-recursive helper.
    At each step: mulx(x[I], y) → (hi, lo), then adc_2(hi, lo, carry) → (carry', result[I]).
    For the last word (I+1 >= R): result[I] = y * x[I] + carry (truncated to 64 bits). *)
Fixpoint mul_line_recur (xs : words) (y : uint64) (result : words)
    (I R : nat) (carry : uint64) : words :=
  match xs with
  | [] =>
      (* Done with x words. If M < R, store final carry at result[M] *)
      if (I <? R)%nat
      then set_word result I carry
      else result
  | x :: rest =>
      if (I <? R)%nat then
        if (I + 1 <? R)%nat then
          (* Normal case: mulx + adc_2 *)
          let r := mulx64 x y in
          let '(new_carry, res_I) := adc_2_short (hi r) (lo r) carry in
          mul_line_recur rest y (set_word result I res_I) (S I) R new_carry
        else
          (* Last word case: result[I] = y * x[I] + carry (truncated) *)
          set_word result I (normalize64 (y * x + carry))
      else result
  end.

(** mul_line: compute result[0..min(M+1,R)-1] = y * x[0..M-1]

    C++ reference (uint256.hpp, mul_line):
      mulx(y, x[0], carry, result[0]);
      mul_line_recur<1, R, M>(x, y, result, carry); *)
Definition mul_line (R : nat) (xs : words) (y : uint64) : words :=
  match xs with
  | [] => extend_words R
  | x0 :: rest =>
      let result := extend_words R in
      let r := mulx64 y x0 in  (* Note: C++ calls mulx(y, x[0], ...) *)
      let result' := set_word result 0 (lo r) in
      mul_line_recur rest y result' 1 R (hi r)
  end.

(** ** mul_add_line: Subsequent Rows of Multiplication *)

(** mul_add_line_recur models the template-recursive helper.
    Uses 2-word carry (c_hi, c_lo) for efficiency.

    At each step (J+1 < M && I+J < R):
      - If I+J+2 < R: mulx(x[J+1], y_i) → (hi, lo), then
          adc_3(hi, lo, result[I+J], c_hi, c_lo) → (c_hi', c_lo', result[I+J])
      - If I+J+1 < R but I+J+2 >= R: lo = x[J+1]*y_i, then
          adc_2(lo, result[I+J], c_hi, c_lo) → (c_lo', result[I+J])
      - Otherwise: result[I+J] += c_lo

    When J+1 >= M or I+J >= R (end of loop):
      - If I+M < R: adc_2(c_hi, c_lo, result[I+M-1]) → (result[I+M], result[I+M-1])
      - If I+M = R: result[I+M-1] += c_lo *)
Fixpoint mul_add_line_recur (xs_tail : words) (y_i : uint64) (result : words)
    (J I R : nat) (c_hi c_lo : uint64) : words :=
  match xs_tail with
  | [] =>
      (* End of x words: flush the carry *)
      let pos := (I + J)%nat in
      if (pos + 1 <? R)%nat then
        (* adc_2(c_hi, c_lo, result[pos], result[pos+1], result[pos]) *)
        let '(r_1, r_0) := adc_2_short c_hi c_lo (get_word result pos) in
        set_word (set_word result pos r_0) (pos + 1) r_1
      else if (pos <? R)%nat then
        (* Just add c_lo to result[pos] *)
        set_word result pos (normalize64 (get_word result pos + c_lo))
      else result
  | x_next :: rest =>
      if (I + J <? R)%nat then
        if (I + J + 2 <? R)%nat then
          (* Full case: mulx + adc_3 *)
          let r := mulx64 x_next y_i in
          let '(c_hi', c_lo', res_IJ) :=
            adc_3 (hi r) (lo r) (get_word result (I + J)) c_hi c_lo in
          mul_add_line_recur rest y_i (set_word result (I + J) res_IJ)
                             (S J) I R c_hi' c_lo'
        else if (I + J + 1 <? R)%nat then
          (* Second-to-last: lo = x_next * y_i, adc_2(lo, result[I+J], c_hi, c_lo) *)
          let lo_val := normalize64 (x_next * y_i) in
          let '(c_lo', res_IJ) :=
            adc_2_full lo_val (get_word result (I + J)) c_hi c_lo in
          mul_add_line_recur rest y_i (set_word result (I + J) res_IJ)
                             (S J) I R 0 c_lo'
        else
          (* Last position: result[I+J] += c_lo *)
          let result' := set_word result (I + J)
                           (normalize64 (get_word result (I + J) + c_lo)) in
          mul_add_line_recur rest y_i result' (S J) I R c_hi c_lo
      else result
  end.

(** mul_add_line: compute result[I..min(I+M+1,R)-1] += y_i * x[0..M-1]

    C++ reference (uint256.hpp, mul_add_line):
      if constexpr (I + 1 < R) {
          mulx(x[0], y_i, c_hi, c_lo);
      } else {
          c_hi = 0;
          c_lo = x[0] * y_i;
      }
      mul_add_line_recur<0, I, R, M>(x, y_i, result, c_hi, c_lo); *)
Definition mul_add_line (I R : nat) (xs : words) (y_i : uint64)
    (result : words) : words :=
  match xs with
  | [] => result
  | x0 :: rest =>
      let '(c_hi, c_lo) :=
        if (I + 1 <? R)%nat then
          let r := mulx64 x0 y_i in
          (hi r, lo r)
        else
          (0, normalize64 (x0 * y_i))
      in
      mul_add_line_recur rest y_i result 0 I R c_hi c_lo
  end.

(** ** truncating_mul_runtime: Full Runtime Multiplication *)

(** Recursive helper: applies mul_add_line for rows I = 1..N-1 *)
Fixpoint truncating_mul_runtime_recur (xs : words) (ys_tail : words)
    (result : words) (I R : nat) : words :=
  match ys_tail with
  | [] => result
  | y_i :: rest =>
      let result' := mul_add_line I R xs y_i result in
      truncating_mul_runtime_recur xs rest result' (S I) R
  end.

(** truncating_mul_runtime: main entry point.
    First row via mul_line, then subsequent rows via mul_add_line.

    C++ reference (uint256.hpp, truncating_mul_runtime):
      words_t<R> result;
      mul_line<R>(x, y[0], result);
      truncating_mul_runtime_recur<1, R, M, N>(x, y, result); *)
Definition truncating_mul_runtime (xs ys : words) (R : nat) : words :=
  match ys with
  | [] => extend_words R
  | y0 :: ys_rest =>
      let result := mul_line R xs y0 in
      truncating_mul_runtime_recur xs ys_rest result 1 R
  end.

(** Specialization for uint256: 4x4 -> 4 words *)
Definition truncating_mul256_runtime (x y : uint256) : uint256 :=
  words_to_uint256 (truncating_mul_runtime (uint256_to_words x)
                                            (uint256_to_words y) 4).
