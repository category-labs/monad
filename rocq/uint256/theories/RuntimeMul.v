(** * Runtime Multiplication Model

    The [Make] functor (parameterized by [Uint64Ops]) models the C++
    [truncating_mul_runtime] function from uint256.hpp.  The inline
    assembly primitives (mulx, adc_2, adc_3) come from the [UintOps]
    interface; everything else is defined structurally.

    This file contains:

    - [mul_line] / [mul_line_recur]: first row (no accumulation)
    - [mul_add_line] / [mul_add_line_recur]: subsequent rows
      (multiply-accumulate)
    - [mul_add_line_recur_alt]: equivalent alternative formulation
    - [truncating_mul_runtime]: top-level entry point

    Proofs are in RuntimeMulProofs.v. *)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Uint Primitives Words.
Import ListNotations.

Module Make (Import U64 : Uint64Ops).
Include UintNotations(U64).
Include Words.Make(U64).
Open Scope uint_scope.

(** ** mul_line: First Row of Multiplication *)

(** mul_line_recur models the template-recursive helper.

    In our model below, the C++ the template parameter M is encoded in
    the length of the list xs which naturally leads to a
    pattern-matching definition.

    At each step: mulx(x[I], y) → (hi, lo), then adc_2(hi, lo, carry) →
    (carry', result[I]).

    For the last word (I+1 >= R): result[I] = y * x[I] + carry
    (truncated to 64 bits). *)
Fixpoint mul_line_recur (xs : words) (y : t) (result : words)
    (I R : nat) (carry : t) : words :=
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
          let (hi,lo) := mulx x y in
          let '(new_carry, res_I) := adc_2_short hi lo carry in
          mul_line_recur rest y (set_word result I res_I) (S I) R new_carry
        else
          (* Last word case: result[I] = y * x[I] + carry (truncated) *)
          set_word result I (y * x + carry)
      else result
  end.

(** mul_line: compute result[0..min(M+1,R)-1] = y * x[0..M-1]

    C++ reference (uint256.hpp, mul_line):
      mulx(y, x[0], carry, result[0]);
      mul_line_recur<1, R, M>(x, y, result, carry); *)
Definition mul_line (R : nat) (xs : words) (y : t) : words :=
  match xs with
  | [] => extend_words R
  | x0 :: rest =>
      let result := extend_words R in
      let '(carry, lo) := mulx y x0 in
      let result' := set_word result 0 lo in
      mul_line_recur rest y result' 1 R carry
  end.

(** ** mul_add_line: Subsequent Rows of Multiplication *)

(** mul_add_line_recur models the template-recursive helper.

    At each step (J+1 < M && I+J < R):
      - If I+J+2 < R: mulx(x[J+1], y_i) -> (hi, lo), then
          adc_3(hi, lo, result[I+J], c_hi, c_lo) -> (c_hi', c_lo', result[I+J])
      - If I+J+1 < R but I+J+2 >= R: lo = x[J+1]*y_i, then
          adc_2(lo, result[I+J], c_hi, c_lo) -> (c_lo', result[I+J])
      - Otherwise: result[I+J] += c_lo

    When J+1 >= M or I+J >= R (end of loop):
      - If I+M < R: adc_2(c_hi, c_lo, result[I+M-1]) -> (result[I+M], result[I+M-1])
      - If I+M = R: result[I+M-1] += c_lo *)
Fixpoint mul_add_line_recur (xs : words) (y_i : t) (result : words)
    (J I R : nat) (c_hi c_lo : t) : words :=
  match xs with
  | [] =>
      let pos := (I + J)%nat in
      if (pos + 1 <? R)%nat then
        let '(r_1, r_0) := adc_2_short c_hi c_lo (get_word result pos) in
        set_word (set_word result pos r_0) (pos + 1) r_1
      else if (pos <? R)%nat then
        set_word result pos (get_word result pos + c_lo)
      else result
  | x :: rest =>
      if (I + J <? R)%nat then
        if (I + J + 2 <? R)%nat then
          let '(hi, lo) := mulx x y_i in
          let '(c_hi', c_lo', res_IJ) :=
            adc_3 hi lo (get_word result (I + J)) c_hi c_lo in
          mul_add_line_recur rest y_i (set_word result (I + J) res_IJ)
                             (S J) I R c_hi' c_lo'
        else if (I + J + 1 <? R)%nat then
          let lo_val := x * y_i in
          let '(c_lo', res_IJ) :=
            adc_2_full lo_val (get_word result (I + J)) c_hi c_lo in
          mul_add_line_recur rest y_i (set_word result (I + J) res_IJ)
                             (S J) I R c_hi c_lo'
        else
          let result' := set_word result (I + J)
                           (get_word result (I + J) + c_lo) in
          mul_add_line_recur rest y_i result' (S J) I R c_hi c_lo
      else result
  end.

(** An alternative model for mul_add_line_recur which is slightly more
    faithful to the recursive structure.  Proved equivalent to
    mul_add_line_recur by mul_add_line_recur_alt_eq. *)
Fixpoint mul_add_line_recur_alt (xs : words) (y_i : t) (result : words)
    (J I R : nat) (c_hi c_lo : t) : words :=
  match xs with
  | [] =>
      let pos := (I + J)%nat in
      if (pos + 1 <? R)%nat then
        let '(r_1, r_0) := adc_2_short c_hi c_lo (get_word result pos) in
        set_word (set_word result pos r_0) (pos + 1) r_1
      else if (pos <? R)%nat then
        set_word result pos (get_word result pos + c_lo)
      else result
  | x :: rest =>
      if (I + J <? R)%nat then
        let '(c_hi', c_lo', res_IJ) :=
          if (I + J + 2 <? R)%nat then
            let '(hi, lo) := mulx x y_i in
            adc_3 hi lo (get_word result (I + J)) c_hi c_lo
          else if (I + J + 1 <? R)%nat then
            let lo_val := x * y_i in
            let '(c_lo', res_IJ) :=
              adc_2_full lo_val (get_word result (I + J)) c_hi c_lo in
            (c_hi, c_lo', res_IJ)
          else
            (c_hi, c_lo, (get_word result (I + J) + c_lo)) in
        mul_add_line_recur_alt rest y_i (set_word result (I + J) res_IJ)
                           (S J) I R c_hi' c_lo'
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
Definition mul_add_line (I R : nat) (xs : words) (y_i : t)
    (result : words) : words :=
  match xs with
  | [] => result
  | x0 :: rest =>
      let '(c_hi, c_lo) :=
        if (I + 1 <? R)%nat then
          mulx x0 y_i
        else
          (0, x0 * y_i)
      in
      mul_add_line_recur rest y_i result 0 I R c_hi c_lo
  end.

(** ** truncating_mul_runtime: Full Runtime Multiplication *)

(** Recursive helper: applies mul_add_line for rows I = 1..N-1 *)
Fixpoint truncating_mul_runtime_recur (xs : words) (ys : words)
    (result : words) (I R : nat) : words :=
  match ys with
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
  | y :: rest =>
      let result := mul_line R xs y in
      truncating_mul_runtime_recur xs rest result 1 R
  end.

End Make.
