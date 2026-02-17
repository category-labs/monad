(** * Constexpr Multiplication Model

    Models the C++ truncating_mul_constexpr function's unified nested-loop
    structure. This is schoolbook multiplication with truncation to R words.

    This file contains only definitions. Proofs are in ConstexprMulProofs.v.

    C++ reference (uint256.hpp, truncating_mul_constexpr):
      for (size_t j = 0; j < N; j++) {
          uint64_t carry = 0;
          for (size_t i = 0; i < M && i + j < R; i++) {
              uint64_t hi, lo;
              mulx(x[i], y[j], hi, lo);
              auto [s0, c0] = addc(lo, result[i + j], false);
              auto [s1, c1] = addc(s0, carry, false);
              result[i + j] = s1;
              auto [s2, c2] = addc(hi, c0, c1);
              carry = s2;
          }
          if (j + M < R) result[j + M] = carry;
      }
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives Words.
Import ListNotations.
Open Scope Z_scope.

(** Inner loop: process x[i] * y[j] for i = 0..M-1, accumulating into result[i+j]
    Returns updated result and final carry *)
Fixpoint constexpr_inner_loop (xs : words) (y : uint64) (result : words)
    (j : nat) (i : nat) (R : nat) (carry : uint64) : words * uint64 :=
  match xs with
  | [] => (result, carry)
  | x :: rest =>
      if (i + j <? R)%nat then
        let r := mulx64 x y in                                      (* hi:lo = x[i] * y[j] *)
        let s0 := addc64 (lo r) (get_word result (i + j)) false in  (* lo + result[i+j] *)
        let s1 := addc64 (value64 s0) carry false in                (* + carry *)
        let new_result := set_word result (i + j) (value64 s1) in
        let s2 := addc64 (hi r) 0 (carry64 s0 || carry64 s1) in     (* hi + c0 + c1 *)
        constexpr_inner_loop rest y new_result j (S i) R (value64 s2)
      else
        (result, carry)  (* i + j >= R: stop early (truncation) *)
  end.

(** Outer loop: iterate over y[j] for j = 0..N-1 *)
Fixpoint constexpr_outer_loop (xs ys : words) (result : words)
    (j : nat) (R : nat) : words :=
  match ys with
  | [] => result
  | y :: rest =>
      let '(new_result, carry) := constexpr_inner_loop xs y result j 0 R 0 in
      (* Store final carry at result[j + M] if in bounds *)
      let final_result :=
        if (j + length xs <? R)%nat
        then set_word new_result (j + length xs) carry
        else new_result in
      constexpr_outer_loop xs rest final_result (S j) R
  end.

(** truncating_mul_constexpr: schoolbook multiplication with truncation *)
Definition truncating_mul_constexpr (xs ys : words) (R : nat) : words :=
  let result := extend_words R in  (* Initialize to zeros *)
  constexpr_outer_loop xs ys result 0 R.

(** Specialization for uint256: 4x4 -> 4 words *)
Definition truncating_mul256_constexpr (x y : uint256) : uint256 :=
  words_to_uint256 (truncating_mul_constexpr (uint256_to_words x)
                                              (uint256_to_words y) 4).
