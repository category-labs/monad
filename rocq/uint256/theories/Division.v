(** * Multi-Word Division Model

    Models the C++ udivrem function which divides an M-word number by an
    N-word divisor.  The control flow is identical for both constexpr
    and runtime paths; only the leaf operations (div64, shld64, shrd64)
    differ.

    This file contains:

    - Single-word divisor model (long_div);
    - Knuth's Algorithm D for multi-word divisors
    - udivrem: top-level unsigned division dispatcher
    - sdivrem256: signed division wrapper

    Proofs are in DivisionProofs.v.
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Uint Primitives Words.
Import ListNotations.
Open Scope Z_scope.

(** Result of long division *)
Record long_div_result := mk_long_div_result {
  ld_quot : words;
  ld_rem : uint64
}.

(** Process words from most significant to least significant.
    Input: list in MSW-first order (i.e., rev of little-endian).
    Each step divides (rem * 2^64 + u) by v, passing remainder forward. *)
Fixpoint long_div_fold (us : words) (v : uint64) (rem : uint64) : long_div_result :=
  match us with
  | [] => mk_long_div_result [] rem
  | u :: rest =>
      let r := div64 rem u v in
      let rec_result := long_div_fold rest v (rem64 r) in
      mk_long_div_result (quot64 r :: ld_quot rec_result) (ld_rem rec_result)
  end.

(** long_div: divide word list by single word.
    Input is little-endian, so we reverse to process MSW first,
    then reverse quotient back to little-endian. *)
Definition long_div (us : words) (v : uint64) : long_div_result :=
  let r := long_div_fold (rev us) v 0 in
  mk_long_div_result (rev (ld_quot r)) (ld_rem r).

(** ** Utility Definitions *)

(** Count non-zero words from MSW down.
    Scans the reversed (MSW-first) word list, skipping leading zeros. *)
Fixpoint skip_leading_zeros (rs : words) : nat :=
  match rs with
  | [] => 0%nat
  | r :: rest => if (r =? 0) then skip_leading_zeros rest else length rs
  end.

Definition count_significant_words (ws : words) : nat :=
  skip_leading_zeros (rev ws).

(** Leading zeros of a 64-bit word. C++ ref: std::countl_zero. *)
Definition countl_zero64 (w : uint64) : nat :=
  if (w =? 0) then 64%nat else (63 - Z.to_nat (Z.log2 w))%nat.

(** Decompose a Z value into n little-endian 64-bit words. *)
(* TODO: Possibly rename this: from_Z_words? to_words_Z? *)
Fixpoint Z_to_words (z : Z) (n : nat) : words :=
  match n with
  | O => []
  | S n' => normalize64 z :: Z_to_words (Z.shiftr z 64) n'
  end.

(** Extract a contiguous sub-range of a word list. *)
Definition get_segment (ws : words) (start len : nat) : words :=
  firstn len (skipn start ws).

(** Update a contiguous sub-range of a word list. *)
Fixpoint set_segment (ws : words) (start : nat) (seg : words) : words :=
  match start with
  | O => seg ++ skipn (length seg) ws
  | S start' =>
      match ws with
      | [] => []
      | w :: rest => w :: set_segment rest start' seg
      end
  end.

(** ** Normalization / Denormalization *)

(** Left-shift a word list by [shift] bits (0 <= shift < 64).
    Produces [length ws + 1] words (overflow word appended as MSW).
    Uses shld64 from Primitives.v.
    C++ ref: uint256.hpp lines 1208-1213. *)
Fixpoint shift_left_words_aux (ws : words) (prev : uint64) (shift : nat)
    : words :=
  match ws with
  | [] => [shld64 0 prev shift]
  | w :: rest => shld64 w prev shift :: shift_left_words_aux rest w shift
  end.

Definition shift_left_words (ws : words) (shift : nat) : words :=
  shift_left_words_aux ws 0 shift.

(** Right-shift a word list by [shift] bits (0 <= shift < 64).
    Denormalizes the remainder after Knuth division.
    C++ ref: uint256.hpp lines 1223-1226. *)
Fixpoint shift_right_words (ws : words) (shift : nat) : words :=
  match ws with
  | [] => []
  | w :: rest =>
      let high := hd 0 rest in
      shrd64 high w shift :: shift_right_words rest shift
  end.

(** ** Knuth Division Core *)

(** Trial quotient estimation with one refinement step.
    C++ ref: uint256.hpp lines 1088-1137. *)
Definition knuth_div_estimate (u_high u_mid u_low v_high v_second : uint64)
    : uint64 :=
  if (u_high =? v_high) then modulus64 - 1
  else
    let r := div64 u_high u_mid v_high in
    let q0 := quot64 r in
    if (q0 =? 0) then 0
    else
      let r0 := rem64 r in
      if (q0 * v_second >? r0 * modulus64 + u_low)
      then q0 - 1
      else q0.

(** Subtract q_hat * v from u segment, with add-back correction.
    Modeled mathematically on Z (the C++ uses uint128_t, not assembly).
    C++ ref: uint256.hpp lines 1139-1165. *)
(* TODO: Refine to model C++ more closely since this represents the meat
   of the algorithm *)
Definition knuth_div_subtract_correct (u_seg : words) (q_hat : Z)
    (v : words) (n : nat) : words * uint64 :=
  let u_val := to_Z_words u_seg in
  let v_val := to_Z_words v in
  let diff := u_val - q_hat * v_val in
  if (diff <? 0) then
    (Z_to_words (diff + v_val) (n + 1), normalize64 (q_hat - 1))
  else
    (Z_to_words diff (n + 1), normalize64 q_hat).

(** One iteration of Knuth division: estimate + subtract + correct. *)
Definition knuth_div_step (u : words) (v : words) (i n : nat)
    : words * uint64 :=
  let q_hat := knuth_div_estimate
    (get_word u (i + n)) (get_word u (i + n - 1))
    (get_word u (i + n - 2)) (get_word v (n - 1)) (get_word v (n - 2)) in
  if (q_hat =? 0) then (u, 0)
  else
    let u_seg := get_segment u i (n + 1) in
    let '(new_seg, final_q) :=
      knuth_div_subtract_correct u_seg q_hat v n in
    (set_segment u i new_seg, final_q).

(** Outer loop: iterate from i = m-n down to 0.
    [fuel] ensures structural termination; [current_i] is the actual index. *)
Fixpoint knuth_div_loop (u : words) (v : words) (quot : words)
    (n : nat) (fuel : nat) (current_i : nat) : words * words :=
  match fuel with
  | O => (u, quot)
  | S fuel' =>
      let '(u', q_i) := knuth_div_step u v current_i n in
      knuth_div_loop u' v (set_word quot current_i q_i)
        n fuel' (Nat.pred current_i)
  end.

(** Knuth's Algorithm D: divide m+1 words by n words (n > 1).
    Requires normalized divisor (MSB of v[n-1] set).
    Returns (modified_u, quotient). Remainder is first n words of modified_u.
    C++ ref: uint256.hpp line 1074. *)
Definition knuth_div (m n : nat) (u v : words) : words * words :=
  knuth_div_loop u v (extend_words (m - n + 1)) n (m - n + 1) (m - n).

(** ** Top-Level Unsigned Division *)

Record udivrem_result := mk_udivrem_result {
  ud_quot : words;
  ud_rem : words
}.

(** Top-level unsigned division dispatcher.
    Dispatches to 4 cases based on count_significant_words.
    [M] and [N] are the output sizes for quotient and remainder.

    Deviates from the C++ implementation in the case of division by
    zero.  Rather than raising an assertion, the model returns 0 for any
    given divisor.  In the knuth_div case, the normalisation shift is
    only applied to the significant words (the C++ bounds the loops
    using the template parameters so they can be unrolled -- check
    this detail).
*)
Definition udivrem (M N : nat) (u v : words) : udivrem_result :=
  let m := count_significant_words u in
  let n := count_significant_words v in
  if Nat.eqb n 0 then
    mk_udivrem_result (extend_words M) (extend_words N)
  else if Nat.ltb m n then
    mk_udivrem_result (extend_words M)
      (firstn N (u ++ repeat 0 N))
  else if Nat.eqb m 1 then
    let r := div64 0 (get_word u 0) (get_word v 0) in
    mk_udivrem_result
      (set_word (extend_words M) 0 (quot64 r))
      (set_word (extend_words N) 0 (rem64 r))
  else if Nat.eqb n 1 then
    let ld := long_div (firstn m u) (get_word v 0) in
    mk_udivrem_result
      (ld_quot ld ++ repeat 0 (M - length (ld_quot ld)))
      (set_word (extend_words N) 0 (ld_rem ld))
  else
    let shift := countl_zero64 (get_word v (n - 1)) in
    let u_norm := shift_left_words (firstn m u) shift in
    let v_norm := firstn n (shift_left_words (firstn n v) shift) in
    let '(u_after, quot) := knuth_div m n u_norm v_norm in
    let rem := shift_right_words (firstn n u_after) shift in
    mk_udivrem_result
      (quot ++ repeat 0 (M - length quot))
      (rem ++ repeat 0 (N - length rem)).

(** ** Signed Division *)

(** Two's complement negation of a word list. *)
Definition negate_words (ws : words) : words :=
  Z_to_words ((-to_Z_words ws) mod modulus_words (length ws)) (length ws).

(** Signed 256-bit division (two's complement).
    C++ ref: uint256.hpp lines 1299-1316. *)
Definition sdivrem256 (u v : words) : udivrem_result :=
  let sign_bit := Z.shiftl 1 63 in
  let u_neg := negb (Z.land (get_word u 3) sign_bit =? 0) in
  let v_neg := negb (Z.land (get_word v 3) sign_bit =? 0) in
  let u_abs := if u_neg then negate_words u else u in
  let v_abs := if v_neg then negate_words v else v in
  let result := udivrem 4 4 u_abs v_abs in
  let quot_neg := xorb u_neg v_neg in
  mk_udivrem_result
    (if quot_neg then negate_words (ud_quot result) else ud_quot result)
    (if u_neg then negate_words (ud_rem result) else ud_rem result).
