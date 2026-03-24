(** * Multi-Word Division Model

    The [Make] functor (parameterized by [Uint64Ops]) models the C++
    [udivrem] function from uint256.hpp.  Leaf operations (div, shld64,
    shrd64) come from the [UintOps] interface and Primitives.Make.

    The functor defines:

    - [long_div]: single-word divisor path
    - [knuth_div_estimate]: trial quotient for Knuth Algorithm D
    - [countl_zero]: leading-zero count (via abstract shifts)
    - [shift_left_words] / [shift_right_words]: word-list
      normalization and denormalization
    - Utility helpers: [count_significant_words], [get_segment],
      [set_segment]

    Legacy concrete definitions outside the functor (using Z-level
    arithmetic) cover the Knuth subtract-and-correct loop,
    [udivrem], [negate_words], and [sdivrem256].  These are blocked
    from porting by [knuth_div_subtract_correct]'s dependence on
    [to_Z_words].

    Proofs are in DivisionProofs.v. *)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Uint Primitives Words.
Import ListNotations.

Module Make (U64 : Uint64Ops) (U128 : Uint128Ops)
  (Import Bridge : UintWidenOps U64 U128).
Include UintNotations(U64).
Include Primitives.Make(U64).
Include Words.Make(U64).

(* Notations for 128-bit operations *)
Module WN := UintNotations(U128).

(** Maximum representable value (all bits set, i.e., [2^width - 1]) *)
Definition u64_max_val : U64.t := 0 - 1.

(** Result of long division *)
Record long_div_result := mk_long_div_result {
  ld_quot : words;
  ld_rem : U64.t
}.

(** Process words from most significant to least significant.
    Input: list in MSW-first order (i.e., rev of little-endian).
    Each step divides (rem * (base width) + u) by v, passing remainder forward. *)
Fixpoint long_div_fold (us : words) (v : U64.t) (rem : U64.t) : long_div_result :=
  match us with
  | [] => mk_long_div_result [] rem
  | u :: rest =>
      let (quot,rem) := U64.div rem u v in
      let rec_result := long_div_fold rest v rem in
      mk_long_div_result (quot :: ld_quot rec_result) (ld_rem rec_result)
  end.

(** long_div: divide word list by single word.
    Input is little-endian, so we reverse to process MSW first,
    then reverse quotient back to little-endian. *)
Definition long_div (us : words) (v : U64.t) : long_div_result :=
  let r := long_div_fold (rev us) v 0 in
  mk_long_div_result (rev (ld_quot r)) (ld_rem r).


(** ** Knuth Division Core *)

(** ** Utility Definitions *)

(** Count leading zeros by scanning from MSB down.
    At each step, [shr x pos'] is zero iff all bits at position [pos']
    and above are zero. *)
(* TODO: Consider adding counting zeros to the interface since this
         definitions is a bit weird? *)
Fixpoint countl_zero_go (x : U64.t) (pos : nat) : nat :=
  match pos with
  | O => O
  | S pos' =>
      if (U64.shr x pos' =? 0) then S (countl_zero_go x pos')
      else O
  end.

(** Count leading zeros of a value.
    C++ ref: std::countl_zero. *)
Definition countl_zero (x : U64.t) : nat :=
  countl_zero_go x (Pos.to_nat U64.width).

(** Count non-zero words from MSW down.
    Scans the reversed (MSW-first) word list, skipping leading zeros. *)
Fixpoint skip_leading_zeros (rs : words) : nat :=
  match rs with
  | [] => 0%nat
  | r :: rest => if (r =? 0) then skip_leading_zeros rest else length rs
  end.

Definition count_significant_words (ws : words) : nat :=
  skip_leading_zeros (rev ws).

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

Section KnuthMainLoop.

(* Give notational precedence to 128-bit operations. *)
Import WN.
Local Open Scope uint_scope.

(** Trial quotient estimation with one refinement step.
    Return a 128-bit trial quotient following the
    C++ ref: uint256.hpp lines 1088-1137. *)
Definition knuth_div_estimate (u_hi u_mid u_lo v_hi v_snd : U64.t) : U128.t :=
  if (U64.eqb u_hi v_hi) then widen u64_max_val
  else
    let (q0,r0) := U64.div u_hi u_mid v_hi in
    if (U64.eqb q0 U64.zero) then 0
    else
      let q_hat := widen q0 in
      if (q_hat * widen v_snd >? combine r0 u_lo)
      then q_hat - 1
      else q_hat.

(** Subtraction loop: [u_seg[0..n-1] -= q_hat * v[0..n-1]],
    propagating borrow via [k : U128.t].

    Each iteration mirrors the C++ (uint256.hpp lines 1143-1147):

      [prod  = q_hat * v[j]]
        128-bit full multiply (both operands widened to U128).

      [t = u[j+ix] - k - (prod & mask64)]
        128-bit subtract; [prod & mask64] extracts the low 64 bits.
        Modelled as [widen (trunc prod)] which is equivalent.

      [u[j+ix] = (uint64_t)t]
        Truncate [t] to 64 bits and store back.

      [k = (prod >> 64) - (int128_t)t >> 64]
        Borrow propagation.  [prod >> 64] is the high half of the
        product; [(int128_t)t >> 64] is an arithmetic right-shift
        that sign-extends if [t] wrapped negative.

    Returns [(u_seg, k)] where [k] is the final borrow.
    The caller is responsible for the post-loop assignment
    [u[ix+n] = (uint64_t)(u[ix+n] - k)] (C++ line 1149-1150). *)
Fixpoint knuth_sub_loop (u_seg : words) (q_hat : U128.t) (vs : words)
    (j : nat) (k : U128.t) : words * U128.t :=
  match vs with
  | [] => (u_seg, k)
  | vj :: vs_rest =>
      let prod := q_hat * widen vj in
      let t := widen (get_word u_seg j) - k - widen (trunc prod) in
      let k' := widen (hi prod) - signed_hi t in
      knuth_sub_loop (set_word u_seg j (trunc t)) q_hat vs_rest (S j) k'
  end.

(** Add-back loop: [u_seg[0..n-1] += v[0..n-1]], propagating carry via [k].
    Used when the trial quotient was one too large.
    C++ ref: uint256.hpp lines 1158-1163. *)
Fixpoint knuth_addback_loop (u_seg : words) (vs : words)
    (j : nat) (k : U128.t) : words * U128.t :=
  match vs with
  | [] => (u_seg, k)
  | vj :: vs_rest =>
      let t := widen (get_word u_seg j) + widen vj + k in
      knuth_addback_loop (set_word u_seg j (trunc t)) vs_rest (S j) (U128.shr t 64)
  end.

(** Word-level subtract-and-correct, modeling the C++ uint128_t loop.
    Takes [q_hat : U128.t] from Uint.v.
    Returns updated segment and final quotient word.
    C++ ref: uint256.hpp lines 1139-1165. *)
Definition knuth_div_subtract (u_seg : words) (q_hat : U128.t)
    (v : words) (n : nat) : words * U64.t :=
  let '(u_sub, k) := knuth_sub_loop u_seg q_hat v 0%nat 0 in
  let t := widen (get_word u_sub n) - k in
  let u_after := set_word u_sub n (trunc t) in
  if (U128.shr t 127 =? 1) then
    let '(u_corr, k_add) := knuth_addback_loop u_after v 0%nat 0 in
    (set_word u_corr n (trunc (widen (get_word u_corr n) + k_add)),
     trunc (q_hat - 1))
  else
    (u_after, trunc q_hat).

End KnuthMainLoop.

(** ** Normalization / Denormalization *)

(** Left-shift a word list by [shift] bits (0 <= shift < 64).
    Produces [length ws + 1] words (overflow word appended as MSW).
    C++ ref: uint256.hpp lines 1208-1213. *)
Fixpoint shift_left_words_aux (ws : words) (prev : U64.t) (shift : nat)
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

(** ** Legacy concrete definitions
    The following use Z-level arithmetic ([to_Z_words], [Z_to_words],
    [normalize64]) and cannot move into the [UintOps] functor.
    [knuth_div_subtract_correct] is the root blocker — it models the
    subtract-and-correct step mathematically on Z rather than with
    word-level operations.  Porting it would require defining
    multi-word multiply-by-scalar and subtract-with-borrow in the
    abstract interface. *)

(** One iteration of Knuth division: estimate + subtract + correct. *)
Definition knuth_div_step (u : words) (v : words) (i n : nat)
    : words * U64.t :=
  let q_hat := knuth_div_estimate
    (get_word u (i + n)) (get_word u (i + n - 1))
    (get_word u (i + n - 2)) (get_word v (n - 1)) (get_word v (n - 2)) in
  if (U128.eqb q_hat U128.zero) then (u, 0)
  else
    let u_seg := get_segment u i (n + 1) in
    let '(new_seg, final_q) :=
      knuth_div_subtract u_seg q_hat v n in
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
    let (q,r) := U64.div 0 (get_word u 0) (get_word v 0) in
    mk_udivrem_result
      (set_word (extend_words M) 0 q)
      (set_word (extend_words N) 0 r)
  else if Nat.eqb n 1 then
    let ld := long_div (firstn m u) (get_word v 0) in
    mk_udivrem_result
      (ld_quot ld ++ repeat 0 (M - length (ld_quot ld)))
      (set_word (extend_words N) 0 (ld_rem ld))
  else
    let shift := countl_zero (get_word v (n - 1)) in
    let u_norm := shift_left_words (firstn m u) shift in
    let v_norm := firstn n (shift_left_words (firstn n v) shift) in
    let '(u_after, quot) := knuth_div m n u_norm v_norm in
    let rem := shift_right_words (firstn n u_after) shift in
    mk_udivrem_result
      (quot ++ repeat 0 (M - length quot))
      (rem ++ repeat 0 (N - length rem)).

(** ** Signed Division *)

(** Two's complement negation of a word list via borrow-chain
    subtraction from zero.  Each word is subtracted from 0 with
    borrow propagation, equivalent to bitwise complement + 1. *)
Fixpoint negate_words_aux (ws : words) (borrow : bool) : words :=
  match ws with
  | [] => []
  | w :: rest =>
      let r := subb64 0 w borrow in
      value64 r :: negate_words_aux rest (carry64 r)
  end.

Definition negate_words (ws : words) : words :=
  negate_words_aux ws false.

(** Test whether the sign bit (MSB of the top word) is set.
    [n] is the number of words in the representation. *)
Definition is_negative (ws : words) (n : nat) : bool :=
  U64.shr (get_word ws (n - 1)) (Pos.to_nat U64.width - 1) =? 1.

(** Signed division of [n]-word two's complement integers.
    Converts operands to absolute values, performs unsigned division,
    then adjusts the signs of quotient and remainder.
    C++ ref: uint256.hpp lines 1299-1316. *)
Definition sdivrem (n : nat) (u v : words) : udivrem_result :=
  let u_neg := is_negative u n in
  let v_neg := is_negative v n in
  let u_abs := if u_neg then negate_words u else u in
  let v_abs := if v_neg then negate_words v else v in
  let result := udivrem n n u_abs v_abs in
  let quot_neg := xorb u_neg v_neg in
  mk_udivrem_result
    (if quot_neg then negate_words (ud_quot result) else ud_quot result)
    (if u_neg then negate_words (ud_rem result) else ud_rem result).

End Make.
