(** * Long Division Proofs

    Correctness proofs for the long division model defined in Division.v.
*)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint Primitives Words WordsLemmas Division.

Module MakeProofs (U64 : Uint64) (U128 : Uint128)
  (Import Bridge : UintWiden U64 U128).
Import U64.
Include Division.Make(U64)(U128)(Bridge).
Module WL := WordsLemmas.MakeProofs(U64).
Import WL.

Import ListNotations.
Open Scope Z_scope.

(** ** Structural Properties *)

(** long_div_fold produces quotient with same length as input *)
Lemma long_div_fold_length : forall us v rem,
  length (ld_quot (long_div_fold us v rem)) = length us.
Proof.
  induction us as [|u rest IH]; intros v rem.
  - reflexivity.
  - unfold long_div_fold; fold long_div_fold.
    cbn [ld_quot length]. rewrite IH. reflexivity.
Qed.

(** ** Correctness *)

(** Correctness of long_div_fold: processes MSW-first list.
    The invariant uses rev to convert from the big-endian quotient order
    produced by long_div_fold to the little-endian to_Z_words interpretation. *)
Lemma long_div_fold_correct : forall us v rem,
  to_Z v > 0 ->
  to_Z rem < to_Z v ->
  let r := long_div_fold us v rem in
  to_Z rem * modulus_words (length us) + to_Z_words (rev us) =
    to_Z_words (rev (ld_quot r)) * to_Z v + to_Z (ld_rem r).
Proof.
  induction us as [|u rest IH]; intros v rem Hv Hrem.
  - cbn [long_div_fold ld_quot ld_rem rev length to_Z_words].
    rewrite modulus_words_0.
    lia.
  - unfold long_div_fold; fold long_div_fold. cbn [ld_quot ld_rem].
    pose proof (spec_div _ u _ Hv Hrem) as Hdiv.
    destruct (div rem u v) as [q rm].
    destruct Hdiv as [Hdiv_eq Hdiv_lt].
    cbn [fst snd].
    set (rec := long_div_fold rest v rm).
    pose proof (IH v rm Hv Hdiv_lt) as HIH.
    change (long_div_fold rest v rm) with rec in HIH.
    cbn in HIH.
    cbn [rev].
    rewrite !to_Z_words_app_single. rewrite !length_rev.
    cbn [length].
    rewrite modulus_words_succ.
    assert (Hlen: length (ld_quot rec) = length rest).
    { subst rec. apply long_div_fold_length. }
    rewrite Hlen.
    lia.
Qed.

(** Main correctness theorem for long_div *)
Theorem long_div_correct : forall us v,
  to_Z v > 0 ->
  let r := long_div us v in
  to_Z_words us = to_Z_words (ld_quot r) * to_Z v + to_Z (ld_rem r).
Proof.
  intros us v Hv. unfold long_div. cbn [ld_quot ld_rem].
  set (r := long_div_fold (rev us) v U64.zero).
  assert (Hrem: to_Z U64.zero < to_Z v) by (rewrite spec_zero; lia).
  pose proof (long_div_fold_correct (rev us) v U64.zero Hv Hrem) as Hfold.
  change (long_div_fold (rev us) v U64.zero) with r in Hfold.
  cbv zeta in Hfold. rewrite rev_involutive in Hfold.
  rewrite spec_zero, Z.mul_0_l, Z.add_0_l in Hfold.
  exact Hfold.
Qed.

(** ** Multi-Word Shift Correctness *)

(** Left-shift preserves value scaled by 2^shift.
    The result has length [length ws + 1] (overflow word appended). *)
Lemma shift_left_words_correct : forall ws shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words (shift_left_words ws shift) =
    to_Z_words ws * 2 ^ (Z.of_nat shift).
Proof. Admitted.

(** Right-shift divides value by 2^shift (truncating). *)
Lemma shift_right_words_correct : forall ws shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words (shift_right_words ws shift) =
    to_Z_words ws / 2 ^ (Z.of_nat shift).
Proof. Admitted.

(** Shift-left then shift-right is division (round-trip for aligned values). *)
Lemma shift_right_left_cancel : forall ws shift,
  (shift < Pos.to_nat U64.width)%nat ->
  to_Z_words ws mod 2 ^ (Z.of_nat shift) = 0 ->
  to_Z_words (shift_right_words (firstn (length ws) (shift_left_words ws shift)) shift) =
    to_Z_words ws.
Proof. Admitted.

(** ** Knuth Subtract-and-Correct *)

(** knuth_sub_loop computes [u_seg - q_hat * v] with borrow propagation.
    The mathematical value of the segment decreases by [q_hat * v_val],
    modulo the segment width, with the borrow [k] tracking the overflow. *)
Lemma knuth_sub_loop_correct : forall u_seg q_hat vs j k,
  length u_seg = (j + length vs)%nat ->
  let '(u', k') := knuth_sub_loop u_seg q_hat vs j k in
  to_Z_words u' + U128.to_Z k' * modulus_words (j + length vs) =
    to_Z_words u_seg - (U128.to_Z q_hat * to_Z_words vs - U128.to_Z k)
      * base width ^ (Z.of_nat j).
Proof. Admitted.

(** knuth_addback_loop computes [u_seg + v] with carry propagation.
    Used when the trial quotient overestimated by 1. *)
Lemma knuth_addback_loop_correct : forall u_seg vs j k,
  length u_seg = (j + length vs)%nat ->
  let '(u', k') := knuth_addback_loop u_seg vs j k in
  to_Z_words u' + U128.to_Z k' * modulus_words (j + length vs) =
    to_Z_words u_seg + (to_Z_words vs + U128.to_Z k)
      * base width ^ (Z.of_nat j).
Proof. Admitted.

(** knuth_div_subtract: one full subtract-and-correct step.
    Returns [(u_after, q_final)] where:
    - [u_after] is the updated segment
    - [q_final] is the corrected quotient digit
    The key invariant: [u_orig = q_final * v + u_after] over the segment. *)
Lemma knuth_div_subtract_correct : forall u_seg q_hat v n,
  length u_seg = (n + 1)%nat -> length v = n ->
  to_Z_words v > 0 ->
  let '(u_after, q_final) := knuth_div_subtract u_seg q_hat v n in
  to_Z_words u_seg =
    to_Z q_final * to_Z_words v + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.

(** ** Knuth Division — Single Step and Loop *)

(** knuth_div_step: one iteration combining estimate + subtract + correct. *)
Lemma knuth_div_step_correct : forall u v i n,
  length v = n -> (n > 1)%nat ->
  (i + n < length u)%nat ->
  to_Z_words v > 0 ->
  let '(u', q_i) := knuth_div_step u v i n in
  to_Z_words (get_segment u i (n + 1)) =
    to_Z q_i * to_Z_words v + to_Z_words (firstn n (get_segment u' i (n + 1))) /\
  0 <= to_Z_words (firstn n (get_segment u' i (n + 1))) < to_Z_words v.
Proof. Admitted.

(** knuth_div_loop: the outer loop iterating from [m-n] down to [0].
    Invariant: the mathematical quotient is accumulated in [quot],
    and [u] is progressively reduced. *)
Lemma knuth_div_loop_correct : forall u v quot n fuel current_i,
  length v = n -> (n > 1)%nat ->
  to_Z_words v > 0 ->
  let '(u_after, quot_final) := knuth_div_loop u v quot n fuel current_i in
  to_Z_words u =
    to_Z_words quot_final * to_Z_words v + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.

(** ** Knuth Division — Main Theorem *)

(** knuth_div: full Algorithm D for normalized inputs.
    Preconditions: [length u = m+1], [length v = n], [m >= n > 1],
    and the divisor is normalized (MSB of [v[n-1]] is set). *)
Theorem knuth_div_correct : forall m n u v,
  length u = (m + 1)%nat -> length v = n ->
  (m >= n)%nat -> (n > 1)%nat ->
  to_Z_words v > 0 ->
  let '(u_after, quot) := knuth_div m n u v in
  to_Z_words u = to_Z_words quot * to_Z_words v
    + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.

(** ** Top-Level Division Correctness *)

(** udivrem: general unsigned division dispatcher.
    Handles all cases: division by zero, dividend < divisor,
    single-word, long division, and Knuth multi-word division. *)
Theorem udivrem_correct : forall M N u v,
  length u = M -> length v = N ->
  to_Z_words v > 0 ->
  let r := udivrem M N u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

(** Specialization to 256-bit (4-word) operands. *)
Theorem udivrem256_correct : forall u v,
  length u = 4%nat -> length v = 4%nat ->
  to_Z_words v > 0 ->
  let r := udivrem 4 4 u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

End MakeProofs.
