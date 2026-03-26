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

(*
(** ** Multi-Word Shift Correctness *)

Lemma shift_left_words_correct : forall ws shift,
  (shift < 64)%nat ->
  to_Z_words (shift_left_words ws shift) =
    to_Z_words ws * 2 ^ (Z.of_nat shift).
Proof. Admitted.

Lemma shift_right_words_correct : forall ws shift,
  (shift < 64)%nat ->
  to_Z_words (shift_right_words ws shift) =
    to_Z_words ws / 2 ^ (Z.of_nat shift).
Proof. Admitted.

(** ** Knuth Division Correctness *)

Theorem knuth_div_correct : forall m n u v,
  length u = (m + 1)%nat -> length v = n ->
  (m >= n)%nat -> (n > 1)%nat ->
  Z.testbit (get_word v (n - 1)) 63 = true ->
  let '(u_after, quot) := knuth_div m n u v in
  to_Z_words u = to_Z_words quot * to_Z_words v
    + to_Z_words (firstn n u_after) /\
  0 <= to_Z_words (firstn n u_after) < to_Z_words v.
Proof. Admitted.
*)
(** ** Top-Level Division Correctness *)

Theorem udivrem_correct : forall M N u v,
  length u = M -> length v = N ->
  to_Z_words v > 0 ->
  let r := udivrem M N u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

Theorem udivrem256_correct : forall u v,
  length u = 4%nat -> length v = 4%nat ->
  to_Z_words v > 0 ->
  let r := udivrem 4 4 u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

End MakeProofs.
