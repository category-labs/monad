(** * Long Division Proofs

    Correctness proofs for the long division model defined in Division.v.
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives Words WordsLemmas Division.
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

(** long_div produces quotient with same length as input *)
Lemma long_div_length : forall us v,
  length (ld_quot (long_div us v)) = length us.
Proof.
  intros us v. unfold long_div. simpl.
  rewrite length_rev. rewrite long_div_fold_length. rewrite length_rev.
  reflexivity.
Qed.

(** ** Correctness *)

(** Correctness of long_div_fold: processes MSW-first list.
    The invariant uses rev to convert from the big-endian quotient order
    produced by long_div_fold to the little-endian to_Z_words interpretation. *)
Lemma long_div_fold_correct : forall us v rem,
  0 < v < modulus64 ->
  0 <= rem < v ->
  words_valid us ->
  let r := long_div_fold us v rem in
  rem * modulus_words (length us) + to_Z_words (rev us) =
    to_Z_words (rev (ld_quot r)) * to_Z64 v + to_Z64 (ld_rem r) /\
  0 <= to_Z64 (ld_rem r) < to_Z64 v.
Proof.
  induction us as [|u rest IH]; intros v rem Hv Hrem Hvalid.
  - cbn [long_div_fold ld_quot ld_rem rev length].
    cbn [to_Z_words modulus_words words_bits Z.of_nat Z.mul Z.pow_pos Pos.mul].
    unfold modulus_words, words_bits. cbn [Z.of_nat Z.mul Z.pow_pos Pos.mul].
    unfold to_Z64. split; lia.
  - unfold long_div_fold; fold long_div_fold. cbn [ld_quot ld_rem].
    set (r := div64 rem u v). set (rec := long_div_fold rest v (rem64 r)).
    assert (Hdiv: Z.shiftl (to_Z64 rem) 64 + to_Z64 u =
            to_Z64 (quot64 r) * to_Z64 v + to_Z64 (rem64 r) /\
            to_Z64 (rem64 r) < to_Z64 v).
    { apply div64_correct. lia. unfold div64_precondition, to_Z64. lia. }
    destruct Hdiv as [Hdiv_eq Hdiv_rem_lt].
    assert (Hrem64_nn: 0 <= to_Z64 (rem64 r)).
    { subst r. unfold div64, rem64, from_Z64, normalize64, to_Z64.
      apply Z.mod_pos_bound. unfold modulus64. lia. }
    assert (Hvalid_rest: words_valid rest). { inversion Hvalid; assumption. }
    pose proof (IH v (rem64 r) Hv (conj Hrem64_nn Hdiv_rem_lt) Hvalid_rest) as HIH.
    change (long_div_fold rest v (rem64 r)) with rec in HIH.
    destruct HIH as [HIH_eq HIH_rem].
    split; [| exact HIH_rem].
    cbn [rev]. rewrite !to_Z_words_app_single. rewrite !length_rev.
    assert (Hlen_rec: length (ld_quot rec) = length rest).
    { subst rec. apply long_div_fold_length. }
    rewrite Hlen_rec. cbn [length].
    unfold modulus_words, words_bits. rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat (length rest)) * 64)
      with (64 + 64 * Z.of_nat (length rest)) by lia.
    rewrite Z.pow_add_r by lia.
    set (M := 2 ^ (64 * Z.of_nat (length rest))).
    unfold to_Z64 in *. rewrite Z.shiftl_mul_pow2 in Hdiv_eq by lia.
    unfold modulus_words, words_bits in HIH_eq.
    replace (Z.of_nat (length rest) * 64)
      with (64 * Z.of_nat (length rest)) in HIH_eq by lia.
    fold M in HIH_eq.
    nia.
Qed.

(** Main correctness theorem for long_div *)
Theorem long_div_correct : forall us v,
  words_valid us ->
  0 < v < modulus64 ->
  let r := long_div us v in
  to_Z_words us = to_Z_words (ld_quot r) * to_Z64 v + to_Z64 (ld_rem r) /\
  0 <= to_Z64 (ld_rem r) < to_Z64 v.
Proof.
  intros us v Hvalid Hv. unfold long_div. cbn [ld_quot ld_rem].
  set (r := long_div_fold (rev us) v 0).
  assert (Hvalid_rev: words_valid (rev us)).
  { unfold words_valid in *. apply Forall_rev. exact Hvalid. }
  pose proof (long_div_fold_correct (rev us) v 0 Hv
    (conj (Z.le_refl 0) (proj1 Hv)) Hvalid_rev) as Hfold.
  change (long_div_fold (rev us) v 0) with r in Hfold.
  cbv zeta in Hfold. rewrite rev_involutive in Hfold.
  rewrite Z.mul_0_l, Z.add_0_l in Hfold. exact Hfold.
Qed.
(*
(** ** Multi-Word Shift Correctness *)

Lemma shift_left_words_correct : forall ws shift,
  words_valid ws -> (shift < 64)%nat ->
  to_Z_words (shift_left_words ws shift) =
    to_Z_words ws * 2 ^ (Z.of_nat shift).
Proof. Admitted.

Lemma shift_right_words_correct : forall ws shift,
  words_valid ws -> (shift < 64)%nat ->
  to_Z_words (shift_right_words ws shift) =
    to_Z_words ws / 2 ^ (Z.of_nat shift).
Proof. Admitted.

(** ** Knuth Division Correctness *)

Theorem knuth_div_correct : forall m n u v,
  words_valid u -> words_valid v ->
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
  words_valid u -> words_valid v ->
  length u = M -> length v = N ->
  to_Z_words v > 0 ->
  let r := udivrem M N u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.

Theorem udivrem256_correct : forall u v,
  words_valid u -> words_valid v ->
  length u = 4%nat -> length v = 4%nat ->
  to_Z_words v > 0 ->
  let r := udivrem 4 4 u v in
  to_Z_words u =
    to_Z_words (ud_quot r) * to_Z_words v + to_Z_words (ud_rem r) /\
  0 <= to_Z_words (ud_rem r) < to_Z_words v.
Proof. Admitted.
