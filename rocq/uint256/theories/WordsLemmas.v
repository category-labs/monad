(** * Lemmas for the Multi-Word Unsigned Integers

    This file proves various properties for the words type defined in
    Words.v

    This is a shared foundation used by both constexpr and runtime
    multiplication models, as well as division.  *)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives Words.
Import ListNotations.
Open Scope Z_scope.

(** Equivalence lemma: uint256 and word list representations agree *)
Lemma uint256_words_equiv : forall x : uint256,
  to_Z256 x = to_Z_words (uint256_to_words x).
Proof.
  intros x.
  unfold to_Z256, uint256_to_words, to_Z_words, to_Z64.
  ring.
Qed.

(** Value of valid n-word list is bounded *)
Lemma words_valid_bound : forall ws,
  words_valid ws ->
  0 <= to_Z_words ws < modulus_words (length ws).
Proof.
  induction ws as [| w rest IH]; intros Hvalid.
  - unfold modulus_words, words_bits; simpl; lia.
  - unfold modulus_words, words_bits; cbn [to_Z_words length].
    inversion Hvalid as [| w' rest' Hw Hrest]; subst.
    specialize (IH Hrest).
    unfold to_Z64 in *.
    unfold modulus_words, words_bits in *.
    rewrite Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat (length rest)) * 64)
      with (64 + Z.of_nat (length rest) * 64) by ring.
    rewrite Z.pow_add_r by lia.
    unfold modulus64 in *.
    split; lia.
Qed.

(** ** Word List Helper Lemmas *)

(** Length of set_word is preserved *)
Lemma set_word_length : forall ws i v,
  length (set_word ws i v) = length ws.
Proof.
  induction ws as [|w rest IH]; intros i v.
  - simpl; reflexivity.
  - destruct i.
    + simpl. reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.

(** set_word preserves words_valid *)
Lemma set_word_valid : forall ws i v,
  words_valid ws ->
  0 <= v < modulus64 ->
  words_valid (set_word ws i v).
Proof.
  unfold words_valid.
  induction ws as [|w rest IH]; intros i v Hvalid Hv.
  - constructor.
  - destruct i; inversion Hvalid; subst; cbn [set_word];
    constructor; try assumption. apply IH; assumption.
Qed.

(** get_word after set_word at same index *)
Lemma get_set_word_same : forall ws i v,
  (i < length ws)%nat ->
  get_word (set_word ws i v) i = v.
Proof.
  induction ws as [|w rest IH]; intros i v Hi.
  - simpl in Hi. lia.
  - destruct i; simpl in *; [reflexivity|].
    apply IH; lia.
Qed.

(** get_word after set_word at different index *)
Lemma get_set_word_other : forall ws i j v,
  i <> j ->
  get_word (set_word ws i v) j = get_word ws j.
Proof.
  induction ws as [|w rest IH]; intros i j v Hij.
  - simpl. reflexivity.
  - destruct i; destruct j; auto; try lia.
    simpl. apply IH. lia.
Qed.

(** Length of extend_words *)
Lemma extend_words_length : forall n,
  length (extend_words n) = n.
Proof.
  unfold extend_words; auto using repeat_length.
Qed.

(** get_word from extend_words returns 0 *)
Lemma get_extend_words : forall n i,
  (i < n)%nat ->
  get_word (extend_words n) i = 0.
Proof.
  intros n i Hi.
  unfold get_word, extend_words.
  apply nth_repeat.
Qed.

(** extend_words has valid words (all zeros) *)
Lemma extend_words_valid : forall n,
  words_valid (extend_words n).
Proof.
  intros n. unfold extend_words, words_valid.
  apply Forall_forall. intros x Hx.
  apply repeat_spec in Hx. subst.
  unfold modulus64; lia.
Qed.

(** to_Z_words of extend_words is 0 *)
Lemma to_Z_extend_words : forall n,
  to_Z_words (extend_words n) = 0.
Proof.
  intros n. induction n as [|n' IH].
  - simpl. reflexivity.
  - unfold extend_words in *; cbn [repeat to_Z_words].
    unfold to_Z64. rewrite IH. lia.
Qed.

(** to_Z_words of appended single word *)
Lemma to_Z_words_app_single : forall ws w,
  to_Z_words (ws ++ [w]) = to_Z_words ws + to_Z64 w * 2^(64 * Z.of_nat (length ws)).
Proof.
  induction ws as [|w0 rest IH]; intros w.
  - cbn [app to_Z_words length Z.of_nat Z.mul Z.pow_pos Pos.mul].
    unfold to_Z64. ring.
  - cbn [app to_Z_words length]. rewrite IH. unfold to_Z64.
    rewrite Nat2Z.inj_succ.
    replace (64 * Z.succ (Z.of_nat (length rest)))
      with (64 + 64 * Z.of_nat (length rest)) by lia.
    rewrite Z.pow_add_r by lia. ring.
Qed.

(** ** Word List Mathematical Properties *)

(** Contribution of setting word i to v *)
Lemma to_Z_words_set_word : forall ws i v,
  (i < length ws)%nat ->
  words_valid ws ->
  0 <= v < modulus64 ->
  to_Z_words (set_word ws i v) =
    to_Z_words ws - to_Z64 (get_word ws i) * 2^(64 * Z.of_nat i) +
    to_Z64 v * 2^(64 * Z.of_nat i).
Proof.
  induction ws as [|w rest IH]; intros i v Hi Hvalid Hv.
  - simpl in Hi. lia.
  - destruct i.
    + cbn [set_word get_word to_Z_words nth Z.of_nat Z.mul Z.pow_pos Pos.mul].
      unfold to_Z64. ring.
    + simpl in Hi.
      inversion Hvalid as [|w' rest' Hw Hrest]; subst.
      cbn [set_word to_Z_words get_word nth].
      rewrite IH by (try lia; assumption).
      unfold get_word, to_Z64.
      rewrite Nat2Z.inj_succ.
      replace (64 * Z.succ (Z.of_nat i)) with (64 + 64 * Z.of_nat i) by lia.
      rewrite Z.pow_add_r by lia.
      ring.
Qed.
