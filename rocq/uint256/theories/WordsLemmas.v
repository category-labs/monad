(** * Lemmas for Multi-Word Unsigned Integers

    The [Make] functor (parameterized by [Uint64Ops]) proves
    structural properties of the [words] operations from Words.v:

    - [set_word_length]: set_word preserves list length
    - [get_set_word_same] / [get_set_word_other]: get after set
    - [extend_words_length] / [get_extend_words]: properties of
      zero-padded word lists

    Legacy concrete lemmas (using Z-level [to_Z_words],
    [words_valid], etc.) are retained below the functor.  *)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Uint Primitives Words.
From Stdlib Require Import DoubleType.
Import ListNotations.

Module Make (Import U64 : Uint64Ops).
Include UintNotations(U64).
Include Words.Make(U64).
Open Scope uint_scope.
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

End Make.

(** ** Abstract proof functor — [to_Z_words] and Z-level reasoning *)

Module MakeProofs (Import U64 : Uint64).
Include Make(U64).

#[local] Open Scope Z_scope.

(** Interpretation of a word list as a multi-word integer (little-endian) *)
Fixpoint to_Z_words (ws : words) : Z :=
  match ws with
  | [] => 0
  | w :: rest => to_Z w + (base width) * to_Z_words rest
  end.

(** Modulus for an n-word number: [(base width) ^ n] *)
Definition modulus_words (n : nat) : Z := (base width) ^ (Z.of_nat n).

Lemma modulus_words_0 : modulus_words 0 = 1%Z.
Proof. unfold modulus_words. reflexivity. Qed.

Lemma modulus_words_succ : forall n,
  modulus_words (S n) = base width * modulus_words n.
Proof.
  intros. unfold modulus_words.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. reflexivity.
Qed.

(** Every word is bounded by [spec_to_Z] *)
Lemma get_word_bounded : forall ws i,
  (i < length ws)%nat ->
  0 <= to_Z (get_word ws i) < (base width).
Proof.
  intros ws i Hi.
  apply spec_to_Z.
Qed.

(** Bound on multi-word value *)
Lemma to_Z_words_bound : forall ws,
  0 <= to_Z_words ws < modulus_words (length ws).
Proof.
  induction ws as [| w rest IH].
  - unfold modulus_words. simpl. lia.
  - cbn [to_Z_words length].
    pose proof (spec_to_Z w) as Hw.
    unfold modulus_words in *. cbn [length].
    rewrite Nat2Z.inj_succ.
    replace ((base width) ^ Z.succ (Z.of_nat (length rest)))
      with ((base width) * (base width) ^ Z.of_nat (length rest))
      by (rewrite Z.pow_succ_r by lia; ring).
    nia.
Qed.

(** [to_Z_words] of zero-padded word list is 0 *)
Lemma to_Z_extend_words : forall n,
  to_Z_words (extend_words n) = 0.
Proof.
  intros n. induction n as [|n' IH].
  - simpl. reflexivity.
  - unfold extend_words in *. cbn [repeat to_Z_words].
    rewrite spec_zero. rewrite IH. lia.
Qed.

(** [get_word] from [extend_words] returns [zero] *)
Lemma get_extend_words_zero : forall n i,
  (i < n)%nat ->
  get_word (extend_words n) i = zero.
Proof.
  intros n i Hi.
  unfold get_word, extend_words.
  apply nth_repeat.
Qed.

(** [to_Z] of [get_word] from [extend_words] is 0 *)
Lemma get_extend_words_Z : forall n i,
  (i < n)%nat ->
  to_Z (get_word (extend_words n) i) = 0.
Proof.
  intros n i Hi.
  rewrite get_extend_words_zero by exact Hi.
  apply spec_zero.
Qed.

(** Setting word [i] changes the value by replacing the [i]-th digit *)
Lemma to_Z_words_set_word : forall ws i v,
  (i < length ws)%nat ->
  to_Z_words (set_word ws i v) =
    to_Z_words ws - to_Z (get_word ws i) * (base width) ^ (Z.of_nat i) +
    to_Z v * (base width) ^ (Z.of_nat i).
Proof.
  induction ws as [|w rest IH]; intros i v Hi.
  - simpl in Hi. lia.
  - destruct i.
    + cbn [set_word get_word to_Z_words nth].
      simpl Z.of_nat. rewrite Z.pow_0_r. ring.
    + simpl in Hi.
      cbn [set_word to_Z_words get_word nth].
      rewrite IH by lia.
      rewrite Nat2Z.inj_succ.
      rewrite Z.pow_succ_r by lia.
      set (P := (base width) ^ Z.of_nat i). unfold get_word. nia.
Qed.

(** [to_Z_words] of appended single word *)
Lemma to_Z_words_app_single : forall ws w,
  to_Z_words (ws ++ [w]) =
    to_Z_words ws + to_Z w * modulus_words (length ws).
Proof.
  induction ws as [|w0 rest IH]; intros w.
  - cbn [app to_Z_words length Z.of_nat]. rewrite modulus_words_0. ring.
  - cbn [app to_Z_words length]. rewrite IH.
    rewrite modulus_words_succ.
    ring.
Qed.

End MakeProofs.

(*
(** Convert a word list to its mathematical value (little-endian) *)
Fixpoint to_Z_words (ws : words) : Z :=
  match ws with
  | [] => 0
  | w :: rest => to_Z w + 2^64 * to_Z_words rest
  end.

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

(** Equivalence lemma: uint256 and word list representations agree *)
(* TODO: Remove once we have expunged uint256 from the rest of the
   development in favour of the words type. *)
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
  to_Z_words (set_word ws i v) =P
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
*)
