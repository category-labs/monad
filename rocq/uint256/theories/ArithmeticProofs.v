(** * Arithmetic Correctness Proof Skeleton

    Boilerplate correctness statements for the composite arithmetic
    definitions in [Arithmetic.v].

    The intent is to phrase the main theorems against the same semantic
    layer used elsewhere in the development:

    - [WL.to_Z_words] for unsigned values
    - [modulus_words 4] for the 256-bit modulus
    - [Z.quot] / [Z.rem] for signed division and remainder

    This file is intentionally a scaffold: small structural facts are
    proved here, while the main semantic theorems are left as proof
    obligations to be filled in incrementally. *)

From Stdlib Require Import ZArith Lia List Bool.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint Words WordsLemmas Arithmetic.
From Uint256 Require Import DivisionProofs RuntimeMulProofs.

Import ListNotations.

Module MakeProofs (Import U64 : Uint64) (U128 : Uint128)
  (Import Bridge : UintWiden U64 U128).
Include Arithmetic.Make(U64)(U128)(Bridge).
Module WL := WordsLemmas.MakeProofs(U64).
Module DP := DivisionProofs.MakeProofs(U64)(U128)(Bridge).
Module RMP := RuntimeMulProofs.MakeProofs(U64).

Open Scope Z_scope.

Local Coercion to_Z : t >-> Z.

Local Definition to_Z_words := WL.to_Z_words.
Local Definition modulus_words := WL.modulus_words.

Definition modulus256 : Z := modulus_words 4.

Definition sign_threshold256 : Z := modulus256 / 2.

Definition to_Z_uint256 (x : uint256) : Z :=
  to_Z_words (uint256_to_words x).

Definition to_Z_signed_uint256 (x : uint256) : Z :=
  let ux := to_Z_uint256 x in
  if Z.ltb ux sign_threshold256 then ux else ux - modulus256.

Definition to_Z_signed_words (ws : words) : Z :=
  to_Z_signed_uint256 (words_to_uint256 ws).

Lemma uint256_to_words_length : forall x,
  length (uint256_to_words x) = 4%nat.
Proof.
  intros [x0 x1 x2 x3]. reflexivity.
Qed.

Lemma words_to_uint256_roundtrip : forall x,
  words_to_uint256 (uint256_to_words x) = x.
Proof.
  intros [x0 x1 x2 x3]. reflexivity.
Qed.

Lemma to_Z_uint256_bounds : forall x,
  0 <= to_Z_uint256 x < modulus256.
Proof.
  intro x.
  unfold to_Z_uint256, modulus256.
  apply WL.to_Z_words_bound.
Qed.

Lemma to_Z_zero_uint256 :
  to_Z_uint256 zero_uint256 = 0.
Proof.
  unfold to_Z_uint256, zero_uint256, uint256_to_words, to_Z_words.
  cbn.
  rewrite !spec_zero.
  lia.
Qed.

Lemma to_Z_one_uint256 :
  to_Z_uint256 one_uint256 = 1.
Proof.
  unfold to_Z_uint256, one_uint256, uint256_to_words, to_Z_words.
  cbn.
  rewrite spec_one.
  rewrite !spec_zero.
  lia.
Qed.

Lemma to_Z_two_uint256 :
  to_Z_uint256 two_uint256 = 2.
Proof.
  unfold to_Z_uint256, two_uint256, uint256_to_words, to_Z_words.
  cbn.
  rewrite spec_add, !spec_one.
  rewrite !spec_zero.
  rewrite Z.mul_0_r, Z.add_0_r.
  rewrite Z.mod_small.
  - lia.
  - unfold base. rewrite width_is_64. simpl. lia.
Qed.

Lemma base_width_gt_1 : 1 < base width.
Proof.
  unfold base. rewrite width_is_64. simpl. lia.
Qed.

Lemma mod_carry_decompose : forall B n,
  0 < B -> 0 <= n < 2 * B ->
  n mod B + (if B <=? n then B else 0) = n.
Proof.
  intros B n HB Hn.
  destruct (Z_lt_ge_dec n B) as [Hsmall|Hcarry].
  - rewrite Z.mod_small by lia.
    destruct (Z.leb_spec0 B n); lia.
  - assert (HBnz : B <> 0) by lia.
    pose proof (Z.mod_pos_bound n B HB) as Hm.
    pose proof (Z.div_mod n B HBnz) as Hdiv.
    assert (Hq : n / B = 1) by nia.
    destruct (Z.leb_spec0 B n); nia.
Qed.

Lemma carry_second_false_if_first_true : forall B x y c,
  1 < B ->
  0 <= x < B -> 0 <= y < B ->
  (c = 0 \/ c = 1) ->
  B <= x + y ->
  (x + y) mod B + c < B.
Proof.
  intros B x y c HB Hx Hy Hc Hcarry.
  assert (Hsum : x + y < 2 * B) by nia.
  assert (HBpos : 0 < B) by lia.
  assert (HBnz : B <> 0) by lia.
  pose proof (Z.mod_pos_bound (x + y) B HBpos) as Hm.
  pose proof (Z.div_mod (x + y) B HBnz) as Hdiv.
  assert (Hq : (x + y) / B = 1) by nia.
  destruct Hc as [Hc|Hc]; subst c; nia.
Qed.

Lemma addc_carry_bool : forall B x y c,
  1 < B ->
  0 <= x < B -> 0 <= y < B ->
  (c = 0 \/ c = 1) ->
  ((B <=? x + y) || (B <=? (x + y) mod B + c)) = (B <=? x + y + c).
Proof.
  intros B x y c HB Hx Hy Hc.
  destruct (Z.leb_spec0 B (x + y)) as [Hcarry|Hnocarry].
  - assert (Hsecond : (x + y) mod B + c < B).
    { apply carry_second_false_if_first_true; try lia. }
    destruct (Z.leb_spec0 B ((x + y) mod B + c));
      destruct (Z.leb_spec0 B (x + y + c));
      simpl; try reflexivity; try lia.
  - assert (Hsmall : x + y < B) by lia.
    assert (Hmod : (x + y) mod B = x + y) by (apply Z.mod_small; lia).
    rewrite Hmod.
    reflexivity.
Qed.

Lemma addc_full_generic : forall B x y c,
  1 < B ->
  0 <= x < B ->
  0 <= y < B ->
  (c = 0 \/ c = 1) ->
  ((x + y) mod B + c) mod B +
    (if ((B <=? x + y) || (B <=? (x + y) mod B + c)) then B else 0) =
  x + y + c.
Proof.
  intros B x y c HB Hx Hy Hc.
  rewrite addc_carry_bool by assumption.
  rewrite Zplus_mod_idemp_l.
  apply mod_carry_decompose.
  - lia.
  - destruct Hc as [Hc|Hc]; subst c; nia.
Qed.

Lemma wrapped_add_ltb_left : forall B x y,
  1 < B ->
  0 <= x < B ->
  0 <= y < B ->
  ((x + y) mod B <? x) = (B <=? x + y).
Proof.
  intros B x y HB Hx Hy.
  destruct (B <=? x + y) eqn:Hcarry.
  - apply Z.leb_le in Hcarry.
    apply Z.ltb_lt.
    assert (Hmod : (x + y) mod B = x + y - B).
    { symmetry. apply Z.mod_unique with (q := 1); lia. }
    rewrite Hmod. lia.
  - apply Z.leb_gt in Hcarry.
    apply Z.ltb_ge.
    rewrite Z.mod_small by lia.
    lia.
Qed.

Lemma addc64_full_correct_word : forall lhs rhs carry_in,
  to_Z (value64 (addc64 lhs rhs carry_in)) +
    (if carry64 (addc64 lhs rhs carry_in) then base width else 0) =
  to_Z lhs + to_Z rhs + if carry_in then 1 else 0.
Proof.
  intros lhs rhs carry_in.
  unfold addc64.
  cbn [value64 carry64].
  remember ((lhs + rhs)%Uint) as sum eqn:Hsum.
  remember ((sum + of_bool carry_in)%Uint) as sum_carry eqn:Hsum_carry.
  pose proof (spec_to_Z lhs) as Hlhs.
  pose proof (spec_to_Z rhs) as Hrhs.
  assert (HsumZ : to_Z sum = (to_Z lhs + to_Z rhs) mod base width).
  { subst sum. apply spec_add. }
  assert (Hsum_bound : 0 <= to_Z sum < base width).
  { subst sum. apply spec_to_Z. }
  assert (HcarryZ : 0 <= (if carry_in then 1 else 0) < base width).
  { destruct carry_in; split; try lia; apply base_width_gt_1. }
  assert (Hsum_carryZ :
    to_Z sum_carry = (to_Z sum + if carry_in then 1 else 0) mod base width).
  { subst sum_carry. rewrite spec_add, spec_of_bool. reflexivity. }
  rewrite !spec_ltb.
  rewrite Hsum_carryZ.
  rewrite (wrapped_add_ltb_left
    (base width) (to_Z sum) (if carry_in then 1 else 0)
    (base_width_gt_1) Hsum_bound HcarryZ).
  rewrite HsumZ.
  rewrite (wrapped_add_ltb_left (base width) (to_Z lhs) (to_Z rhs)
    (base_width_gt_1) Hlhs Hrhs).
  apply addc_full_generic.
  - apply base_width_gt_1.
  - exact Hlhs.
  - exact Hrhs.
  - destruct carry_in; auto.
Qed.

Lemma addc64_carry_correct_word : forall lhs rhs carry_in,
  carry64 (addc64 lhs rhs carry_in) =
    Z.leb (base width) (to_Z lhs + to_Z rhs + if carry_in then 1 else 0).
Proof.
  intros lhs rhs carry_in.
  unfold addc64.
  cbn [carry64].
  remember ((lhs + rhs)%Uint) as sum eqn:Hsum.
  remember ((sum + of_bool carry_in)%Uint) as sum_carry eqn:Hsum_carry.
  pose proof (spec_to_Z lhs) as Hlhs.
  pose proof (spec_to_Z rhs) as Hrhs.
  assert (HsumZ : to_Z sum = (to_Z lhs + to_Z rhs) mod base width).
  { subst sum. apply spec_add. }
  assert (Hsum_bound : 0 <= to_Z sum < base width).
  { subst sum. apply spec_to_Z. }
  assert (HcarryZ : 0 <= (if carry_in then 1 else 0) < base width).
  { destruct carry_in; split; try lia; apply base_width_gt_1. }
  assert (Hsum_carryZ :
    to_Z sum_carry = (to_Z sum + if carry_in then 1 else 0) mod base width).
  { subst sum_carry. rewrite spec_add, spec_of_bool. reflexivity. }
  rewrite !spec_ltb.
  rewrite Hsum_carryZ.
  rewrite (wrapped_add_ltb_left
    (base width) (to_Z sum) (if carry_in then 1 else 0)
    (base_width_gt_1) Hsum_bound HcarryZ).
  rewrite HsumZ.
  rewrite (wrapped_add_ltb_left (base width) (to_Z lhs) (to_Z rhs)
    (base_width_gt_1) Hlhs Hrhs).
  apply addc_carry_bool.
  - apply base_width_gt_1.
  - exact Hlhs.
  - exact Hrhs.
  - destruct carry_in; auto.
Qed.

(** ** 256-bit add/sub *)

Lemma addc_full_correct_aux : forall x y,
  to_Z_uint256 (value256 (addc x y)) +
    (if carry256 (addc x y) then modulus256 else 0) =
    to_Z_uint256 x + to_Z_uint256 y.
Proof.
  intros [x0 x1 x2 x3] [y0 y1 y2 y3].
  unfold addc, to_Z_uint256, modulus256, to_Z_words, modulus_words.
  cbn - [addc64].
  set (r0 := addc64 x0 y0 false).
  set (r1 := addc64 x1 y1 (carry64 r0)).
  set (r2 := addc64 x2 y2 (carry64 r1)).
  set (r3 := addc64 x3 y3 (carry64 r2)).
  pose proof (addc64_full_correct_word x0 y0 false) as H0.
  fold r0 in H0.
  pose proof (addc64_full_correct_word x1 y1 (carry64 r0)) as H1.
  fold r1 in H1.
  pose proof (addc64_full_correct_word x2 y2 (carry64 r1)) as H2.
  fold r2 in H2.
  pose proof (addc64_full_correct_word x3 y3 (carry64 r2)) as H3.
  fold r3 in H3.
  destruct (carry64 r0), (carry64 r1), (carry64 r2), (carry64 r3);
    simpl in H0, H1, H2, H3 |- *;
    ring_simplify in H0;
    ring_simplify in H1;
    ring_simplify in H2;
    ring_simplify in H3;
    ring_simplify;
    lia.
Qed.

Theorem addc_value_correct : forall x y,
  to_Z_uint256 (value256 (addc x y)) =
    (to_Z_uint256 x + to_Z_uint256 y) mod modulus256.
Proof.
  intros x y.
  set (v := to_Z_uint256 (value256 (addc x y))) in *.
  set (s := to_Z_uint256 x + to_Z_uint256 y) in *.
  pose proof (addc_full_correct_aux x y) as Hfull.
  fold v in Hfull.
  fold s in Hfull.
  pose proof (to_Z_uint256_bounds (value256 (addc x y))) as Hbound.
  fold v in Hbound.
  destruct (carry256 (addc x y)) eqn:Hcarry.
  - simpl in Hfull.
    apply Z.mod_unique with (q := 1).
    + left. exact Hbound.
    + rewrite Z.mul_1_r. rewrite Z.add_comm. exact (eq_sym Hfull).
  - simpl in Hfull.
    rewrite <- Hfull.
    rewrite Z.add_0_r.
    symmetry.
    apply Z.mod_small.
    exact Hbound.
Qed.

Theorem addc_carry_correct : forall x y,
  carry256 (addc x y) =
    Z.leb modulus256 (to_Z_uint256 x + to_Z_uint256 y).
Proof.
  intros x y.
  set (v := to_Z_uint256 (value256 (addc x y))) in *.
  set (s := to_Z_uint256 x + to_Z_uint256 y) in *.
  pose proof (addc_full_correct_aux x y) as Hfull.
  fold v in Hfull.
  fold s in Hfull.
  pose proof (to_Z_uint256_bounds (value256 (addc x y))) as Hbound.
  fold v in Hbound.
  destruct (carry256 (addc x y)) eqn:Hcarry.
  - simpl in Hfull.
    symmetry.
    apply Z.leb_le.
    lia.
  - simpl in Hfull.
    symmetry.
    apply Z.leb_gt.
    lia.
Qed.

Theorem addc_full_correct : forall x y,
  to_Z_uint256 (value256 (addc x y)) +
    (if carry256 (addc x y) then modulus256 else 0) =
    to_Z_uint256 x + to_Z_uint256 y.
Proof.
  apply addc_full_correct_aux.
Qed.

Lemma subb_borrow_bool : forall B x y c,
  1 < B ->
  0 <= x < B ->
  0 <= y < B ->
  (c = 0 \/ c = 1) ->
  ((x <? y) || ((x - y) mod B <? c)) = (x <? y + c).
Proof.
  intros B x y c HB Hx Hy Hc.
  destruct Hc as [Hc|Hc]; subst c.
  - replace (y + 0) with y by lia.
    assert (Hmod : ((x - y) mod B <? 0) = false).
    { apply Z.ltb_ge. pose proof (Z.mod_pos_bound (x - y) B). lia. }
    rewrite Hmod, orb_false_r. reflexivity.
  - destruct (x <? y) eqn:Hxy.
    + apply Z.ltb_lt in Hxy.
      simpl.
      symmetry.
      apply Z.ltb_lt.
      lia.
    + apply Z.ltb_ge in Hxy.
      simpl.
      assert (Hmod : (x - y) mod B = x - y).
      { apply Z.mod_small. lia. }
      rewrite Hmod.
      destruct (Z.ltb_spec0 (x - y) 1);
        destruct (Z.ltb_spec0 x (y + 1)); simpl; lia.
Qed.

Lemma mod_borrow_decompose : forall B n,
  0 < B ->
  - B <= n < B ->
  n mod B - (if n <? 0 then B else 0) = n.
Proof.
  intros B n HB Hn.
  destruct (n <? 0) eqn:Hneg.
  - apply Z.ltb_lt in Hneg.
    assert (Hmod : n mod B = n + B).
    { symmetry. apply Z.mod_unique with (q := -1); lia. }
    rewrite Hmod. lia.
  - apply Z.ltb_ge in Hneg.
    rewrite Z.mod_small by lia. lia.
Qed.

Lemma subb_full_generic : forall B x y c,
  1 < B ->
  0 <= x < B ->
  0 <= y < B ->
  (c = 0 \/ c = 1) ->
  ((x - y) mod B - c) mod B -
    (if ((x <? y) || ((x - y) mod B <? c)) then B else 0) =
  x - y - c.
Proof.
  intros B x y c HB Hx Hy Hc.
  rewrite subb_borrow_bool by assumption.
  rewrite Zminus_mod_idemp_l.
  assert (Hlt : (x <? y + c) = (x - y - c <? 0)).
  { destruct (Z.ltb_spec0 x (y + c));
      destruct (Z.ltb_spec0 (x - y - c) 0); simpl; lia. }
  rewrite Hlt.
  apply mod_borrow_decompose.
  - lia.
  - destruct Hc as [Hc|Hc]; subst c; lia.
Qed.

Lemma subb64_full_correct_word : forall lhs rhs borrow_in,
  to_Z (value64 (subb64 lhs rhs borrow_in)) -
    (if carry64 (subb64 lhs rhs borrow_in) then base width else 0) =
  to_Z lhs - to_Z rhs - if borrow_in then 1 else 0.
Proof.
  intros lhs rhs borrow_in.
  unfold subb64.
  cbn [value64 carry64].
  remember ((lhs - rhs)%Uint) as sub eqn:Hsub.
  remember ((sub - of_bool borrow_in)%Uint) as sub_borrow eqn:Hsub_borrow.
  pose proof (spec_to_Z lhs) as Hlhs.
  pose proof (spec_to_Z rhs) as Hrhs.
  assert (HsubZ : to_Z sub = (to_Z lhs - to_Z rhs) mod base width).
  { subst sub. apply spec_sub. }
  assert (Hsub_borrowZ :
    to_Z sub_borrow =
      (to_Z sub - if borrow_in then 1 else 0) mod base width).
  { subst sub_borrow. rewrite spec_sub, spec_of_bool. reflexivity. }
  rewrite !spec_gtb.
  rewrite !Z.gtb_ltb.
  rewrite spec_of_bool.
  rewrite Hsub_borrowZ, HsubZ.
  apply subb_full_generic.
  - apply base_width_gt_1.
  - exact Hlhs.
  - exact Hrhs.
  - destruct borrow_in; auto.
Qed.

Lemma subb64_borrow_correct_word : forall lhs rhs borrow_in,
  carry64 (subb64 lhs rhs borrow_in) =
    Z.ltb (to_Z lhs - to_Z rhs - if borrow_in then 1 else 0) 0.
Proof.
  intros lhs rhs borrow_in.
  unfold subb64.
  cbn [carry64].
  remember ((lhs - rhs)%Uint) as sub eqn:Hsub.
  pose proof (spec_to_Z lhs) as Hlhs.
  pose proof (spec_to_Z rhs) as Hrhs.
  assert (HsubZ : to_Z sub = (to_Z lhs - to_Z rhs) mod base width).
  { subst sub. apply spec_sub. }
  rewrite !spec_gtb.
  rewrite !Z.gtb_ltb.
  rewrite spec_of_bool.
  rewrite HsubZ.
  rewrite subb_borrow_bool.
  - assert (Hlt :
      (to_Z lhs <? to_Z rhs + if borrow_in then 1 else 0) =
      ((to_Z lhs - to_Z rhs - if borrow_in then 1 else 0) <? 0)).
    { destruct (Z.ltb_spec0 (to_Z lhs)
          (to_Z rhs + if borrow_in then 1 else 0));
        destruct (Z.ltb_spec0
          (to_Z lhs - to_Z rhs - if borrow_in then 1 else 0) 0);
        simpl; lia. }
    exact Hlt.
  - apply base_width_gt_1.
  - exact Hlhs.
  - exact Hrhs.
  - destruct borrow_in; auto.
Qed.

Lemma subb_full_correct_aux : forall x y,
  to_Z_uint256 (value256 (subb x y)) -
    (if carry256 (subb x y) then modulus256 else 0) =
    to_Z_uint256 x - to_Z_uint256 y.
Proof.
  intros [x0 x1 x2 x3] [y0 y1 y2 y3].
  unfold subb, to_Z_uint256, modulus256, to_Z_words, modulus_words.
  cbn - [subb64].
  set (r0 := subb64 x0 y0 false).
  set (r1 := subb64 x1 y1 (carry64 r0)).
  set (r2 := subb64 x2 y2 (carry64 r1)).
  set (r3 := subb64 x3 y3 (carry64 r2)).
  pose proof (subb64_full_correct_word x0 y0 false) as H0.
  fold r0 in H0.
  pose proof (subb64_full_correct_word x1 y1 (carry64 r0)) as H1.
  fold r1 in H1.
  pose proof (subb64_full_correct_word x2 y2 (carry64 r1)) as H2.
  fold r2 in H2.
  pose proof (subb64_full_correct_word x3 y3 (carry64 r2)) as H3.
  fold r3 in H3.
  destruct (carry64 r0), (carry64 r1), (carry64 r2), (carry64 r3);
    simpl in H0, H1, H2, H3 |- *;
    ring_simplify in H0;
    ring_simplify in H1;
    ring_simplify in H2;
    ring_simplify in H3;
    ring_simplify;
    lia.
Qed.

Theorem subb_value_correct : forall x y,
  to_Z_uint256 (value256 (subb x y)) =
    (to_Z_uint256 x - to_Z_uint256 y) mod modulus256.
Proof.
  intros x y.
  set (v := to_Z_uint256 (value256 (subb x y))) in *.
  set (s := to_Z_uint256 x - to_Z_uint256 y) in *.
  pose proof (subb_full_correct_aux x y) as Hfull.
  fold v in Hfull.
  fold s in Hfull.
  pose proof (to_Z_uint256_bounds (value256 (subb x y))) as Hbound.
  fold v in Hbound.
  destruct (carry256 (subb x y)) eqn:Hcarry.
  - simpl in Hfull.
    apply Z.mod_unique with (q := -1).
    + left. exact Hbound.
    + lia.
  - simpl in Hfull.
    rewrite <- Hfull.
    rewrite Z.sub_0_r.
    symmetry.
    apply Z.mod_small.
    exact Hbound.
Qed.

Theorem subb_borrow_correct : forall x y,
  carry256 (subb x y) = Z.ltb (to_Z_uint256 x) (to_Z_uint256 y).
Proof.
  intros x y.
  set (v := to_Z_uint256 (value256 (subb x y))) in *.
  set (s := to_Z_uint256 x - to_Z_uint256 y) in *.
  pose proof (subb_full_correct_aux x y) as Hfull.
  fold v in Hfull.
  fold s in Hfull.
  pose proof (to_Z_uint256_bounds (value256 (subb x y))) as Hbound.
  fold v in Hbound.
  destruct (carry256 (subb x y)) eqn:Hcarry.
  - simpl in Hfull.
    symmetry.
    apply Z.ltb_lt.
    lia.
  - simpl in Hfull.
    symmetry.
    apply Z.ltb_ge.
    lia.
Qed.

Theorem subb_full_correct : forall x y,
  to_Z_uint256 (value256 (subb x y)) -
    (if carry256 (subb x y) then modulus256 else 0) =
    to_Z_uint256 x - to_Z_uint256 y.
Proof.
  apply subb_full_correct_aux.
Qed.

Theorem ltb_uint256_correct : forall x y,
  ltb_uint256 x y = Z.ltb (to_Z_uint256 x) (to_Z_uint256 y).
Proof.
  intros x y.
  unfold ltb_uint256.
  apply subb_borrow_correct.
Qed.

Theorem add_words_full_uint256_correct : forall x y,
  to_Z_words (add_words_full_uint256 x y) =
    to_Z_uint256 x + to_Z_uint256 y.
Proof.
  intros x y.
  unfold add_words_full_uint256.
  rewrite WL.to_Z_words_app_single.
  rewrite uint256_to_words_length.
  change (modulus_words 4) with modulus256.
  rewrite spec_of_bool.
  pose proof (addc_full_correct_aux x y) as H.
  unfold to_Z_uint256 in H.
  destruct (carry256 (addc x y)); simpl in H;
    rewrite ?Z.mul_0_r, ?Z.mul_1_l;
    exact H.
Qed.
Theorem addmod_None_iff : forall x y modulus,
  addmod x y modulus = None <->
  to_Z_uint256 modulus = 0.
Admitted.

Theorem addmod_correct : forall x y modulus r,
  0 < to_Z_uint256 modulus ->
  addmod x y modulus = Some r ->
  to_Z_uint256 r =
    (to_Z_uint256 x + to_Z_uint256 y) mod to_Z_uint256 modulus /\
  0 <= to_Z_uint256 r < to_Z_uint256 modulus.
Admitted.

Theorem mulmod_None_iff : forall x y modulus,
  mulmod x y modulus = None <->
  to_Z_uint256 modulus = 0.
Admitted.

Theorem mulmod_correct : forall x y modulus r,
  0 < to_Z_uint256 modulus ->
  mulmod x y modulus = Some r ->
  to_Z_uint256 r =
    (to_Z_uint256 x * to_Z_uint256 y) mod to_Z_uint256 modulus /\
  0 <= to_Z_uint256 r < to_Z_uint256 modulus.
Admitted.

(** ** Signed helpers *)

Theorem negate_uint256_correct : forall x,
  to_Z_uint256 (negate_uint256 x) =
    (- to_Z_uint256 x) mod modulus256.
Proof.
  intro x.
  unfold negate_uint256.
  rewrite subb_value_correct.
  rewrite to_Z_zero_uint256.
  change ((0 - to_Z_uint256 x) mod modulus256)
    with ((- to_Z_uint256 x) mod modulus256).
  reflexivity.
Qed.

Theorem negate_words_correct : forall ws,
  length ws = 4%nat ->
  to_Z_words (negate_words ws) =
    (- to_Z_words ws) mod modulus256.
Proof.
  intros ws Hlen.
  destruct ws as [|w0 [|w1 [|w2 [|w3 [|w4 ws']]]]];
    simpl in Hlen; try discriminate.
  inversion Hlen; subst; clear Hlen.
  unfold negate_words.
  simpl.
  pose proof (subb_value_correct zero_uint256 (mk_uint256 w0 w1 w2 w3)) as H.
  rewrite to_Z_zero_uint256 in H.
  unfold to_Z_uint256 in H.
  simpl in H.
  change ((0 - to_Z_words [w0; w1; w2; w3]) mod modulus256)
    with ((- to_Z_words [w0; w1; w2; w3]) mod modulus256) in H.
  exact H.
Qed.
Lemma to_Z_sign_bit : to_Z sign_bit = 2 ^ 63.
Proof.
  unfold sign_bit, word_width.
  rewrite width_is_64.
  rewrite spec_shl, spec_one.
  rewrite width_is_64.
  rewrite Z.shiftl_mul_pow2 by lia.
  unfold base.
  rewrite Z.mod_small.
  - reflexivity.
  - split.
    + apply Z.mul_nonneg_nonneg; lia.
    + change (1 * 2 ^ 63 < 2 ^ 64).
      replace (1 * 2 ^ 63) with (2 ^ 63) by lia.
      apply Z.pow_lt_mono_r; lia.
Qed.

Lemma sign_threshold256_eq :
  sign_threshold256 = modulus_words 3 * to_Z sign_bit.
Proof.
  unfold sign_threshold256, modulus256, modulus_words, WL.modulus_words.
  rewrite width_is_64.
  rewrite to_Z_sign_bit.
  vm_compute.
  reflexivity.
Qed.
Lemma high_word_ltb_split : forall low hi B s,
  0 <= low < B ->
  0 <= hi ->
  (hi <? s) = (low + B * hi <? B * s).
Proof.
  intros low hi B s Hlow Hhi.
  destruct (Z.ltb_spec0 hi s) as [Hlt|Hge].
  - destruct (Z.ltb_spec0 (low + B * hi) (B * s)) as [Hlt0|Hge0].
    + reflexivity.
    + nia.
  - destruct (Z.ltb_spec0 (low + B * hi) (B * s)) as [Hlt0|Hge0].
    + nia.
    + reflexivity.
Qed.
Theorem is_negative_correct : forall x,
  is_negative x = negb (Z.ltb (to_Z_uint256 x) sign_threshold256).
Admitted.
Lemma modulus256_pos : 0 < modulus256.
Proof.
  pose proof (to_Z_uint256_bounds zero_uint256) as H.
  rewrite to_Z_zero_uint256 in H.
  lia.
Qed.

Lemma count_significant_words_uint256_zero_iff : forall x,
  count_significant_words (uint256_to_words x) = 0%nat <->
  to_Z_uint256 x = 0.
Proof.
  intro x.
  split.
  - intro Hcsw.
    unfold to_Z_uint256.
    apply DP.count_significant_words_zero.
    exact Hcsw.
  - intro Hz.
    destruct (Nat.eq_dec (count_significant_words (uint256_to_words x)) 0)
      as [Hcsw|Hcsw]; [exact Hcsw|].
    pose proof (DP.count_significant_words_lower_bound (uint256_to_words x))
      as Hlb.
    cbv zeta in Hlb.
    assert (Hn : (0 < count_significant_words (uint256_to_words x))%nat)
      by lia.
    specialize (Hlb Hn).
    pose proof (DP.WL.modulus_words_pos
      (DP.count_significant_words (uint256_to_words x) - 1)) as Hpos.
    assert (Hgt : 0 < DP.WL.to_Z_words (uint256_to_words x)).
    { nia. }
    unfold to_Z_uint256, to_Z_words in Hz.
    change (DP.WL.to_Z_words (uint256_to_words x) = 0) in Hz.
    lia.
Qed.

Lemma negate_uint256_zero_iff : forall x,
  to_Z_uint256 (negate_uint256 x) = 0 <->
  to_Z_uint256 x = 0.
Proof.
  intro x.
  split.
  - intro Hneg.
    pose proof (to_Z_uint256_bounds x) as Hx.
    rewrite negate_uint256_correct in Hneg.
    destruct (Z.eq_dec (to_Z_uint256 x) 0) as [Hx0|Hx0]; auto.
    assert (Hxpos : 0 < to_Z_uint256 x) by lia.
    pose proof (mod_borrow_decompose modulus256 (- to_Z_uint256 x)
      modulus256_pos ltac:(lia)) as Hmod.
    assert (Hlt : (- to_Z_uint256 x <? 0) = true).
    { apply Z.ltb_lt. lia. }
    rewrite Hlt in Hmod.
    rewrite Hneg in Hmod.
    lia.
  - intro Hx0.
    rewrite negate_uint256_correct.
    rewrite Hx0, Z.opp_0.
    apply Z.mod_0_l.
    pose proof modulus256_pos.
    lia.
Qed.

Theorem sdivrem_None_iff : forall u v,
  sdivrem u v = None <->
  to_Z_uint256 v = 0.
Admitted.

Theorem sdivrem_correct : forall u v r,
  to_Z_uint256 v <> 0 ->
  sdivrem u v = Some r ->
  to_Z_signed_words (ud_quot r) =
    Z.quot (to_Z_signed_uint256 u) (to_Z_signed_uint256 v) /\
  to_Z_signed_words (ud_rem r) =
    Z.rem (to_Z_signed_uint256 u) (to_Z_signed_uint256 v).
Admitted.

Theorem slt_correct : forall x y,
  slt x y = Z.ltb (to_Z_signed_uint256 x) (to_Z_signed_uint256 y).
Admitted.

(** ** Exponentiation and shifts *)

Theorem shift_left_uint256_aux_correct : forall x shift,
  to_Z_uint256 (shift_left_uint256_aux x shift) =
    if Z.ltb (to_Z shift) 256
    then (to_Z_uint256 x * 2 ^ to_Z shift) mod modulus256
    else 0.
Admitted.

Theorem shift_left_uint256_correct : forall x shift,
  to_Z_uint256 (shift_left_uint256 x shift) =
    if Z.ltb (to_Z_uint256 shift) (base width)
    then if Z.ltb (to_Z_uint256 shift) 256
         then (to_Z_uint256 x * 2 ^ to_Z_uint256 shift) mod modulus256
         else 0
    else 0.
Admitted.

Theorem exp_correct : forall base exponent,
  to_Z_uint256 (exp base exponent) =
    Z.pow (to_Z_uint256 base) (to_Z_uint256 exponent) mod modulus256.
Admitted.

End MakeProofs.
