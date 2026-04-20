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
From Uint256 Require Import Uint Base Words WordsLemmas Arithmetic.
From Uint256 Require Import DivisionProofs RuntimeMulProofs.

Import ListNotations.

Module MakeProofs (B : Base.BaseProofSig) (U128 : Uint128)
  (Import Bridge : UintWiden B.U64 U128)
  (WL : WordsLemmas.WordsLemmasProofSig with Module U64 := B.U64)
  (RM : RuntimeMul.RuntimeMulProofSig with Module U64 := B.U64)
  (RMP : RuntimeMulProofs.RuntimeMulProofsSig(B)(RM)(WL))
  (Div : Division.DivisionProofSig(B)(U128)(Bridge))
  (DP : DivisionProofs.DivisionProofsSig(B)(U128)(Bridge)(Div)(WL))
  (Arith : Arithmetic.ArithmeticSig(B)(U128)(Bridge)(Div)(RM)).
Include Arith.
Import B.U64.

Open Scope Z_scope.

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
  - rewrite Z.mod_small.
  2: { lia. }
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
Lemma to_Z_w3_zero_of_uint256_zero : forall x,
  to_Z_uint256 x = 0 -> to_Z (w3 x) = 0.
Proof.
  intros [x0 x1 x2 x3] Hx.
  pose proof (spec_to_Z x3) as H3.
  assert (Hlb : modulus_words 3 * to_Z x3 <=
    to_Z_uint256 (mk_uint256 x0 x1 x2 x3)).
  {
    unfold to_Z_uint256, to_Z_words.
    cbn.
    unfold modulus_words, WL.modulus_words.
    simpl.
    replace ((base width) ^ 3 * to_Z x3)
      with (base width * (base width * (base width * to_Z x3)))
      by ring.
    pose proof (spec_to_Z x0) as H0.
    pose proof (spec_to_Z x1) as H1.
    pose proof (spec_to_Z x2) as H2.
    nia.
  }
  rewrite Hx in Hlb.
  destruct (Z.eq_dec (to_Z x3) 0) as [Hx3|Hx3]; [exact Hx3|].
  pose proof (WL.modulus_words_pos 3) as Hm.
  change (WL.modulus_words 3) with (modulus_words 3) in Hm.
  assert (Hm_pos : 0 < modulus_words 3) by lia.
  assert (Hx3_pos : 0 < to_Z x3) by lia.
  assert (Hprod : 0 < modulus_words 3 * to_Z x3).
  { apply Z.mul_pos_pos; [exact Hm_pos | exact Hx3_pos]. }
  lia.
Qed.

Lemma udivrem_uint256_divisor_exists : forall M u modulus,
  0 < to_Z_uint256 modulus ->
  exists r, udivrem M 4 u (uint256_to_words modulus) = Some r.
Proof.
  intros M u modulus Hmod.
  unfold udivrem.
  set (m := count_significant_words u).
  set (n := count_significant_words (uint256_to_words modulus)).
  assert (Hn_pos : (0 < n)%nat).
  {
    destruct (Nat.eq_dec n 0) as [Hn0|Hn0]; [|lia].
    subst n.
    pose proof (DP.count_significant_words_zero (uint256_to_words modulus)
      Hn0) as Hz.
    unfold to_Z_uint256 in Hmod.
    change (to_Z_words (uint256_to_words modulus) = 0) in Hz.
    lia.
  }
  destruct (Nat.eqb n 0) eqn:Hn0.
  { apply Nat.eqb_eq in Hn0. lia. }
  destruct (Nat.ltb m n) eqn:Hmn.
  { eexists. reflexivity. }
  destruct (Nat.eqb m 1) eqn:Hm1.
  - apply Nat.eqb_eq in Hm1.
    apply Nat.ltb_ge in Hmn.
    assert (Hn1 : n = 1%nat) by lia.
    subst n.
    pose proof (DP.count_significant_words_msw_nonzero
      (uint256_to_words modulus) Hn_pos) as Hvpos.
    assert (Hn1p : DP.count_significant_words (uint256_to_words modulus) = 1%nat).
    { change (count_significant_words (uint256_to_words modulus) = 1%nat).
      exact Hn1. }
    rewrite Hn1p in Hvpos.
    simpl in Hvpos.
    assert (H0_lt : to_Z zero < to_Z (get_word (uint256_to_words modulus) 0)).
    { change (to_Z zero < to_Z (WL.get_word (uint256_to_words modulus) 0)).
      rewrite spec_zero.
      lia. }
    pose proof (spec_div zero (get_word u 0)
      (get_word (uint256_to_words modulus) 0) Hvpos H0_lt)
      as [q [r0 [Hdiv _]]].
    rewrite Hdiv. eexists. reflexivity.
  - destruct (Nat.eqb n 1) eqn:Hn1.
    + eexists. reflexivity.
    + destruct
        (knuth_div m n
          (shift_left_words (firstn m u)
            (countl_zero (get_word (uint256_to_words modulus) (n - 1))))
          (firstn n
            (shift_left_words (firstn n (uint256_to_words modulus))
              (countl_zero (get_word (uint256_to_words modulus) (n - 1))))))
        as [u_after quot].
      eexists. reflexivity.
Qed.

Theorem addmod_None_iff : forall x y modulus,
(*
In-progress script:
Proof.
  intros x y modulus.
  split.
  - intro Hnone.
    destruct (Z.eq_dec (to_Z_uint256 modulus) 0) as [Hz|Hz]; auto.
    pose proof (to_Z_uint256_bounds modulus) as Hbounds.
    assert (Hmod : 0 < to_Z_uint256 modulus) by lia.
    unfold addmod in Hnone.
    destruct (((negb (w3 modulus =? 0)) && (w3 x <=? w3 modulus)%Uint &&
        (w3 y <=? w3 modulus)%Uint)%bool) eqn:Hguard.
    + (* Stalled here: the fast path reduces to [Some _], but the proof
         script needs a cleaner local contradiction argument than repeated
         [simpl]/[discriminate] against the nested boolean branch. *)
      admit.
    + destruct (udivrem 5 4 (add_words_full_uint256 x y)
        (uint256_to_words modulus)) eqn:Hud; [discriminate|].
      destruct (udivrem_uint256_divisor_exists 5
        (add_words_full_uint256 x y) modulus Hmod) as [r Hr].
      rewrite Hr in Hud. discriminate.
  - intro Hz.
    unfold addmod.
    assert (Hw3 : to_Z (w3 modulus) = 0).
    { apply to_Z_w3_zero_of_uint256_zero. exact Hz. }
    rewrite spec_eqb, Hw3, spec_zero.
    simpl.
    apply <- count_significant_words_uint256_zero_iff in Hz.
    unfold udivrem.
    rewrite Hz.
    reflexivity.
Abort.
*)
  addmod x y modulus = None <->
  to_Z_uint256 modulus = 0.
Proof.
  intros x y modulus.
  split.
  - intro Hnone.
    destruct (Z.eq_dec (to_Z_uint256 modulus) 0) as [Hz|Hz]; auto.
    pose proof (to_Z_uint256_bounds modulus) as Hmod_bound.
    assert (Hmod : 0 < to_Z_uint256 modulus) by lia.
    exfalso.
    destruct (negb (w3 modulus =? 0)%Uint) eqn:Hm;
      destruct (w3 x <=? w3 modulus)%Uint eqn:Hx;
      destruct (w3 y <=? w3 modulus)%Uint eqn:Hy;
      unfold addmod in Hnone; rewrite Hm, Hx, Hy in Hnone;
      cbn zeta in Hnone;
      try (destruct (udivrem 5 4 (add_words_full_uint256 x y)
             (uint256_to_words modulus)) eqn:Hud; [discriminate|];
           destruct (udivrem_uint256_divisor_exists 5
             (add_words_full_uint256 x y) modulus Hmod) as [r Hr];
           rewrite Hr in Hud; discriminate).
    repeat match type of Hnone with
      | context [subb ?a ?b] =>
          let H := fresh "Hsub" in destruct (subb a b) eqn:H
      | context [addc ?a ?b] =>
          let H := fresh "Hadd" in destruct (addc a b) eqn:H
      | context [if ?b then _ else _] =>
          let Hb := fresh "Hb" in destruct b eqn:Hb
      end; discriminate.
  - intro Hz.
    destruct modulus as [m0 m1 m2 m3].
    unfold to_Z_uint256, to_Z_words in Hz.
    cbn [uint256_to_words WL.to_Z_words w0 w1 w2 w3] in Hz.
    pose proof (spec_to_Z m0) as H0.
    pose proof (spec_to_Z m1) as H1.
    pose proof (spec_to_Z m2) as H2.
    pose proof (spec_to_Z m3) as H3.
    unfold base in Hz, H0, H1, H2, H3.
    rewrite !width_is_64 in Hz, H0, H1, H2, H3.
    assert (Hm0 : to_Z m0 = 0).
    { nia. }
    assert (Hm1 : to_Z m1 = 0).
    { nia. }
    assert (Hm2 : to_Z m2 = 0).
    { nia. }
    assert (Hm3 : to_Z m3 = 0).
    { nia. }
    assert (Hcount :
      count_significant_words (uint256_to_words (mk_uint256 m0 m1 m2 m3)) = 0%nat).
    { unfold count_significant_words.
      cbn [uint256_to_words rev skip_leading_zeros app w0 w1 w2 w3].
      rewrite !spec_eqb, Hm0, Hm1, Hm2, Hm3, !spec_zero.
      reflexivity. }
    unfold addmod.
    cbn [w3].
    rewrite spec_eqb, Hm3, spec_zero.
    simpl.
    unfold udivrem.
    rewrite Hcount.
    reflexivity.
Qed.


Lemma to_Z_uint256_split_w3 : forall x,
  to_Z_uint256 x =
    to_Z_words [w0 x; w1 x; w2 x] + modulus_words 3 * to_Z (w3 x).
Proof.
  intros [x0 x1 x2 x3].
  unfold to_Z_uint256, to_Z_words, modulus_words, WL.modulus_words.
  cbn [uint256_to_words WL.to_Z_words].
  nia.
Qed.

Lemma to_Z_uint256_lt_w3_succ : forall x,
  to_Z_uint256 x < modulus_words 3 * (to_Z (w3 x) + 1).
Proof.
  intro x.
  rewrite to_Z_uint256_split_w3.
  pose proof (WL.to_Z_words_bound [w0 x; w1 x; w2 x]) as Hlow.
  change (0 <= to_Z_words [w0 x; w1 x; w2 x] < modulus_words 3) in Hlow.
  nia.
Qed.

Lemma topword_le_lt_double : forall x y,
  0 < to_Z (w3 y) ->
  to_Z (w3 x) <= to_Z (w3 y) ->
  to_Z_uint256 x < 2 * to_Z_uint256 y.
Proof.
  intros x y Hmodhi Hle.
  pose proof (to_Z_uint256_lt_w3_succ x) as Hx.
  pose proof (WL.to_Z_words_bound [w0 y; w1 y; w2 y]) as Hlow.
  change (0 <= to_Z_words [w0 y; w1 y; w2 y] < modulus_words 3) in Hlow.
  pose proof (WL.modulus_words_pos 3) as HB.
  assert (Hstep1 :
    to_Z_uint256 x < modulus_words 3 * (to_Z (w3 y) + 1)) by nia.
  assert (Hstep2 :
    modulus_words 3 * (to_Z (w3 y) + 1) <=
    2 * modulus_words 3 * to_Z (w3 y)) by nia.
  assert (Hstep3 :
    2 * modulus_words 3 * to_Z (w3 y) <= 2 * to_Z_uint256 y).
  {
    rewrite to_Z_uint256_split_w3.
    nia.
  }
  lia.
Qed.

Lemma addmod_fast_path_guard : forall x y modulus,
  ((negb (w3 modulus =? 0)%Uint) && (w3 x <=? w3 modulus)%Uint &&
      (w3 y <=? w3 modulus)%Uint)%bool = true ->
  0 < to_Z (w3 modulus) /\
  to_Z (w3 x) <= to_Z (w3 modulus) /\
  to_Z (w3 y) <= to_Z (w3 modulus).
Proof.
  intros x y modulus Hguard.
  apply andb_prop in Hguard as [Hxy Hyle].
  apply andb_prop in Hxy as [Hnz Hxle].
  apply negb_true_iff in Hnz.
  rewrite (spec_eqb (w3 modulus) 0%Uint), spec_zero in Hnz.
  rewrite (spec_leb (w3 x) (w3 modulus)) in Hxle.
  rewrite (spec_leb (w3 y) (w3 modulus)) in Hyle.
  apply Z.leb_le in Hxle.
  apply Z.leb_le in Hyle.
  destruct (to_Z (w3 modulus) =? 0) eqn:Heq; simpl in Hnz; try discriminate.
  apply Z.eqb_neq in Heq.
  pose proof (spec_to_Z (w3 modulus)) as Hmb.
  split.
  - lia.
  - split; lia.
Qed.

Lemma norm_subb_once_correct : forall x modulus,
  0 < to_Z_uint256 modulus ->
  to_Z_uint256 x < 2 * to_Z_uint256 modulus ->
  to_Z_uint256
    (if carry256 (subb x modulus) then x else value256 (subb x modulus)) =
      to_Z_uint256 x mod to_Z_uint256 modulus /\
  0 <= to_Z_uint256
    (if carry256 (subb x modulus) then x else value256 (subb x modulus)) <
      to_Z_uint256 modulus.
Proof.
  intros x modulus Hmod Hlt.
  pose proof (to_Z_uint256_bounds x) as Hx_bound.
  destruct (carry256 (subb x modulus)) eqn:Hcarry.
  - rewrite subb_borrow_correct in Hcarry.
    apply Z.ltb_lt in Hcarry.
    split.
    + symmetry.
      apply Z.mod_small.
      lia.
    + lia.
  - rewrite subb_borrow_correct in Hcarry.
    apply Z.ltb_ge in Hcarry.
    pose proof (subb_value_correct x modulus) as Hval.
    pose proof (to_Z_uint256_bounds modulus) as Hmod_bound.
    assert (Hsmall :
      0 <= to_Z_uint256 x - to_Z_uint256 modulus < to_Z_uint256 modulus) by lia.
    assert (Hsmall256 :
      0 <= to_Z_uint256 x - to_Z_uint256 modulus < modulus256) by lia.
    rewrite Hval.
    rewrite Z.mod_small by exact Hsmall256.
    split.
    + apply Z.mod_unique with (q := 1); lia.
    + exact Hsmall.
Qed.

(* Lemma addmod_fast_inputs_correct : forall x y modulus, *)
(*   0 < to_Z_uint256 modulus -> *)
(*   ((negb (w3 modulus =? 0)) && (w3 x <=? w3 modulus) && *)
(*       (w3 y <=? w3 modulus))%bool = true -> *)
(*   to_Z_uint256 *)
(*     (if carry256 (subb x modulus) then x else value256 (subb x modulus)) = *)
(*       to_Z_uint256 x mod to_Z_uint256 modulus /\ *)
(*   0 <= to_Z_uint256 *)
(*     (if carry256 (subb x modulus) then x else value256 (subb x modulus)) < *)
(*       to_Z_uint256 modulus /\ *)
(*   to_Z_uint256 *)
(*     (if carry256 (subb y modulus) then y else value256 (subb y modulus)) = *)
(*       to_Z_uint256 y mod to_Z_uint256 modulus /\ *)
(*   0 <= to_Z_uint256 *)
(*     (if carry256 (subb y modulus) then y else value256 (subb y modulus)) < *)
(*       to_Z_uint256 modulus. *)
(* Proof. *)
(*   intros x y modulus Hmod Hguard. *)
(*   destruct (addmod_guard_true_props x y modulus Hguard) as [Hmhi [Hxhi Hyhi]]. *)
(*   pose proof (topword_le_implies_lt_double_modulus x modulus Hmhi Hxhi) as Hxlt. *)
(*   pose proof (topword_le_implies_lt_double_modulus y modulus Hmhi Hyhi) as Hylt. *)
(*   pose proof (normalize_subb_once_correct x modulus Hmod Hxlt) as Hxnorm. *)
(*   pose proof (normalize_subb_once_correct y modulus Hmod Hylt) as Hynorm. *)
(*   destruct Hxnorm as [Hxnorm Hxrange]. *)
(*   destruct Hynorm as [Hynorm Hyrange]. *)
(*   destruct Hxrange as [Hxnonneg Hxltm]. *)
(*   destruct Hyrange as [Hynonneg Hyltm]. *)
(*   repeat split; assumption. *)
(* Qed. *)

Lemma addmod_reduced_inputs_correct : forall x y modulus,
  0 < to_Z_uint256 modulus ->
  0 <= to_Z_uint256 x < to_Z_uint256 modulus ->
  0 <= to_Z_uint256 y < to_Z_uint256 modulus ->
  let xy_sum := addc x y in
  let rem := subb (value256 xy_sum) modulus in
  to_Z_uint256
    (if (carry256 xy_sum || negb (carry256 rem))%bool
     then value256 rem else value256 xy_sum) =
      (to_Z_uint256 x + to_Z_uint256 y) mod to_Z_uint256 modulus /\
  0 <= to_Z_uint256
    (if (carry256 xy_sum || negb (carry256 rem))%bool
     then value256 rem else value256 xy_sum) <
      to_Z_uint256 modulus.
Proof.
  intros x y modulus Hmod [Hxlo Hxhi] [Hylo Hyhi].
  cbn zeta.
  set (xy_sum := addc x y).
  set (rem := subb (value256 xy_sum) modulus).
  set (s := to_Z_uint256 x + to_Z_uint256 y).
  pose proof (to_Z_uint256_bounds modulus) as Hmod_bound.
  assert (Hs_range : 0 <= s < 2 * to_Z_uint256 modulus) by lia.
  destruct (carry256 xy_sum) eqn:Hcarry; cbn [orb negb].
  - assert (Hlow_eq : to_Z_uint256 (value256 xy_sum) = s - modulus256).
    { unfold s in *.
      unfold xy_sum.
      unfold xy_sum in Hcarry.
      pose proof (addc_full_correct x y) as Hsum.
      rewrite Hcarry in Hsum. lia. }
    assert (Hlow_lt_mod : to_Z_uint256 (value256 xy_sum) <
      to_Z_uint256 modulus).
    { rewrite Hlow_eq. lia. }
    assert (Hborrow_true : carry256 rem = true).
    { pose proof (subb_borrow_correct (value256 xy_sum) modulus) as Hborrow.
      fold rem in Hborrow.
      rewrite Hborrow. apply Z.ltb_lt. exact Hlow_lt_mod. }
    assert (Hres : to_Z_uint256 (value256 rem) =
      s - to_Z_uint256 modulus).
    { unfold s in *.
      pose proof (subb_full_correct (value256 xy_sum) modulus) as Hsub.
      fold rem in Hsub.
      rewrite Hborrow_true in Hsub.
      rewrite Hlow_eq in Hsub. lia. }
    rewrite Hres.
    rewrite Hlow_eq in Hlow_lt_mod.
    pose proof (to_Z_uint256_bounds (value256 xy_sum)) as Hlow_bound.
    rewrite Hlow_eq in Hlow_bound.
    split; [|lia].
    apply Z.mod_unique with (q := 1); [left|]; lia.
  - assert (Hlow_eq : to_Z_uint256 (value256 xy_sum) = s).
    {
      pose proof (addc_full_correct x y) as Hsum.
      subst xy_sum.
      rewrite Hcarry in Hsum.
      lia. }
    destruct (carry256 rem) eqn:Hborrow_rem; cbn [orb negb].
    + pose proof Hborrow_rem as Hborrow_lt.
      pose proof (subb_borrow_correct (value256 xy_sum) modulus) as Hborrow.
      fold rem in Hborrow.
      rewrite Hborrow in Hborrow_lt.
      apply Z.ltb_lt in Hborrow_lt.
      rewrite Hlow_eq.
      split.
      * symmetry.
        apply Z.mod_small. lia.
      * lia.
    + pose proof Hborrow_rem as Hborrow_ge.
      pose proof (subb_borrow_correct (value256 xy_sum) modulus) as Hborrow.
      fold rem in Hborrow.
      rewrite Hborrow in Hborrow_ge.
      apply Z.ltb_ge in Hborrow_ge.
      assert (Hres : to_Z_uint256 (value256 rem) =
        s - to_Z_uint256 modulus).
      { unfold s in *.
        pose proof (subb_full_correct (value256 xy_sum) modulus) as Hsub.
        fold rem in Hsub.
        rewrite Hborrow_rem in Hsub.
        rewrite Hlow_eq in Hsub.
        lia. }
      rewrite Hres.
      split.
      * apply Z.mod_unique with (q := 1); lia.
      * lia.
Qed.

Theorem addmod_correct : forall x y modulus r,
  0 < to_Z_uint256 modulus ->
  addmod x y modulus = Some r ->
  to_Z_uint256 r =
    (to_Z_uint256 x + to_Z_uint256 y) mod to_Z_uint256 modulus /\
  0 <= to_Z_uint256 r < to_Z_uint256 modulus.
Proof.
  intros x y modulus r Hmod Hadd.
  unfold addmod in Hadd.
  destruct ((negb (w3 modulus =? 0)%Uint) && (w3 x <=? w3 modulus)%Uint &&
      (w3 y <=? w3 modulus)%Uint)%bool eqn:Hguard.
  - set (x_norm := if carry256 (subb x modulus) then x
                   else value256 (subb x modulus)).
    fold x_norm in Hadd.
    set (y_norm := if carry256 (subb y modulus) then y
                   else value256 (subb y modulus)).
    fold y_norm in Hadd.
    apply addmod_fast_path_guard in Hguard.
    destruct Hguard as [Hnz [Hxle Hyle]].
    pose proof (topword_le_lt_double x modulus Hnz Hxle) as Hxlt.
    pose proof (topword_le_lt_double y modulus Hnz Hyle) as Hylt.
    pose proof (norm_subb_once_correct x modulus Hmod Hxlt)as Hxnorm.
    pose proof (norm_subb_once_correct y modulus Hmod Hylt)as Hynorm.
    fold x_norm in Hxnorm. fold y_norm in Hynorm.
    destruct Hxnorm as [Hxmod Hxrange].
    destruct Hynorm as [Hymod Hyrange].
    pose proof (addmod_reduced_inputs_correct x_norm y_norm modulus Hmod
                  Hxrange Hyrange) as Hred.
    cbn zeta in Hred.
    destruct (addc x_norm y_norm) as [sum_xy carry_xy] eqn:Hsum.
    cbn [carry256 value256] in Hadd, Hred.
    destruct (subb sum_xy modulus) as [sum_rem borrow_rem] eqn:Hrem.
    cbn [carry256 value256] in Hadd, Hred.
    destruct Hred as [Hrmod Hrrange].
    destruct (carry_xy || negb borrow_rem)%bool eqn:Hchoose;
      inversion Hadd; subst; clear Hadd.
    + rewrite Hrmod, Hxmod, Hymod.
      rewrite <- Zplus_mod.
      split; [|apply Z.mod_pos_bound]; lia.
    + (* same theorem, opposite branch of the final boolean *)
      rewrite Hrmod, Hxmod, Hymod.
      rewrite <- Zplus_mod.
      split; [|apply Z.mod_pos_bound]; lia.
  - (* fallback [udivrem 5 4] path *)
    destruct (udivrem 5 4 (add_words_full_uint256 x y) (uint256_to_words modulus))
      as [divr|] eqn:Hud; try discriminate.
    inversion Hadd; subst; clear Hadd.
    (* bridge [Hud] to division correctness, then use the remainder bound and
       [to_Z_uint256_words_to_uint256_small]. *)
    pose proof (uint256_to_words_length modulus) as Hmod_len.
    assert (Hsum_len : length (add_words_full_uint256 x y) = 5%nat).
    { unfold add_words_full_uint256.
      rewrite length_app, uint256_to_words_length.
      simpl. lia. }
    assert (Hmod_pos : to_Z_words (uint256_to_words modulus) > 0).
    { unfold to_Z_uint256 in Hmod. lia. }
    pose proof (DP.udivrem_correct 5 4
      (add_words_full_uint256 x y) (uint256_to_words modulus) divr
      Hsum_len Hmod_len Hmod_pos Hud) as [Hdiv Hrange].
    pose proof (add_words_full_uint256_correct x y) as Hsum.
    assert (Hrem_small : 0 <= to_Z_words (ud_rem divr) < modulus256).
    { pose proof (to_Z_uint256_bounds modulus) as Hmod_bound.
      unfold to_Z_uint256 in Hmod_bound.
      split.
      - exact (proj1 Hrange).
      - eapply Z.lt_trans.
        + exact (proj2 Hrange).
        + exact (proj2 Hmod_bound). }
    assert (Hrem_value :
      to_Z_uint256 (words_to_uint256 (ud_rem divr)) =
      to_Z_words (ud_rem divr)).
    { destruct (ud_rem divr) as [|r0 [|r1 [|r2 [|r3 rest]]]].
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - pose proof
          (WL.to_Z_words_firstn_skipn (r0 :: r1 :: r2 :: r3 :: rest) 4
             ltac:(simpl; lia)) as Hsplit.
        cbn [firstn skipn] in Hsplit.
        change (WL.modulus_words 4) with modulus256 in Hsplit.
        pose proof (WL.to_Z_words_bound [r0; r1; r2; r3]) as Hprefix.
        change (0 <= to_Z_words [r0; r1; r2; r3] < modulus256)
          in Hprefix.
        pose proof (WL.to_Z_words_bound rest) as Hrest.
        assert (Hrest0 : to_Z_words rest = 0).
        { destruct Hrest as [Hrest_nonneg _].
          pose proof (proj1 Hprefix) as Hprefix_nonneg.
          assert (Htail_small : modulus256 * to_Z_words rest < modulus256).
          { pose proof (proj2 Hrem_small) as Hsmall.
            assert (Htail_le : modulus256 * to_Z_words rest <=
              to_Z_words (r0 :: r1 :: r2 :: r3 :: rest)).
            { change (modulus256 * WL.to_Z_words rest <=
                WL.to_Z_words (r0 :: r1 :: r2 :: r3 :: rest)).
              rewrite Hsplit.
              assert (Hprefix_nonneg_wl :
                0 <= WL.to_Z_words [r0; r1; r2; r3]).
              { exact Hprefix_nonneg. }
              lia. }
            lia. }
          assert (Hrest_nonneg_local : 0 <= to_Z_words rest).
          { exact Hrest_nonneg. }
          pose proof (to_Z_uint256_bounds modulus) as Hmod_bound.
          assert (Hmod256_pos : 0 < modulus256) by lia.
          nia. }
        unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words WL.to_Z_words].
        assert (Hrest0_wl : WL.to_Z_words rest = 0).
        { exact Hrest0. }
        rewrite Hrest0_wl.
        cbn.
        reflexivity. }
    rewrite Hrem_value.
    split.
    + assert (Hsum_wl :
        WL.to_Z_words (add_words_full_uint256 x y) =
        to_Z_uint256 x + to_Z_uint256 y).
      { exact Hsum. }
      rewrite Hsum_wl in Hdiv.
      assert (Hdiv_local :
        to_Z_uint256 x + to_Z_uint256 y =
        to_Z_words (ud_quot divr) * to_Z_uint256 modulus +
        to_Z_words (ud_rem divr)).
      { exact Hdiv. }
      assert (Hrange_local :
        0 <= to_Z_words (ud_rem divr) < to_Z_uint256 modulus).
      { exact Hrange. }
      apply Z.mod_unique with (q := to_Z_words (ud_quot divr));
        [left; exact Hrange_local|nia].
    + exact Hrange.

Qed.


Theorem mulmod_None_iff : forall x y modulus,
(*
In-progress script:
Proof.
  intros x y modulus.
  split.
  - intro Hnone.
    destruct (Z.eq_dec (to_Z_uint256 modulus) 0) as [Hz|Hz]; auto.
    pose proof (to_Z_uint256_bounds modulus) as Hbounds.
    assert (Hmod : 0 < to_Z_uint256 modulus) by lia.
    unfold mulmod in Hnone.
    destruct (udivrem 8 4
      (RMP.truncating_mul_runtime (uint256_to_words x) (uint256_to_words y) 8)
      (uint256_to_words modulus)) eqn:Hud; simpl in Hnone;
      [inversion Hnone|].
    destruct (udivrem_uint256_divisor_exists 8
      (RMP.truncating_mul_runtime (uint256_to_words x) (uint256_to_words y) 8)
      modulus Hmod) as [r Hr].
    (* Stalled here: [Hud] and [Hr] should contradict immediately, but the
       option equality is not simplifying cleanly under the current proof
       state. *)
    admit.
  - intro Hz.
    unfold mulmod.
    apply <- count_significant_words_uint256_zero_iff in Hz.
    unfold udivrem.
    rewrite Hz.
    reflexivity.
Abort.
*)
  mulmod x y modulus = None <->
  to_Z_uint256 modulus = 0.
Proof.
  intros x y modulus.
  split.
  - intro Hnone.
    destruct (Z.eq_dec (to_Z_uint256 modulus) 0) as [Hz|Hz]; auto.
    pose proof (to_Z_uint256_bounds modulus) as Hbounds.
    assert (Hmod : 0 < to_Z_uint256 modulus) by lia.
    exfalso.
    unfold mulmod in Hnone.
    destruct (udivrem 8 4
      (RMP.truncating_mul_runtime (uint256_to_words x) (uint256_to_words y) 8)
      (uint256_to_words modulus)) eqn:Hud; simpl in Hnone;
      [discriminate|].
    destruct (udivrem_uint256_divisor_exists 8
      (RMP.truncating_mul_runtime (uint256_to_words x) (uint256_to_words y) 8)
      modulus Hmod) as [r Hr].
    rewrite Hr in Hud. discriminate.
  - intro Hz.
    destruct modulus as [m0 m1 m2 m3].
    unfold to_Z_uint256, to_Z_words in Hz.
    cbn [uint256_to_words WL.to_Z_words w0 w1 w2 w3] in Hz.
    pose proof (spec_to_Z m0) as H0.
    pose proof (spec_to_Z m1) as H1.
    pose proof (spec_to_Z m2) as H2.
    pose proof (spec_to_Z m3) as H3.
    unfold base in Hz, H0, H1, H2, H3.
    rewrite !width_is_64 in Hz, H0, H1, H2, H3.
    assert (Hm0 : to_Z m0 = 0) by nia.
    assert (Hm1 : to_Z m1 = 0) by nia.
    assert (Hm2 : to_Z m2 = 0) by nia.
    assert (Hm3 : to_Z m3 = 0) by nia.
    assert (Hcount :
      count_significant_words (uint256_to_words (mk_uint256 m0 m1 m2 m3)) = 0%nat).
    { unfold count_significant_words.
      cbn [uint256_to_words rev skip_leading_zeros app w0 w1 w2 w3].
      rewrite !spec_eqb, Hm0, Hm1, Hm2, Hm3, !spec_zero.
      reflexivity. }
    unfold mulmod.
    cbn [uint256_to_words].
    unfold udivrem.
    rewrite Hcount.
    reflexivity.
Qed.


Lemma to_Z_uint256_words_to_uint256_small : forall ws,
(*
In-progress script:
Proof.
  intros ws Hbound.
  destruct ws as [|w0 [|w1 [|w2 [|w3 rest]]]].
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat].
    lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat].
    lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat].
    lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat].
    lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat].
    lia.
  - pose proof (WL.to_Z_words_firstn_skipn (w0 :: w1 :: w2 :: w3 :: rest) 4
      ltac:(lia)) as Hsplit.
    cbn [firstn skipn] in Hsplit.
    pose proof (WL.to_Z_words_bound rest) as Hrest.
    (* Stalled here: from [to_Z_words (firstn 4 ws) + modulus256 *
       to_Z_words rest < modulus256], we need the tail to be zero, then the
       first four words give the whole value. *)
    admit.
Abort.
*)
  0 <= to_Z_words ws < modulus256 ->
  to_Z_uint256 (words_to_uint256 ws) = to_Z_words ws.
Proof.
  intros ws Hbound.
  destruct ws as [|x0 [|x1 [|x2 [|x3 rest]]]].
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
    rewrite !spec_zero. lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
    rewrite !spec_zero. lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
    rewrite !spec_zero. lia.
  - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
    rewrite !spec_zero. lia.
  - pose proof
      (WL.to_Z_words_firstn_skipn (x0 :: x1 :: x2 :: x3 :: rest) 4
         ltac:(simpl; lia)) as Hsplit.
    cbn [firstn skipn] in Hsplit.
    change (WL.modulus_words 4) with modulus256 in Hsplit.
    pose proof (WL.to_Z_words_bound [x0; x1; x2; x3]) as Hprefix.
    change (0 <= to_Z_words [x0; x1; x2; x3] < modulus256) in Hprefix.
    pose proof (WL.to_Z_words_bound rest) as Hrest.
    assert (Hrest0 : to_Z_words rest = 0).
    { destruct Hrest as [Hrest_nonneg _].
      pose proof (proj1 Hprefix) as Hprefix_nonneg.
      assert (Htail_small : modulus256 * to_Z_words rest < modulus256).
      { pose proof (proj2 Hbound) as Hsmall.
        assert (Htail_le : modulus256 * to_Z_words rest <=
          to_Z_words (x0 :: x1 :: x2 :: x3 :: rest)).
        { change (modulus256 * WL.to_Z_words rest <=
            WL.to_Z_words (x0 :: x1 :: x2 :: x3 :: rest)).
          rewrite Hsplit.
          assert (Hprefix_nonneg_wl : 0 <= WL.to_Z_words [x0; x1; x2; x3]).
          { exact Hprefix_nonneg. }
          lia. }
        lia. }
      assert (Hrest_nonneg_local : 0 <= to_Z_words rest).
      { exact Hrest_nonneg. }
      assert (Hmod256_pos : 0 < modulus256).
      { unfold modulus256, modulus_words, WL.modulus_words, base.
        rewrite width_is_64. nia. }
      nia. }
    unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
    cbn [app firstn repeat uint256_to_words WL.to_Z_words w0 w1 w2 w3].
    assert (Hrest0_wl : WL.to_Z_words rest = 0).
    { exact Hrest0. }
    rewrite Hrest0_wl.
    cbn [w0 w1 w2 w3].
    reflexivity.
Qed.


Lemma modulus256_square : modulus256 * modulus256 = modulus_words 8.
Proof.
  unfold modulus256, modulus_words.
  simpl.
  change ((base width) ^ 4 * (base width) ^ 4 = (base width) ^ 8).
  rewrite <- Z.pow_add_r by lia.
  reflexivity.
Qed.

Theorem mulmod_correct : forall x y modulus r,
  0 < to_Z_uint256 modulus ->
  mulmod x y modulus = Some r ->
  to_Z_uint256 r =
    (to_Z_uint256 x * to_Z_uint256 y) mod to_Z_uint256 modulus /\
  0 <= to_Z_uint256 r < to_Z_uint256 modulus.
(*
In-progress script:
Proof.
  intros x y modulus r Hmod Hmul.
  unfold mulmod in Hmul.
  set (prod :=
    RMP.truncating_mul_runtime (uint256_to_words x) (uint256_to_words y) 8) in *.
  destruct (udivrem 8 4 prod (uint256_to_words modulus)) as [[q rem]|]
    eqn:Hud; try discriminate.
  inversion Hmul; subst; clear Hmul.
  pose proof (RMP.truncating_mul_runtime_length
    (uint256_to_words x) (uint256_to_words y) 8 ltac:(lia)) as Hprod_len.
  pose proof (uint256_to_words_length modulus) as Hmod_len.
  pose proof (RMP.truncating_mul_runtime_correct
    (uint256_to_words x) (uint256_to_words y) 8 ltac:(lia)) as Hprod_mod.
  pose proof (WL.to_Z_words_bound prod) as Hprod_bound0.
  pose proof (to_Z_uint256_bounds x) as Hx_bound.
  pose proof (to_Z_uint256_bounds y) as Hy_bound.
  assert (Hxy_small :
    0 <= to_Z_uint256 x * to_Z_uint256 y < modulus_words 8).
  {
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - rewrite <- modulus256_square.
      nia.
  }
  (* Stalled here: the remaining arithmetic is fine, but the proof needs a
     reusable bridge from the local [udivrem] result to [DP.udivrem_correct].
     A first attempt via a generic map-to-DP lemma turned out broader than
     this theorem and is parked for now. *)
Abort.
*)
(* Remaining: Finish The 512-Bit Product Path By Relating The Local
   [Udivrem 8 4] Result To The Division Proof Module, Then Rewrite The Remainder Back
   Through [To_Z_Uint256_Words_To_Uint256_Small]. *)
Proof.
  intros x y modulus r Hmod Hmul.
  unfold mulmod in Hmul.
  set (prod :=
    RMP.truncating_mul_runtime (uint256_to_words x) (uint256_to_words y) 8)
    in *.
  destruct (udivrem 8 4 prod (uint256_to_words modulus)) as [divr|] eqn:Hud;
    try discriminate.
  inversion Hmul; subst r; clear Hmul.
  pose proof
    (RMP.truncating_mul_runtime_length
       (uint256_to_words x) (uint256_to_words y) 8 ltac:(lia))
    as Hprod_len.
  pose proof (uint256_to_words_length modulus) as Hmod_len.
  assert (Hmod_pos : to_Z_words (uint256_to_words modulus) > 0).
  { unfold to_Z_uint256 in Hmod. lia. }
  pose proof
    (DP.udivrem_correct 8 4 prod (uint256_to_words modulus) divr
       Hprod_len Hmod_len Hmod_pos Hud)
    as [Hdiv Hrange].
  pose proof
    (RMP.truncating_mul_runtime_correct
       (uint256_to_words x) (uint256_to_words y) 8
       ltac:(rewrite !uint256_to_words_length; lia)
       ltac:(rewrite !uint256_to_words_length; lia)
       ltac:(lia)
       ltac:(rewrite !uint256_to_words_length; lia))
    as Hprod_mod.
  pose proof (to_Z_uint256_bounds x) as Hx_bound.
  pose proof (to_Z_uint256_bounds y) as Hy_bound.
  assert (Hprod_small : 0 <= to_Z_words prod < modulus_words 8).
  { pose proof (WL.to_Z_words_bound prod) as Hbound.
    assert (Hlen_prod : length prod = 8%nat).
    { change
        (length
           (RMP.truncating_mul_runtime
              (uint256_to_words x) (uint256_to_words y) 8) = 8%nat).
      exact Hprod_len. }
    rewrite Hlen_prod in Hbound.
    exact Hbound. }
  assert (Hxy_small :
    0 <= to_Z_uint256 x * to_Z_uint256 y < modulus_words 8).
  { rewrite <- modulus256_square.
    nia. }
  assert (Hprod_value :
    to_Z_words prod = to_Z_uint256 x * to_Z_uint256 y).
  { unfold to_Z_uint256 in Hprod_mod.
    rewrite Z.mod_small in Hprod_mod by exact Hprod_small.
    rewrite Z.mod_small in Hprod_mod by exact Hxy_small.
    exact Hprod_mod. }
  assert (Hrem_small : 0 <= to_Z_words (ud_rem divr) < modulus256).
  { pose proof (to_Z_uint256_bounds modulus) as Hmod_bound.
    split.
    - exact (proj1 Hrange).
    - eapply Z.lt_trans; [exact (proj2 Hrange)| exact (proj2 Hmod_bound)]. }
  pose proof
    (to_Z_uint256_words_to_uint256_small (ud_rem divr) Hrem_small)
    as Hrem_value.
  rewrite Hrem_value.
  split.
  - assert (Hprod_value_wl :
      WL.to_Z_words prod = to_Z_uint256 x * to_Z_uint256 y).
    { exact Hprod_value. }
    rewrite Hprod_value_wl in Hdiv.
    assert (Hrange_local :
      0 <= to_Z_words (ud_rem divr) < to_Z_uint256 modulus).
    { exact Hrange. }
    apply Z.mod_unique with (q := to_Z_words (ud_quot divr)).
    + left. exact Hrange_local.
    +       rewrite <- (Z.mul_comm (to_Z_words (ud_quot divr))
                   (to_Z_uint256 modulus)).
      exact Hdiv.
  - exact Hrange.
Qed.

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
Proof.
  intros [x0 x1 x2 x3].
  unfold is_negative, to_Z_uint256.
  rewrite spec_ltb.
  change
    (negb (to_Z x3 <? to_Z sign_bit) =
     negb (WL.to_Z_words [x0; x1; x2; x3] <? sign_threshold256)).
  rewrite sign_threshold256_eq.
  rewrite to_Z_sign_bit.
  cbn [WL.to_Z_words].
  replace
    (to_Z x0 + base width *
       (to_Z x1 + base width *
          (to_Z x2 + base width * (to_Z x3 + base width * 0))))
    with (WL.to_Z_words [x0; x1; x2] + modulus_words 3 * to_Z x3).
  2:{ cbn [WL.to_Z_words].
      rewrite WL.modulus_words_succ, WL.modulus_words_succ,
        WL.modulus_words_succ, WL.modulus_words_0.
      ring. }
  f_equal.
  apply high_word_ltb_split.
  - exact (WL.to_Z_words_bound [x0; x1; x2]).
  - pose proof (spec_to_Z x3). lia.
Qed.

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
    pose proof (WL.modulus_words_pos
      (DP.count_significant_words (uint256_to_words x) - 1)) as Hpos.
    assert (Hgt : 0 < WL.to_Z_words (uint256_to_words x)).
    { nia. }
    unfold to_Z_uint256, to_Z_words in Hz.
    change (WL.to_Z_words (uint256_to_words x) = 0) in Hz.
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
(*
In-progress script:
Proof.
  intros u v.
  unfold sdivrem.
  remember (is_negative u) as u_neg.
  remember (is_negative v) as v_neg.
  remember (if u_neg then negate_uint256 u else u) as u_abs.
  remember (if v_neg then negate_uint256 v else v) as v_abs.
  set (divr := udivrem 4 4 (uint256_to_words u_abs) (uint256_to_words v_abs)).
  destruct divr as [r|] eqn:Hdiv.
  - split; [discriminate|].
    intro Hv0.
    assert (Hvabs0 : to_Z_uint256 v_abs = 0).
    { subst v_abs. destruct v_neg; [apply negate_uint256_zero_iff|]; assumption. }
    apply <- count_significant_words_uint256_zero_iff in Hvabs0.
    unfold divr, udivrem in Hdiv.
    rewrite Hvabs0 in Hdiv.
    discriminate.
  - split.
    + intro Hnone.
      unfold divr, udivrem in Hdiv.
      destruct (count_significant_words (uint256_to_words v_abs)) eqn:Hcsw.
      * apply count_significant_words_uint256_zero_iff in Hcsw.
        subst v_abs.
        destruct v_neg; [apply negate_uint256_zero_iff in Hcsw|]; assumption.
      * (* Stalled here: need a cleaner contradiction argument showing that
           [udivrem] cannot be [None] once the divisor has positive value,
           by analyzing the remaining branches of [udivrem]. *)
        discriminate.
    + intro Hv0.
      assert (Hvabs0 : to_Z_uint256 v_abs = 0).
      { subst v_abs. destruct v_neg; [apply negate_uint256_zero_iff|]; assumption. }
      apply <- count_significant_words_uint256_zero_iff in Hvabs0.
      unfold divr, udivrem in Hdiv |- *.
      rewrite Hvabs0.
      reflexivity.
Abort.
*)
(* Remaining: Show That Every Nonzero Divisor Makes The Internal
   Unsigned Division Succeed, Using [Negate_Uint256_Zero_Iff] And The Existing Divisor-Exists Lemma. *)
Proof.
  intros u v.
  unfold sdivrem.
  remember (is_negative u) as u_neg.
  remember (is_negative v) as v_neg.
  remember (if u_neg then negate_uint256 u else u) as u_abs.
  remember (if v_neg then negate_uint256 v else v) as v_abs.
  set (divr := udivrem 4 4 (uint256_to_words u_abs) (uint256_to_words v_abs)).
  split.
  - intro Hnone.
    destruct (Z.eq_dec (to_Z_uint256 v) 0) as [Hv0|Hv0]; auto.
    assert (Hvabs_nonzero : to_Z_uint256 v_abs <> 0).
    { subst v_abs.
      destruct v_neg.
      - intro H0.
        apply Hv0.
        apply (proj1 (negate_uint256_zero_iff v)).
        exact H0.
      - exact Hv0. }
    pose proof (to_Z_uint256_bounds v_abs) as Hvabs_bound.
    assert (Hvabs_pos : 0 < to_Z_uint256 v_abs) by lia.
    destruct (udivrem_uint256_divisor_exists 4
      (uint256_to_words u_abs) v_abs Hvabs_pos) as [r Hr].
    unfold divr in Hnone.
    rewrite Hr in Hnone.
    discriminate.
  - intro Hv0.
    assert (Hvabs0 : to_Z_uint256 v_abs = 0).
    { subst v_abs.
      destruct v_neg.
      - apply (proj2 (negate_uint256_zero_iff v)).
        exact Hv0.
      - exact Hv0. }
    apply <- count_significant_words_uint256_zero_iff in Hvabs0.
    unfold divr, udivrem.
    rewrite Hvabs0.
    reflexivity.
Qed.

Theorem sdivrem_correct : forall u v r,
  to_Z_uint256 v <> 0 ->
  sdivrem u v = Some r ->
  to_Z_signed_words (ud_quot r) =
    Z.quot (to_Z_signed_uint256 u) (to_Z_signed_uint256 v) /\
  to_Z_signed_words (ud_rem r) =
    Z.rem (to_Z_signed_uint256 u) (to_Z_signed_uint256 v).
(* Remaining: Combine The Unsigned Division Theorem With The Sign-Case
   Analysis From [Is_Negative_Correct] And The Quotient/Remainder Negation Lemmas. *)
Admitted.

Lemma signbit63_nonzero_is_negative : forall x,
  negb (eqb (shr (w3 x) 63) zero) = is_negative x.
Proof.
  intros [x0 x1 x2 x3].
  unfold is_negative.
  cbn [w3].
  rewrite spec_eqb, spec_shr, spec_zero, spec_ltb.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite to_Z_sign_bit.
  pose proof (spec_to_Z x3) as Hx3.
  assert (Hdiv_bound : 0 <= to_Z x3 / 2 ^ 63 < 2).
  { split.
    - apply Z.div_pos; lia.
    - unfold base in Hx3. rewrite width_is_64 in Hx3.
      apply Z.div_lt_upper_bound; lia. }
  rewrite Z.mod_small by (unfold base; rewrite width_is_64; lia).
  destruct (Z.ltb_spec0 (to_Z x3) (2 ^ 63)) as [Hlt|Hge].
  - rewrite Z.div_small by lia.
    reflexivity.
  - assert (Hdiv_ge: (to_Z x3) / 2^63 >= 1)
      by (change 1 with (2^63 / 2^63)
          ; apply Z_div_ge; lia).
    assert ((to_Z x3 / 2 ^ Z.of_nat 63 =? 0) = false)
      by (apply Z.eqb_neq; lia).
    apply Znot_lt_ge in Hge.
    rewrite H; reflexivity.
Qed.

Theorem slt_correct : forall x y,
  slt x y = Z.ltb (to_Z_signed_uint256 x) (to_Z_signed_uint256 y).
Proof.
  intros x y.
  unfold slt, to_Z_signed_uint256.
  rewrite !signbit63_nonzero_is_negative.
  rewrite !is_negative_correct.
  rewrite ltb_uint256_correct.
  set (ux := to_Z_uint256 x).
  set (uy := to_Z_uint256 y).
  pose proof (to_Z_uint256_bounds x) as Hux.
  pose proof (to_Z_uint256_bounds y) as Huy.
  destruct (Z.ltb ux sign_threshold256) eqn:Hx;
    destruct (Z.ltb uy sign_threshold256) eqn:Hy; simpl.
  - now rewrite orb_false_r.
  - symmetry; apply Z.ltb_ge; lia.
  - symmetry; apply Z.ltb_lt. lia.
  - destruct (Z.ltb_spec0 ux uy) as [Hlt|Hge].
    + rewrite Z.sub_lt_mono_r with (p := modulus256) in Hlt.
      now apply Z.ltb_lt in Hlt.
    + apply Znot_lt_ge, Z.ge_le in Hge.
      rewrite Z.sub_le_mono_r with (p := modulus256) in Hge.
      now rewrite <- Z.ltb_ge in Hge.
Qed.

Theorem shift_left_uint256_aux_correct : forall x shift,
  to_Z_uint256 (shift_left_uint256_aux x shift) =
    if Z.ltb (to_Z shift) 256
    then (to_Z_uint256 x * 2 ^ to_Z shift) mod modulus256
    else 0.
(* Remaining: Prove Each Branch Of The C++-Style Shift Control Flow
   Against The Corresponding Arithmetic Left-Shift Modulo [Modulus256]. *)
Admitted.

Lemma to_Z_uint256_zero_high : forall s0 s1 s2 s3,
  to_Z s1 = 0 -> to_Z s2 = 0 -> to_Z s3 = 0 ->
  to_Z_uint256 (mk_uint256 s0 s1 s2 s3) = to_Z s0.
Proof.
  intros s0 s1 s2 s3 H1 H2 H3.
  unfold to_Z_uint256, to_Z_words.
  cbn.
  rewrite H1, H2, H3.
  lia.
Qed.

Lemma to_Z_uint256_high_ge_base : forall s0 s1 s2 s3,
  0 < to_Z s1 \/ 0 < to_Z s2 \/ 0 < to_Z s3 ->
  base width <= to_Z_uint256 (mk_uint256 s0 s1 s2 s3).
Proof.
  intros s0 s1 s2 s3 Hhi.
  unfold to_Z_uint256, to_Z_words.
  cbn.
  pose proof (spec_to_Z s0) as H0.
  pose proof (spec_to_Z s1) as H1.
  pose proof (spec_to_Z s2) as H2.
  pose proof (spec_to_Z s3) as H3.
  assert (Hbase : 0 < base width).
  { unfold base. rewrite width_is_64. simpl. lia. }
  assert (Hbase1 : 1 <= base width) by lia.
  destruct Hhi as [Hs1 | [Hs2 | Hs3p]].
  - nia.
  - assert (Hbb : base width <= base width * base width) by nia.
    nia.
  - assert (Hbbb : base width <= base width * base width * base width) by nia.
    nia.
Qed.

Theorem shift_left_uint256_correct : forall x shift,
(*
In-progress script:
Proof.
  intros x [s0 s1 s2 s3].
  unfold shift_left_uint256.
  destruct (s1 =? 0) eqn:Hs1;
    destruct (s2 =? 0) eqn:Hs2;
    destruct (s3 =? 0) eqn:Hs3.
  - (* Good case: all high words are zero.  The intended route is to turn
       [Hs1]/[Hs2]/[Hs3] into [to_Z si = 0], rewrite
       [shift_left_uint256_aux_correct], and then reduce
       [to_Z_uint256 shift] to [to_Z s0].
       The blocker was notation/orientation around [spec_eqb] after the
       destruct-generated equalities. *)
    admit.
  - (* All remaining branches use [to_Z_uint256_high_ge_base] to show the
       outer [if] takes the zero branch.  The statement looks right; the
       script just needs a cleaner way to normalize the [eqb] hypotheses. *)
    admit.
Abort.
*)
  to_Z_uint256 (shift_left_uint256 x shift) =
    if Z.ltb (to_Z_uint256 shift) (base width)
    then if Z.ltb (to_Z_uint256 shift) 256
         then (to_Z_uint256 x * 2 ^ to_Z_uint256 shift) mod modulus256
         else 0
    else 0.
(* Remaining: Split On Whether The High Three Shift Words Are Zero,
   Then Combine [Shift_Left_Uint256_Aux_Correct] With The Zero-High / High-Ge-Base Lemmas. *)
Admitted.

Theorem exp_correct : forall base exponent,
  to_Z_uint256 (exp base exponent) =
    Z.pow (to_Z_uint256 base) (to_Z_uint256 exponent) mod modulus256.
(* Remaining: Prove The Fast Path For Base=2 And Then The Generic
   Square-And-Multiply Loop Against Modular Exponentiation. *)
Admitted.

End MakeProofs.

Module MakeProofsLegacy (Import Word64 : Uint64) (U128 : Uint128)
  (Import Bridge : UintWiden Word64 U128).
Module B := Base.MakeProof(Word64).
Module WL := WordsLemmas.MakeProofs(B).
Module RM := RuntimeMul.MakeProof(B).
Module RMP := RuntimeMulProofs.MakeProofs(B)(RM)(WL).
Module Div := Division.Make(B)(U128)(Bridge).
Module DP := DivisionProofs.MakeProofs(B)(U128)(Bridge)(Div)(WL).
Module Arith := Arithmetic.Make(B)(U128)(Bridge)(Div)(RM).
Include MakeProofs(B)(U128)(Bridge)(WL)(RM)(RMP)(Div)(DP)(Arith).
End MakeProofsLegacy.

Module MakeProofsOn := MakeProofs.
