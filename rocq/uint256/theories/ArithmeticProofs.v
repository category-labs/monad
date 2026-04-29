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
From Stdlib Require Import Zquot.
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

Local Notation to_Z_words := WL.to_Z_words.
Local Notation modulus_words := WL.modulus_words.

Definition modulus256 : Z := modulus_words 4.

Definition sign_threshold256 : Z := modulus256 / 2.

Definition to_Z_uint256 (x : uint256) : Z :=
  to_Z_words (uint256_to_words x).

Definition to_Z_signed_uint256 (x : uint256) : Z :=
  let ux := to_Z_uint256 x in
  if Z.ltb ux sign_threshold256 then ux else ux - modulus256.

Definition to_Z_signed_words (ws : words) : Z :=
  to_Z_signed_uint256 (words_to_uint256 ws).

Definition wrap_signed256 (z : Z) : Z :=
  let uz := z mod modulus256 in
  if Z.ltb uz sign_threshold256 then uz else uz - modulus256.

Lemma uint256_to_words_length : forall x,
  length (uint256_to_words x) = 4%nat.
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
  - split; [lia|].
    unfold base. rewrite width_is_64.
    nia.
Qed.

Lemma base_width_gt_1 : 1 < base width.
Proof.
  unfold base. rewrite width_is_64. lia.
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
  apply mod_carry_decompose; [lia|].
  destruct Hc as [Hc|Hc]; subst c; nia.
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

Lemma addc_full_correct : forall x y,
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

(* Theorem addc_value_correct : forall x y, *)
(*   to_Z_uint256 (value256 (addc x y)) = *)
(*     (to_Z_uint256 x + to_Z_uint256 y) mod modulus256. *)
(* Proof. *)
(*   intros x y. *)
(*   set (v := to_Z_uint256 (value256 (addc x y))) in *. *)
(*   set (s := to_Z_uint256 x + to_Z_uint256 y) in *. *)
(*   pose proof (addc_full_correct_aux x y) as Hfull. *)
(*   fold v in Hfull. *)
(*   fold s in Hfull. *)
(*   pose proof (to_Z_uint256_bounds (value256 (addc x y))) as Hbound. *)
(*   fold v in Hbound. *)
(*   destruct (carry256 (addc x y)) eqn:Hcarry. *)
(*   - simpl in Hfull. *)
(*     apply Z.mod_unique with (q := 1). *)
(*     + left. exact Hbound. *)
(*     + rewrite Z.mul_1_r. rewrite Z.add_comm. exact (eq_sym Hfull). *)
(*   - simpl in Hfull. *)
(*     rewrite <- Hfull. *)
(*     rewrite Z.add_0_r. *)
(*     symmetry. *)
(*     apply Z.mod_small. *)
(*     exact Hbound. *)
(* Qed. *)

(* Theorem addc_carry_correct : forall x y, *)
(*   carry256 (addc x y) = *)
(*     Z.leb modulus256 (to_Z_uint256 x + to_Z_uint256 y). *)
(* Proof. *)
(*   intros x y. *)
(*   set (v := to_Z_uint256 (value256 (addc x y))) in *. *)
(*   set (s := to_Z_uint256 x + to_Z_uint256 y) in *. *)
(*   pose proof (addc_full_correct_aux x y) as Hfull. *)
(*   fold v in Hfull. *)
(*   fold s in Hfull. *)
(*   pose proof (to_Z_uint256_bounds (value256 (addc x y))) as Hbound. *)
(*   fold v in Hbound. *)
(*   destruct (carry256 (addc x y)) eqn:Hcarry. *)
(*   - symmetry. *)
(*     apply Z.leb_le. *)
(*     lia. *)
(*   - symmetry. *)
(*     apply Z.leb_gt. *)
(*     lia. *)
(* Qed. *)

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
  pose proof (addc_full_correct x y) as H.
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
    unfold to_Z_uint256.
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
    cbn [uint256_to_words w0 w1 w2 w3] in Hz.
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
  cbn [uint256_to_words].
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
        cbn [app firstn repeat uint256_to_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words w0 w1 w2 w3].
        rewrite !spec_zero. lia.
      - unfold words_to_uint256, fit_words, to_Z_uint256, to_Z_words.
        cbn [app firstn repeat uint256_to_words w0 w1 w2 w3].
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
            { rewrite Hsplit.
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
        unfold words_to_uint256, fit_words.
        cbn [app firstn uint256_to_words to_Z_uint256 to_Z_words].
        assert (Hrest0_wl : to_Z_words rest = 0).
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
    unfold words_to_uint256, fit_words.
    cbn [app firstn uint256_to_words to_Z_uint256 to_Z_words].
    assert (Hrest0_wl : to_Z_words rest = 0).
    { exact Hrest0. }
    rewrite Hrest0_wl.
    cbn.
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

Lemma to_Z_signed_uint256_wrap : forall x,
  to_Z_signed_uint256 x = wrap_signed256 (to_Z_uint256 x).
Proof.
  intro x.
  unfold to_Z_signed_uint256, wrap_signed256.
  pose proof (to_Z_uint256_bounds x) as Hx.
  rewrite Z.mod_small by lia.
  reflexivity.
Qed.

Lemma to_Z_signed_words_wrap : forall ws,
  0 <= to_Z_words ws < modulus256 ->
  to_Z_signed_words ws = wrap_signed256 (to_Z_words ws).
Proof.
  intros ws Hws.
  unfold to_Z_signed_words.
  rewrite to_Z_signed_uint256_wrap.
  f_equal.
  apply to_Z_uint256_words_to_uint256_small.
  exact Hws.
Qed.

Lemma negate_words_small_correct : forall ws,
  0 <= to_Z_words ws < modulus256 ->
  to_Z_words (negate_words ws) = (- to_Z_words ws) mod modulus256.
Proof.
  intros ws Hws.
  change (to_Z_uint256 (negate_uint256 (words_to_uint256 ws)) =
    (- to_Z_words ws) mod modulus256).
  rewrite negate_uint256_correct.
  rewrite to_Z_uint256_words_to_uint256_small by exact Hws.
  reflexivity.
Qed.

Lemma to_Z_signed_negate_words_wrap : forall ws,
  0 <= to_Z_words ws < modulus256 ->
  to_Z_signed_words (negate_words ws) = wrap_signed256 (- to_Z_words ws).
Proof.
  intros ws Hws.
  assert (Hneg : 0 <= to_Z_words (negate_words ws) < modulus256).
  { rewrite negate_words_small_correct by exact Hws.
    apply Z.mod_pos_bound.
    exact modulus256_pos. }
  rewrite (to_Z_signed_words_wrap _ Hneg).
  rewrite negate_words_small_correct by exact Hws.
  unfold wrap_signed256.
  rewrite Z.mod_mod by (pose proof modulus256_pos; lia).
  reflexivity.
Qed.

Lemma to_Z_signed_uint256_nonnegative : forall x,
  is_negative x = false ->
  to_Z_signed_uint256 x = to_Z_uint256 x.
Proof.
  intros x Hneg.
  rewrite is_negative_correct in Hneg.
  apply negb_false_iff in Hneg.
  apply Z.ltb_lt in Hneg.
  unfold to_Z_signed_uint256.
  destruct (Z.ltb_spec0 (to_Z_uint256 x) sign_threshold256); lia.
Qed.

Lemma to_Z_signed_uint256_negative : forall x,
  is_negative x = true ->
  to_Z_signed_uint256 x = - to_Z_uint256 (negate_uint256 x).
Proof.
  intros x Hneg.
  rewrite is_negative_correct in Hneg.
  apply negb_true_iff in Hneg.
  apply Z.ltb_ge in Hneg.
  unfold to_Z_signed_uint256.
  destruct (Z.ltb_spec0 (to_Z_uint256 x) sign_threshold256) as [Hlt|Hge].
  - lia.
  - rewrite negate_uint256_correct.
    pose proof (to_Z_uint256_bounds x) as Hx.
    assert (Hthpos : 0 < sign_threshold256).
    { unfold sign_threshold256, modulus256, modulus_words,
        WL.modulus_words, base.
      rewrite width_is_64.
      vm_compute.
      reflexivity. }
    assert (Hxpos : 0 < to_Z_uint256 x) by lia.
    assert (Hlt0 : (- to_Z_uint256 x <? 0) = true).
    { apply Z.ltb_lt. lia. }
    pose proof (mod_borrow_decompose modulus256 (- to_Z_uint256 x)
      modulus256_pos ltac:(lia)) as Hmod.
    rewrite Hlt0 in Hmod.
    lia.
Qed.

Lemma udivrem_uint256_4_4_correct : forall u_abs v_abs divr,
  0 < to_Z_uint256 v_abs ->
  udivrem 4 4 (uint256_to_words u_abs) (uint256_to_words v_abs) =
    Some divr ->
  to_Z_words (ud_quot divr) =
    Z.quot (to_Z_uint256 u_abs) (to_Z_uint256 v_abs) /\
  to_Z_words (ud_rem divr) =
    Z.rem (to_Z_uint256 u_abs) (to_Z_uint256 v_abs) /\
  0 <= to_Z_words (ud_quot divr) < modulus256 /\
  0 <= to_Z_words (ud_rem divr) < modulus256.
Proof.
  intros u_abs v_abs divr Hvabs_pos Hdiv.
  unfold to_Z_uint256 in Hvabs_pos.
  assert (Hvabs_pos_gt : to_Z_words (uint256_to_words v_abs) > 0) by lia.
  pose proof (DP.udivrem_correct 4 4
    (uint256_to_words u_abs) (uint256_to_words v_abs) divr
    (uint256_to_words_length u_abs) (uint256_to_words_length v_abs)
    Hvabs_pos_gt Hdiv) as [Hdiv_eq Hrange].
  change (to_Z_words (uint256_to_words u_abs)) with (to_Z_uint256 u_abs)
    in Hdiv_eq.
  change (to_Z_words (uint256_to_words v_abs)) with (to_Z_uint256 v_abs)
    in Hdiv_eq.
  change (to_Z_words (uint256_to_words v_abs)) with (to_Z_uint256 v_abs)
    in Hrange.
  rewrite Z.mul_comm in Hdiv_eq.
  assert (Hrem_ok : Zquot.Remainder (to_Z_uint256 u_abs)
    (to_Z_uint256 v_abs) (to_Z_words (ud_rem divr))).
  { left.
    split.
    - pose proof (to_Z_uint256_bounds u_abs). lia.
    - rewrite Z.abs_eq by lia. exact Hrange. }
  pose proof (Zquot.Zquot_unique_full (to_Z_uint256 u_abs)
    (to_Z_uint256 v_abs) (to_Z_words (ud_quot divr))
    (to_Z_words (ud_rem divr)) Hrem_ok Hdiv_eq) as Hquot.
  pose proof (Zquot.Zrem_unique_full (to_Z_uint256 u_abs)
    (to_Z_uint256 v_abs) (to_Z_words (ud_quot divr))
    (to_Z_words (ud_rem divr)) Hrem_ok Hdiv_eq) as Hrem.
  assert (Hq_range : 0 <= to_Z_words (ud_quot divr) < modulus256).
  { pose proof (to_Z_uint256_bounds u_abs) as Huabs_bound.
    split; nia. }
  assert (Hr_range : 0 <= to_Z_words (ud_rem divr) < modulus256).
  { split.
    - exact (proj1 Hrange).
    - eapply Z.lt_trans.
      + exact (proj2 Hrange).
      + exact (proj2 (to_Z_uint256_bounds v_abs)). }
  split.
  - exact Hquot.
  - split.
    + exact Hrem.
    + split.
      * exact Hq_range.
      * exact Hr_range.
Qed.

Theorem sdivrem_correct : forall u v r,
  to_Z_uint256 v <> 0 ->
  sdivrem u v = Some r ->
  to_Z_signed_words (ud_quot r) =
    wrap_signed256
      (Z.quot (to_Z_signed_uint256 u) (to_Z_signed_uint256 v)) /\
  to_Z_signed_words (ud_rem r) =
    wrap_signed256
      (Z.rem (to_Z_signed_uint256 u) (to_Z_signed_uint256 v)).
Proof.
  intros u v r Hv0 Hsdiv.
  unfold sdivrem in Hsdiv.
  destruct (is_negative u) eqn:Hu;
    destruct (is_negative v) eqn:Hv; simpl in Hsdiv.
  - destruct (udivrem 4 4 (uint256_to_words (negate_uint256 u))
        (uint256_to_words (negate_uint256 v))) as [divr|] eqn:Hdiv;
      try discriminate.
    inversion Hsdiv; subst r; clear Hsdiv.
    cbn [ud_quot ud_rem].
    assert (Hvabs_pos : 0 < to_Z_uint256 (negate_uint256 v)).
    { pose proof (to_Z_uint256_bounds (negate_uint256 v)) as Hvabs.
      destruct (Z.eq_dec (to_Z_uint256 (negate_uint256 v)) 0) as [H0|H0].
      - exfalso.
        apply Hv0.
        apply (proj1 (negate_uint256_zero_iff v)).
        exact H0.
      - lia. }
    pose proof (udivrem_uint256_4_4_correct (negate_uint256 u)
      (negate_uint256 v) divr Hvabs_pos Hdiv)
      as [Hquot [Hrem [Hq_range Hr_range]]].
    split.
    + rewrite (to_Z_signed_words_wrap (ud_quot divr) Hq_range).
      rewrite (to_Z_signed_uint256_negative u Hu).
      rewrite (to_Z_signed_uint256_negative v Hv).
      rewrite Z.quot_opp_opp by lia.
      rewrite Hquot.
      reflexivity.
    + rewrite (to_Z_signed_negate_words_wrap (ud_rem divr) Hr_range).
      rewrite (to_Z_signed_uint256_negative u Hu).
      rewrite (to_Z_signed_uint256_negative v Hv).
      rewrite Z.rem_opp_opp by lia.
      rewrite Hrem.
      reflexivity.
  - destruct (udivrem 4 4 (uint256_to_words (negate_uint256 u))
        (uint256_to_words v)) as [divr|] eqn:Hdiv;
      try discriminate.
    inversion Hsdiv; subst r; clear Hsdiv.
    cbn [ud_quot ud_rem].
    assert (Hvabs_pos : 0 < to_Z_uint256 v).
    { pose proof (to_Z_uint256_bounds v). lia. }
    pose proof (udivrem_uint256_4_4_correct (negate_uint256 u) v divr
      Hvabs_pos Hdiv) as [Hquot [Hrem [Hq_range Hr_range]]].
    split.
    + rewrite (to_Z_signed_negate_words_wrap (ud_quot divr) Hq_range).
      rewrite (to_Z_signed_uint256_negative u Hu).
      rewrite (to_Z_signed_uint256_nonnegative v Hv).
      rewrite Z.quot_opp_l by lia.
      rewrite Hquot.
      reflexivity.
    + rewrite (to_Z_signed_negate_words_wrap (ud_rem divr) Hr_range).
      rewrite (to_Z_signed_uint256_negative u Hu).
      rewrite (to_Z_signed_uint256_nonnegative v Hv).
      rewrite Z.rem_opp_l by lia.
      rewrite Hrem.
      reflexivity.
  - destruct (udivrem 4 4 (uint256_to_words u)
        (uint256_to_words (negate_uint256 v))) as [divr|] eqn:Hdiv;
      try discriminate.
    inversion Hsdiv; subst r; clear Hsdiv.
    cbn [ud_quot ud_rem].
    assert (Hvabs_pos : 0 < to_Z_uint256 (negate_uint256 v)).
    { pose proof (to_Z_uint256_bounds (negate_uint256 v)) as Hvabs.
      destruct (Z.eq_dec (to_Z_uint256 (negate_uint256 v)) 0) as [H0|H0].
      - exfalso.
        apply Hv0.
        apply (proj1 (negate_uint256_zero_iff v)).
        exact H0.
      - lia. }
    pose proof (udivrem_uint256_4_4_correct u (negate_uint256 v) divr
      Hvabs_pos Hdiv) as [Hquot [Hrem [Hq_range Hr_range]]].
    split.
    + rewrite (to_Z_signed_negate_words_wrap (ud_quot divr) Hq_range).
      rewrite (to_Z_signed_uint256_nonnegative u Hu).
      rewrite (to_Z_signed_uint256_negative v Hv).
      rewrite Z.quot_opp_r by lia.
      rewrite Hquot.
      reflexivity.
    + rewrite (to_Z_signed_words_wrap (ud_rem divr) Hr_range).
      rewrite (to_Z_signed_uint256_nonnegative u Hu).
      rewrite (to_Z_signed_uint256_negative v Hv).
      rewrite Z.rem_opp_r by lia.
      rewrite Hrem.
      reflexivity.
  - destruct (udivrem 4 4 (uint256_to_words u)
        (uint256_to_words v)) as [divr|] eqn:Hdiv;
      try discriminate.
    inversion Hsdiv; subst r; clear Hsdiv.
    cbn [ud_quot ud_rem].
    assert (Hvabs_pos : 0 < to_Z_uint256 v).
    { pose proof (to_Z_uint256_bounds v). lia. }
    pose proof (udivrem_uint256_4_4_correct u v divr Hvabs_pos Hdiv)
      as [Hquot [Hrem [Hq_range Hr_range]]].
    split.
    + rewrite (to_Z_signed_words_wrap (ud_quot divr) Hq_range).
      rewrite (to_Z_signed_uint256_nonnegative u Hu).
      rewrite (to_Z_signed_uint256_nonnegative v Hv).
      rewrite Hquot.
      reflexivity.
    + rewrite (to_Z_signed_words_wrap (ud_rem divr) Hr_range).
      rewrite (to_Z_signed_uint256_nonnegative u Hu).
      rewrite (to_Z_signed_uint256_nonnegative v Hv).
      rewrite Hrem.
      reflexivity.
Qed.

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

Lemma bounded_shift_nat_correct : forall fuel shift,
  (fuel <= word_width)%nat ->
  to_Z shift < Z.of_nat fuel ->
  bounded_shift_nat fuel shift = Z.to_nat (to_Z shift).
Proof.
  induction fuel as [|fuel IH]; intros shift Hfuel Hlt.
  - pose proof (spec_to_Z shift). exfalso; lia.
  - simpl bounded_shift_nat.
    rewrite spec_eqb, spec_zero.
    destruct (Z.eq_dec (to_Z shift) 0) as [Hz|Hz].
    + rewrite Hz, Z.eqb_refl. reflexivity.
    + assert (Heq : (to_Z shift =? 0) = false) by (apply Z.eqb_neq; exact Hz).
      rewrite Heq.
      pose proof (spec_to_Z shift) as HshiftZ. rewrite width_is_64 in HshiftZ.
      assert (Hsub_lt : to_Z ((shift - 1)%Uint) < Z.of_nat fuel).
      { rewrite spec_sub, spec_one.
        rewrite Z.mod_small.
      2:{ split.
          - lia.
          - pose proof (spec_to_Z shift) as HshiftZ0.
            unfold base in HshiftZ0 |- *.
            rewrite width_is_64 in HshiftZ0 |- *.
            lia. }
        - lia. }
      rewrite IH by lia.
      rewrite spec_sub, spec_one.
      rewrite Z.mod_small.
      2: { split.
           - lia.
           - unfold base, word_width in Hfuel |-.
             rewrite width_is_64. simpl. lia. }
      replace (to_Z shift) with ((to_Z shift - 1) + 1) by lia.
      rewrite Z2Nat.inj_add by lia.
      simpl. lia.
Qed.

Lemma to_Z_words_firstn_shift_left_mod : forall ws s,
  (s < Pos.to_nat U64.width)%nat ->
  to_Z_words (firstn (length ws) (shift_left_words ws s)) =
    (to_Z_words ws * 2 ^ Z.of_nat s) mod modulus_words (length ws).
Proof.
  intros ws s Hs.
  pose proof (DP.shift_left_words_correct ws s Hs) as Hshift.
  pose proof (DP.shift_left_words_length ws s) as Hlen.
  set (result := shift_left_words ws s) in *.
  assert (Hle : (length ws <= length result)%nat) by lia.
  pose proof (WL.to_Z_words_firstn_skipn result (length ws) Hle) as Hsplit.
  pose proof (WL.to_Z_words_bound (firstn (length ws) result)) as Hfirst.
  rewrite firstn_length_le in Hfirst by lia.
  rewrite Hshift in Hsplit.
  apply Z.mod_unique with (q := to_Z_words (skipn (length ws) result)).
  - left. exact Hfirst.
  - rewrite Z.add_comm. exact Hsplit.
Qed.

Lemma shld64_zero_low_spec : forall high s,
  (s < Pos.to_nat U64.width)%nat ->
  to_Z (shld64 high zero s) = to_Z (shl high s).
Proof.
  intros high s Hs.
  rewrite DP.shld64_spec by exact Hs.
  rewrite spec_shl, spec_zero.
  rewrite Z.div_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftl_mul_pow2 by lia.
  lia.
Qed.

Lemma modulus_words_add : forall m n,
  modulus_words (m + n) = modulus_words m * modulus_words n.
Proof.
  intros m n.
  unfold modulus_words, WL.modulus_words.
  rewrite Nat2Z.inj_add.
  rewrite Z.pow_add_r by (pose proof base_width_gt_1; lia).
  ring.
Qed.

Lemma modulus_words_1 :
  modulus_words 1 = 2 ^ 64.
Proof.
  unfold modulus_words, WL.modulus_words, base.
  rewrite width_is_64.
  change (Z.pow_pos (2 ^ 64) 1) with ((2 ^ 64) ^ 1).
  rewrite Z.pow_1_r.
  reflexivity.
Qed.

Lemma modulus_words_2 :
  modulus_words 2 = 2 ^ 128.
Proof.
  unfold modulus_words, WL.modulus_words, base.
  rewrite width_is_64.
  change (Z.pow_pos (2 ^ 64) 2) with ((2 ^ 64) ^ 2).
  rewrite Z.pow_2_r.
  replace 128 with (64 + 64) by lia.
  rewrite Z.pow_add_r by lia.
  reflexivity.
Qed.

Lemma modulus_words_3 :
  modulus_words 3 = 2 ^ 192.
Proof.
  change (modulus_words 3) with (modulus_words (2 + 1)).
  rewrite modulus_words_add.
  rewrite modulus_words_2, modulus_words_1.
  replace 192 with (128 + 64) by lia.
  rewrite Z.pow_add_r by lia.
  reflexivity.
Qed.

Lemma modulus_words_scale_mod : forall k n a,
  modulus_words k * (a mod modulus_words n) =
    (modulus_words k * a) mod modulus_words (k + n).
Proof.
  intros k n a.
  pose proof (WL.modulus_words_pos k) as Hkpos.
  pose proof (WL.modulus_words_pos n) as Hnpos.
  rewrite modulus_words_add.
  apply Z.mod_unique with (q := a / modulus_words n).
  - left.
    pose proof (Z.mod_pos_bound a (WL.modulus_words n) ltac:(lia)) as Hmod.
    replace (modulus_words k * modulus_words n) with
      (WL.modulus_words k * WL.modulus_words n) by reflexivity.
    split; nia.
  - pose proof (Z.div_mod a (modulus_words n) ltac:(lia)) as Hdiv.
    replace a with
      (modulus_words n * (a / modulus_words n) + a mod modulus_words n)
      at 1 by (symmetry; exact Hdiv).
    ring.
Qed.

Lemma to_Z_shl_one : forall n,
  (n < Pos.to_nat U64.width)%nat ->
  to_Z (shl one n) = 2 ^ Z.of_nat n.
Proof.
  intros n Hn.
  rewrite spec_shl, spec_one.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mod_small.
  - lia.
  - split.
    + apply Z.mul_nonneg_nonneg; lia.
    + unfold base. rewrite width_is_64. simpl.
      replace (1 * 2 ^ Z.of_nat n) with (2 ^ Z.of_nat n) by lia.
      assert (Hpowpos : 0 < 2 ^ Z.of_nat n) by (apply Z.pow_pos_nonneg; lia).
      destruct (2 ^ Z.of_nat n) eqn:Hp; simpl in *; try lia.
      rewrite <- Hp. replace (Z.pow_pos 2 64) with (2 ^ 64) by reflexivity.
      rewrite width_is_64 in Hn.
      apply Z.pow_lt_mono_r; lia.
Qed.

Theorem shift_left_uint256_aux_correct : forall x shift,
  to_Z_uint256 (shift_left_uint256_aux x shift) =
    if Z.ltb (to_Z shift) 256
    then (to_Z_uint256 x * 2 ^ to_Z shift) mod modulus256
    else 0.
Proof.
  intros [x0 x1 x2 x3] shift.
  unfold shift_left_uint256_aux, to_Z_uint256.
  cbn [uint256_to_words].
  pose proof (to_Z_shl_one 6 ltac:(rewrite width_is_64; simpl; lia)) as H64.
  pose proof (to_Z_shl_one 7 ltac:(rewrite width_is_64; simpl; lia)) as H128.
  pose proof (to_Z_shl_one 8 ltac:(rewrite width_is_64; simpl; lia)) as H256.
  assert (H192 : to_Z (shl (one + one + one)%Uint 6) = 192).
  { rewrite spec_shl, !spec_add, !spec_one.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small.
    - repeat rewrite Z.mod_small by (unfold base; rewrite width_is_64; simpl; lia).
      nia.
    - repeat rewrite Z.mod_small by (unfold base; rewrite width_is_64; simpl; lia).
      unfold base. rewrite width_is_64. simpl. lia. }
  rewrite !spec_ltb.
  rewrite H64, H128, H256, H192.
  replace (2 ^ Z.of_nat 8) with 256 in *.
  2: reflexivity.
  replace (2 ^ Z.of_nat 7) with 128 in *.
  2: reflexivity.
  replace (2 ^ Z.of_nat 6) with 64 in *.
  2: reflexivity.
  destruct (to_Z shift <? 256) eqn:H256lt.
  - cbn [negb].
    apply Z.ltb_lt in H256lt.
    destruct (to_Z shift <? 128) eqn:H128lt.
    + apply Z.ltb_lt in H128lt.
      destruct (to_Z shift <? 64) eqn:H64lt.
      * apply Z.ltb_lt in H64lt.
        pose proof (spec_to_Z shift) as HshiftZ.
        rewrite (bounded_shift_nat_correct word_width shift ltac:(lia)
          ltac:(unfold word_width; rewrite width_is_64; exact H64lt)).
        unfold uint256_to_words.
        cbn [w0 w1 w2 w3].
        replace
          (WL.to_Z_words
             [shl x0 (Z.to_nat (to_Z shift));
              shld64 x1 x0 (Z.to_nat (to_Z shift));
              shld64 x2 x1 (Z.to_nat (to_Z shift));
              shld64 x3 x2 (Z.to_nat (to_Z shift))])
          with
          (WL.to_Z_words
             (firstn 4
                (shift_left_words [x0; x1; x2; x3]
                   (Z.to_nat (to_Z shift))))).
        2: {
          unfold shift_left_words.
          cbn [firstn shift_left_words_aux WL.to_Z_words].
          rewrite shld64_zero_low_spec.
          2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
          apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
          reflexivity. }
        change (firstn 4 (shift_left_words [x0; x1; x2; x3]
          (Z.to_nat (to_Z shift)))) with
          (firstn (length [x0; x1; x2; x3])
             (shift_left_words [x0; x1; x2; x3]
                (Z.to_nat (to_Z shift)))).
rewrite to_Z_words_firstn_shift_left_mod.
        2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
             apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
        unfold modulus256.
        replace (length [x0; x1; x2; x3]) with 4%nat by reflexivity.
        pose proof (spec_to_Z shift) as HshiftZ_left0.
        pose proof (spec_to_Z shift) as HshiftZ0.
        replace (Z.of_nat (Z.to_nat (to_Z shift))) with (to_Z shift)
          by (symmetry; apply Z2Nat.id; lia).
        reflexivity.
      * apply Z.ltb_ge in H64lt.
        pose proof (spec_to_Z shift) as HshiftZ.
        assert (Hshift64 :
          to_Z ((shift - shl 1 6)%Uint) = to_Z shift - 64).
        { rewrite spec_sub, H64.
          rewrite Z.mod_small.
          - lia.
          - split; [lia|].
            unfold base. rewrite width_is_64. simpl. lia. }
        assert (Hshift64lt : to_Z (shift - shl 1 6)%Uint < 64)
          by (rewrite Hshift64; lia).
        rewrite (bounded_shift_nat_correct word_width (shift - shl 1 6)%Uint
          ltac:(lia)
          ltac:(unfold word_width; rewrite width_is_64, Hshift64; lia)).
        replace (Z.to_nat (to_Z (shift - shl 1 6)%Uint)) with
          (Z.to_nat (to_Z shift - 64)) by (rewrite Hshift64; reflexivity).
        unfold uint256_to_words.
        cbn [w0 w1 w2 w3].
        cbn [WL.to_Z_words].
        rewrite spec_zero.
        assert (HLHS :
          0 + base WL.U64.width *
            (WL.U64.to_Z (shl x0 (Z.to_nat (to_Z shift - 64))) +
             base WL.U64.width *
             (WL.U64.to_Z (shld64 x1 x0 (Z.to_nat (to_Z shift - 64))) +
              base WL.U64.width *
              (WL.U64.to_Z (shld64 x2 x1 (Z.to_nat (to_Z shift - 64))) +
               base WL.U64.width * 0))) =
          modulus_words 1 *
            WL.to_Z_words
              [shl x0 (Z.to_nat (to_Z shift - 64));
               shld64 x1 x0 (Z.to_nat (to_Z shift - 64));
               shld64 x2 x1 (Z.to_nat (to_Z shift - 64))]).
        { unfold modulus_words, WL.modulus_words.
          cbn [WL.to_Z_words]. simpl.
          change (Z.pow_pos (base WL.U64.width) 1)
            with ((base WL.U64.width) ^ 1).
          rewrite Z.pow_1_r. ring. }
        rewrite HLHS.
        replace
          (WL.to_Z_words
             [shl x0 (Z.to_nat (to_Z shift - 64));
              shld64 x1 x0 (Z.to_nat (to_Z shift - 64));
              shld64 x2 x1 (Z.to_nat (to_Z shift - 64))])
          with
          (WL.to_Z_words
             (firstn 3
                (shift_left_words [x0; x1; x2]
                   (Z.to_nat (to_Z shift - 64))))).
        2: {
          unfold shift_left_words.
          cbn [firstn shift_left_words_aux WL.to_Z_words].
          rewrite shld64_zero_low_spec.
          2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
               apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
          reflexivity. }
        change (firstn 3 (shift_left_words [x0; x1; x2]
          (Z.to_nat (to_Z shift - 64)))) with
          (firstn (length [x0; x1; x2])
             (shift_left_words [x0; x1; x2]
                (Z.to_nat (to_Z shift - 64)))).
        rewrite to_Z_words_firstn_shift_left_mod.
        2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
             apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
        pose proof (spec_to_Z shift) as HshiftZ_left1.
        pose proof (spec_to_Z shift) as HshiftZ1.
        replace (Z.of_nat (Z.to_nat (to_Z shift - 64))) with (to_Z shift - 64)
          by (symmetry; apply Z2Nat.id; lia).
        rewrite modulus_words_scale_mod.
        unfold modulus256.
        fold (WL.to_Z_words [x0; x1; x2; x3]).
        rewrite (WL.to_Z_words_firstn_skipn [x0; x1; x2; x3] 3) by (simpl; lia).
        cbn [firstn skipn WL.to_Z_words].
        assert (Hpow64 : 2 ^ to_Z shift = modulus_words 1 * 2 ^ (to_Z shift - 64)).
        { unfold modulus_words, WL.modulus_words, base.
          rewrite width_is_64.
          change (Z.pow_pos (2 ^ 64) 1 * 2 ^ (to_Z shift - 64))
            with (((2 ^ 64) ^ 1) * 2 ^ (to_Z shift - 64)).
          rewrite Z.pow_1_r.
          replace (to_Z shift) with (64 + (to_Z shift - 64)) by lia.
          rewrite Z.pow_add_r by lia.
          replace (64 + (to_Z shift - 64) - 64) with (to_Z shift - 64) by lia.
          reflexivity. }
        rewrite Hpow64.
        rewrite modulus_words_add.
        ring_simplify.
        replace
          (((WL.U64.to_Z x0 +
             base WL.U64.width *
             (WL.U64.to_Z x1 +
              base WL.U64.width * (WL.U64.to_Z x2 + base WL.U64.width * 0)) +
             WL.modulus_words 3 * (WL.U64.to_Z x3 + base WL.U64.width * 0)) *
            (modulus_words 1 * 2 ^ (to_Z shift - 64))))
          with
          (modulus_words 1 * (to_Z_words [x0; x1; x2] * 2 ^ (to_Z shift - 64)) +
           modulus_words 4 *
             ((WL.U64.to_Z x3 + base WL.U64.width * 0) *
              2 ^ (to_Z shift - 64))).
        2: { change (modulus_words 4) with (modulus_words (1 + 3)).
             rewrite modulus_words_add.
             cbn [WL.to_Z_words].
             change (WL.modulus_words 3) with (modulus_words 3).
             nia. }
        rewrite Zplus_mod.
        rewrite (Z.mul_comm (modulus_words 4)
          (((WL.U64.to_Z x3 + base WL.U64.width * 0) * 2 ^ (to_Z shift - 64)))).
        assert (Hmod4nz : modulus_words 4 <> 0).
        { pose proof (WL.modulus_words_pos 4) as Hpos.
          intro Hz. change (WL.modulus_words 4) with (modulus_words 4) in Hpos.
          rewrite Hz in Hpos. lia. }
        rewrite Z.mod_mul by exact Hmod4nz.
        rewrite Z.add_0_r.
        cbn [WL.to_Z_words].
        rewrite <- modulus_words_add.
        rewrite Z.mod_mod by exact Hmod4nz.
        change (modulus_words (1 + 3)) with (modulus_words 4).
        reflexivity.
    + apply Z.ltb_ge in H128lt.
      destruct (to_Z shift <? 192) eqn:H192lt.
      * apply Z.ltb_lt in H192lt.
        pose proof (spec_to_Z shift) as HshiftZ.
        assert (Hshift128 :
          to_Z ((shift - shl 1 7)%Uint) = to_Z shift - 128).
        { rewrite spec_sub, H128.
          rewrite Z.mod_small.
          - lia.
          - split; [lia|].
            unfold base. rewrite width_is_64. simpl. lia. }
        assert (Hshift128lt : to_Z (shift - shl 1 7)%Uint < 64)
          by (rewrite Hshift128; lia).
        rewrite (bounded_shift_nat_correct word_width (shift - shl 1 7)%Uint
          ltac:(lia)
          ltac:(unfold word_width; rewrite width_is_64, Hshift128; lia)).
        replace (Z.to_nat (to_Z (shift - shl 1 7)%Uint)) with
          (Z.to_nat (to_Z shift - 128)) by (rewrite Hshift128; reflexivity).
        unfold uint256_to_words.
        cbn [w0 w1 w2 w3].
        cbn [WL.to_Z_words].
        rewrite !spec_zero.

        assert (HLHS2 :
          0 + base WL.U64.width *
            (0 + base WL.U64.width *
              (WL.U64.to_Z (shl x0 (Z.to_nat (to_Z shift - 128))) +
               base WL.U64.width *
               (WL.U64.to_Z (shld64 x1 x0 (Z.to_nat (to_Z shift - 128))) +
                base WL.U64.width * 0))) =
          modulus_words 2 *
            WL.to_Z_words
              [shl x0 (Z.to_nat (to_Z shift - 128));
               shld64 x1 x0 (Z.to_nat (to_Z shift - 128))]).
        { unfold modulus_words, WL.modulus_words.
          cbn [WL.to_Z_words]. simpl.
          change (Z.pow_pos (base WL.U64.width) 2) with ((base WL.U64.width) ^ 2).
          rewrite Z.pow_2_r. ring. }
        rewrite HLHS2.
        replace
          (WL.to_Z_words
             [shl x0 (Z.to_nat (to_Z shift - 128));
              shld64 x1 x0 (Z.to_nat (to_Z shift - 128))])
          with
          (WL.to_Z_words
             (firstn 2
                (shift_left_words [x0; x1]
                   (Z.to_nat (to_Z shift - 128))))).
        2: {
          unfold shift_left_words.
          cbn [firstn shift_left_words_aux WL.to_Z_words].
          rewrite shld64_zero_low_spec.
          2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
               apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
          reflexivity. }
        change (firstn 2 (shift_left_words [x0; x1]
          (Z.to_nat (to_Z shift - 128)))) with
          (firstn (length [x0; x1])
             (shift_left_words [x0; x1]
                (Z.to_nat (to_Z shift - 128)))).
        rewrite to_Z_words_firstn_shift_left_mod.
        2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
             apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
        pose proof (spec_to_Z shift) as HshiftZ_left2.
        pose proof (spec_to_Z shift) as HshiftZ2.
        replace (Z.of_nat (Z.to_nat (to_Z shift - 128))) with (to_Z shift - 128)
          by (symmetry; apply Z2Nat.id; lia).
        rewrite modulus_words_scale_mod.
        unfold modulus256.
        fold (WL.to_Z_words [x0; x1; x2; x3]).
        rewrite (WL.to_Z_words_firstn_skipn [x0; x1; x2; x3] 2) by (simpl; lia).
        cbn [firstn skipn WL.to_Z_words].
        assert (Hpow128 : 2 ^ to_Z shift = modulus_words 2 * 2 ^ (to_Z shift - 128)).
        { rewrite modulus_words_2.
          replace (to_Z shift) with (128 + (to_Z shift - 128)) by lia.
          rewrite Z.pow_add_r by lia.
          replace (128 + (to_Z shift - 128) - 128) with (to_Z shift - 128) by lia.
          reflexivity. }
        rewrite Hpow128.
        rewrite modulus_words_add.
        ring_simplify.
        replace
          (((WL.U64.to_Z x0 +
             base WL.U64.width * (WL.U64.to_Z x1 + base WL.U64.width * 0) +
             WL.modulus_words 2 *
             (WL.U64.to_Z x2 +
              base WL.U64.width * (WL.U64.to_Z x3 + base WL.U64.width * 0))) *
            (modulus_words 2 * 2 ^ (to_Z shift - 128))))
          with
          (modulus_words 2 * (to_Z_words [x0; x1] * 2 ^ (to_Z shift - 128)) +
           modulus_words 4 *
             (WL.to_Z_words [x2; x3] * 2 ^ (to_Z shift - 128))).
        2: { change (modulus_words 4) with (modulus_words (2 + 2)).
             rewrite modulus_words_add.
             cbn [WL.to_Z_words].
             change (WL.modulus_words 2) with (modulus_words 2).
             nia. }
        rewrite Zplus_mod.
        replace (modulus_words 4 * (to_Z_words [x2; x3] * 2 ^ (to_Z shift - 128)))
          with ((to_Z_words [x2; x3] * 2 ^ (to_Z shift - 128)) * modulus_words 4)
          by ring.
        assert (Hmod4nz : modulus_words 4 <> 0).
        { pose proof (WL.modulus_words_pos 4) as Hpos.
          intro Hz. change (WL.modulus_words 4) with (modulus_words 4) in Hpos.
          rewrite Hz in Hpos. lia. }
        rewrite Z.mod_mul by exact Hmod4nz.
        rewrite Z.add_0_r.
        change (length [x0; x1]) with 2%nat.
        rewrite <- modulus_words_add.
        rewrite Z.mod_mod by exact Hmod4nz.
        change (modulus_words (2 + 2)) with (modulus_words 4).
        reflexivity.
      * apply Z.ltb_ge in H192lt.
        pose proof (spec_to_Z shift) as HshiftZ.
        assert (Hshift192 :
          to_Z ((shift - shl (one + one + one)%Uint 6)%Uint) = to_Z shift - 192).
        { rewrite spec_sub, H192.
          rewrite Z.mod_small.
          - lia.
          - split; [lia|].
            unfold base. rewrite width_is_64. simpl. lia. }
        assert (Hshift192lt : to_Z (shift - shl (one + one + one)%Uint 6)%Uint < 64)
          by (rewrite Hshift192; lia).
        rewrite (bounded_shift_nat_correct word_width
          (shift - shl (one + one + one)%Uint 6)%Uint
          ltac:(lia)
          ltac:(unfold word_width; rewrite width_is_64, Hshift192; lia)).
        replace (Z.to_nat (to_Z (shift - shl (one + one + one)%Uint 6)%Uint)) with
          (Z.to_nat (to_Z shift - 192)) by (rewrite Hshift192; reflexivity).
        unfold uint256_to_words.
        cbn [w0 w1 w2 w3].
        cbn [WL.to_Z_words].
        rewrite !spec_zero.
        assert (HLHS3 :
          0 + base WL.U64.width *
            (0 + base WL.U64.width *
              (0 + base WL.U64.width *
                (WL.U64.to_Z (shl x0 (Z.to_nat (to_Z shift - 192))) +
                 base WL.U64.width * 0))) =
          modulus_words 3 *
            WL.to_Z_words [shl x0 (Z.to_nat (to_Z shift - 192))]).
        { change (modulus_words 3) with (modulus_words (2 + 1)).
          rewrite modulus_words_add.
          unfold modulus_words, WL.modulus_words.
          cbn [WL.to_Z_words]. simpl.
          change (Z.pow_pos (base WL.U64.width) 2) with ((base WL.U64.width) ^ 2).
          change (Z.pow_pos (base WL.U64.width) 1) with ((base WL.U64.width) ^ 1).
          rewrite Z.pow_2_r, Z.pow_1_r. ring. }
        rewrite HLHS3.
        replace
          (WL.to_Z_words [shl x0 (Z.to_nat (to_Z shift - 192))])
          with
          (WL.to_Z_words
             (firstn 1
                (shift_left_words [x0]
                   (Z.to_nat (to_Z shift - 192))))).
        2: {
          unfold shift_left_words.
          cbn [firstn shift_left_words_aux WL.to_Z_words].
          rewrite shld64_zero_low_spec.
          2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
               apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
          reflexivity. }
        change (firstn 1 (shift_left_words [x0]
          (Z.to_nat (to_Z shift - 192)))) with
          (firstn (length [x0])
             (shift_left_words [x0]
                (Z.to_nat (to_Z shift - 192)))).
        rewrite to_Z_words_firstn_shift_left_mod.
        2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
             apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
        pose proof (spec_to_Z shift) as HshiftZ_left3.
        pose proof (spec_to_Z shift) as HshiftZ3.
        replace (Z.of_nat (Z.to_nat (to_Z shift - 192))) with (to_Z shift - 192)
          by (symmetry; apply Z2Nat.id; lia).
        rewrite modulus_words_scale_mod.
        unfold modulus256.
        fold (WL.to_Z_words [x0; x1; x2; x3]).
        rewrite (WL.to_Z_words_firstn_skipn [x0; x1; x2; x3] 1) by (simpl; lia).
        cbn [firstn skipn WL.to_Z_words].
        assert (Hpow192 : 2 ^ to_Z shift = modulus_words 3 * 2 ^ (to_Z shift - 192)).
        { rewrite modulus_words_3.
          replace (to_Z shift) with (192 + (to_Z shift - 192)) by lia.
          rewrite Z.pow_add_r by lia.
          replace (192 + (to_Z shift - 192) - 192) with (to_Z shift - 192) by lia.
          reflexivity. }
        rewrite Hpow192.
        rewrite modulus_words_add.
        ring_simplify.
        replace
          ((((WL.U64.to_Z x0 +
              WL.modulus_words 1 *
              (WL.U64.to_Z x1 +
               base WL.U64.width *
               (WL.U64.to_Z x2 + base WL.U64.width * (WL.U64.to_Z x3 + base WL.U64.width * 0)))) *
             (modulus_words 3 * 2 ^ (to_Z shift - 192)))
            mod modulus_words 4))
          with
          ((modulus_words 3 * (to_Z_words [x0] * 2 ^ (to_Z shift - 192)) +
            modulus_words 4 *
              (WL.to_Z_words [x1; x2; x3] * 2 ^ (to_Z shift - 192)))
           mod modulus_words 4).
        2: { f_equal.
             change (modulus_words 4) with (modulus_words (3 + 1)).
             rewrite modulus_words_add.
             cbn [WL.to_Z_words].
             change (WL.modulus_words 1) with (modulus_words 1).
             ring. }
        assert (Hrhs :
          (((WL.U64.to_Z x0 + base WL.U64.width * 0 +
              WL.modulus_words 1 *
                (WL.U64.to_Z x1 +
                 base WL.U64.width *
                   (WL.U64.to_Z x2 +
                    base WL.U64.width * (WL.U64.to_Z x3 + base WL.U64.width * 0)))) *
             (modulus_words 3 * 2 ^ (to_Z shift - 192)))
           mod modulus_words 4) =
          ((modulus_words 3 * (to_Z_words [x0] * 2 ^ (to_Z shift - 192)) +
            modulus_words 4 *
              (WL.to_Z_words [x1; x2; x3] * 2 ^ (to_Z shift - 192)))
           mod modulus_words 4)).
        { f_equal.
          change (modulus_words 4) with (modulus_words (3 + 1)).
          rewrite modulus_words_add.
          cbn [WL.to_Z_words].
          change (WL.modulus_words 1) with (modulus_words 1).
          ring. }
        rewrite Hrhs. clear Hrhs.
        rewrite Zplus_mod.
        rewrite (Z.mul_comm (modulus_words 4)
          (WL.to_Z_words [x1; x2; x3] * 2 ^ (to_Z shift - 192))).
        assert (Hmod4nz : modulus_words 4 <> 0).
        { pose proof (WL.modulus_words_pos 4) as Hpos.
          intro Hz. change (WL.modulus_words 4) with (modulus_words 4) in Hpos.
          rewrite Hz in Hpos. lia. }
        rewrite Z.mod_mul by exact Hmod4nz.
        rewrite Z.add_0_r.
        change (length [x0]) with 1%nat.
        rewrite <- modulus_words_add.
        rewrite Z.mod_mod by exact Hmod4nz.
        change (modulus_words (3 + 1)) with (modulus_words 4).
        reflexivity.
  - apply Z.ltb_ge in H256lt.
    cbn. rewrite !spec_zero. lia.
Qed.

Lemma to_Z_uint256_zero_high : forall s0 s1 s2 s3,
  to_Z s1 = 0 -> to_Z s2 = 0 -> to_Z s3 = 0 ->
  to_Z_uint256 (mk_uint256 s0 s1 s2 s3) = to_Z s0.
Proof.
  intros s0 s1 s2 s3 H1 H2 H3.
  unfold to_Z_uint256.
  cbn.
  rewrite H1, H2, H3.
  lia.
Qed.

Lemma to_Z_uint256_high_ge_base : forall s0 s1 s2 s3,
  0 < to_Z s1 \/ 0 < to_Z s2 \/ 0 < to_Z s3 ->
  base width <= to_Z_uint256 (mk_uint256 s0 s1 s2 s3).
Proof.
  intros s0 s1 s2 s3 Hhi.
  unfold to_Z_uint256.
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
  to_Z_uint256 (shift_left_uint256 x shift) =
    if Z.ltb (to_Z_uint256 shift) (base width)
    then if Z.ltb (to_Z_uint256 shift) 256
         then (to_Z_uint256 x * 2 ^ to_Z_uint256 shift) mod modulus256
         else 0
    else 0.
Proof.
  intros x [s0 s1 s2 s3].
  unfold shift_left_uint256.
  cbn [w0 w1 w2 w3 andb].
  destruct (s1 =? 0)%Uint eqn:Hs1;
    destruct (s2 =? 0)%Uint eqn:Hs2;
    destruct (s3 =? 0)%Uint eqn:Hs3;
    cbn [andb].
  - rewrite spec_eqb in Hs1. apply Z.eqb_eq in Hs1. rewrite spec_zero in Hs1.
    rewrite spec_eqb in Hs2. apply Z.eqb_eq in Hs2. rewrite spec_zero in Hs2.
    rewrite spec_eqb in Hs3. apply Z.eqb_eq in Hs3. rewrite spec_zero in Hs3.
    rewrite shift_left_uint256_aux_correct.
    rewrite (to_Z_uint256_zero_high s0 s1 s2 s3 Hs1 Hs2 Hs3).
    assert (Hltbase : (to_Z s0 <? base width) = true).
    { apply Z.ltb_lt.
      pose proof (spec_to_Z s0) as H0.
      lia. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs3. apply Z.eqb_neq in Hs3. rewrite spec_zero in Hs3.
    assert (Hs3p : 0 < to_Z s3).
    { pose proof (spec_to_Z s3) as H3.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      right. right. exact Hs3p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs2. apply Z.eqb_neq in Hs2. rewrite spec_zero in Hs2.
    assert (Hs2p : 0 < to_Z s2).
    { pose proof (spec_to_Z s2) as H2.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      right. left. exact Hs2p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs2. apply Z.eqb_neq in Hs2. rewrite spec_zero in Hs2.
    assert (Hs2p : 0 < to_Z s2).
    { pose proof (spec_to_Z s2) as H2.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      right. left. exact Hs2p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase : (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width) = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
Qed.

Lemma shrd64_zero_high_spec : forall low s,
  (s < Pos.to_nat U64.width)%nat ->
  to_Z (shrd64 zero low s) = to_Z (shr low s).
Proof.
  intros low s Hs.
  rewrite DP.shrd64_spec by exact Hs.
  rewrite spec_zero, spec_shr.
  rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.add_0_r.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (spec_to_Z low) as Hlow.
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound.
      * apply Z.pow_pos_nonneg; lia.
      * pose proof (Z.pow_pos_nonneg 2 1 ltac:(lia)) as Hpow.
        nia.
Qed.

Lemma to_Z_low_6_mask : to_Z (sub (shl one 6) one) = 63.
Proof.
  pose proof (to_Z_shl_one 6 ltac:(rewrite width_is_64; simpl; lia)) as H64.
  rewrite spec_sub, H64, spec_one.
  rewrite Z.mod_small.
  - reflexivity.
  - split.
    + lia.
    + unfold base. rewrite width_is_64. simpl.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      pose proof (Z.pow_pos_nonneg 2 64 ltac:(lia)) as Hpow.
      nia.
Qed.

Lemma to_Z_low_7_mask : to_Z (sub (shl one 7) one) = 127.
Proof.
  pose proof (to_Z_shl_one 7 ltac:(rewrite width_is_64; simpl; lia)) as H128.
  rewrite spec_sub, H128, spec_one.
  rewrite Z.mod_small.
  - reflexivity.
  - split; [lia|].
    unfold base. rewrite width_is_64. simpl.
    change (Z.pow_pos 2 64) with (2 ^ 64).
    pose proof (Z.pow_pos_nonneg 2 64 ltac:(lia)) as Hpow.
    nia.
Qed.

Lemma to_Z_land_shift_and_63 : forall shift,
  to_Z (land shift (sub (shl one 6) one)) = to_Z shift mod 64.
Proof.
  intro shift.
  rewrite spec_land, to_Z_low_6_mask.
  change 63 with (Z.ones 6).
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small.
  - reflexivity.
  - split.
    + apply Z.mod_pos_bound. lia.
    + eapply Z.lt_trans.
      * apply Z.mod_pos_bound. lia.
      * unfold base. rewrite width_is_64. simpl. lia.
Qed.

Lemma to_Z_land_shift_and_127 : forall shift,
  to_Z (land shift (sub (shl one 7) one)) = to_Z shift mod 128.
Proof.
  intro shift.
  rewrite spec_land, to_Z_low_7_mask.
  change 127 with (Z.ones 7).
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small.
  - reflexivity.
  - split.
    + apply Z.mod_pos_bound. lia.
    + eapply Z.lt_trans.
      * apply Z.mod_pos_bound. lia.
      * unfold base. rewrite width_is_64. simpl. lia.
Qed.

Lemma to_Z_uint256_div_modulus_words_1 : forall x0 x1 x2 x3,
  to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / modulus_words 1 =
    to_Z_words [x1; x2; x3].
Proof.
  intros x0 x1 x2 x3.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3 WL.to_Z_words].
  replace
    (to_Z x0 +
      base width *
        (to_Z x1 + base width * (to_Z x2 + base width * (to_Z x3 + base width * 0))))
    with (to_Z x0 + modulus_words 1 * to_Z_words [x1; x2; x3]).
  2:{ rewrite modulus_words_1. cbn [WL.to_Z_words].
      unfold base. rewrite width_is_64. nia. }
  rewrite Z.mul_comm.
  rewrite Z.div_add by (pose proof (WL.modulus_words_pos 1); lia).
  rewrite Z.div_small.
  - reflexivity.
  - pose proof (spec_to_Z x0) as H0.
    rewrite modulus_words_1.
    unfold base in H0. rewrite width_is_64 in H0.
    exact H0.
Qed.

Lemma to_Z_uint256_div_modulus_words_2 : forall x0 x1 x2 x3,
  to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / modulus_words 2 =
    to_Z_words [x2; x3].
Proof.
  intros x0 x1 x2 x3.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3 WL.to_Z_words].
  replace
    (to_Z x0 +
      base width *
        (to_Z x1 + base width * (to_Z x2 + base width * (to_Z x3 + base width * 0))))
    with (to_Z_words [x0; x1] + modulus_words 2 * to_Z_words [x2; x3]).
  2:{ rewrite modulus_words_2. cbn [WL.to_Z_words].
      unfold base. rewrite width_is_64. nia. }
  rewrite Z.mul_comm.
  rewrite Z.div_add by (pose proof (WL.modulus_words_pos 2); lia).
  rewrite Z.div_small.
  - reflexivity.
  - pose proof (WL.to_Z_words_bound [x0; x1]) as Hlow.
    change (length [x0; x1]) with 2%nat in Hlow.
    rewrite modulus_words_2.
    rewrite modulus_words_2 in Hlow.
    exact Hlow.
Qed.

Lemma to_Z_uint256_div_modulus_words_3 : forall x0 x1 x2 x3,
  to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / modulus_words 3 =
    to_Z_words [x3].
Proof.
  intros x0 x1 x2 x3.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3 WL.to_Z_words].
  replace
    (to_Z x0 +
      base width *
        (to_Z x1 + base width * (to_Z x2 + base width * (to_Z x3 + base width * 0))))
    with (to_Z_words [x0; x1; x2] + modulus_words 3 * to_Z_words [x3]).
  2:{ rewrite modulus_words_3. cbn [WL.to_Z_words].
      unfold base. rewrite width_is_64. nia. }
  rewrite Z.mul_comm.
  rewrite Z.div_add by (pose proof (WL.modulus_words_pos 3); lia).
  rewrite Z.div_small.
  - reflexivity.
  - pose proof (WL.to_Z_words_bound [x0; x1; x2]) as Hlow.
    change (length [x0; x1; x2]) with 3%nat in Hlow.
    rewrite modulus_words_3.
    rewrite modulus_words_3 in Hlow.
    exact Hlow.
Qed.

Theorem shift_right_uint256_aux_correct : forall x shift,
  to_Z shift < 256 ->
  to_Z_uint256 (shift_right_uint256_aux RightShiftLogical zero x shift) =
    to_Z_uint256 x / 2 ^ to_Z shift.
Proof.
  intros [x0 x1 x2 x3] shift H256lt.
  unfold shift_right_uint256_aux, to_Z_uint256.
  cbn [uint256_to_words].
  pose proof (to_Z_shl_one 6 ltac:(rewrite width_is_64; simpl; lia)) as H64.
  pose proof (to_Z_shl_one 7 ltac:(rewrite width_is_64; simpl; lia)) as H128.
  assert (H192 : to_Z (shl (one + one + one)%Uint 6) = 192).
  { rewrite spec_shl, !spec_add, !spec_one.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small.
    - repeat rewrite Z.mod_small by (unfold base; rewrite width_is_64; simpl; lia).
      nia.
    - repeat rewrite Z.mod_small by (unfold base; rewrite width_is_64; simpl; lia).
      unfold base. rewrite width_is_64. simpl. lia. }
  rewrite !spec_ltb.
  rewrite H64, H128, H192.
  replace (2 ^ Z.of_nat 7) with 128 in * by reflexivity.
  replace (2 ^ Z.of_nat 6) with 64 in * by reflexivity.
  destruct (to_Z shift <? 128) eqn:H128lt.
  + apply Z.ltb_lt in H128lt.
    destruct (to_Z shift <? 64) eqn:H64lt.
    * apply Z.ltb_lt in H64lt.
      assert (Hmask0 :
        to_Z (land shift (sub (shl one 6) one)) = to_Z shift).
      { rewrite to_Z_land_shift_and_63.
        pose proof (spec_to_Z shift) as HshiftZ.
        apply Z.mod_small. lia. }
      rewrite (bounded_shift_nat_correct word_width (land shift (sub (shl one 6) one))
        ltac:(lia)
        ltac:(unfold word_width; rewrite width_is_64, Hmask0; exact H64lt)).
      replace
        (Z.to_nat (to_Z (land shift (sub (shl one 6) one))))
        with (Z.to_nat (to_Z shift))
        by (rewrite Hmask0; reflexivity).
      rewrite (bounded_shift_nat_correct word_width shift ltac:(lia)
        ltac:(unfold word_width; rewrite width_is_64; exact H64lt)).
      unfold uint256_to_words.
      cbn [w0 w1 w2 w3].
      replace
        (to_Z_words
           [shrd64 x1 x0 (Z.to_nat (to_Z shift));
            shrd64 x2 x1 (Z.to_nat (to_Z shift));
            shrd64 x3 x2 (Z.to_nat (to_Z shift));
            shr x3 (Z.to_nat (to_Z shift))])
        with
        (to_Z_words
           (shift_right_words [x0; x1; x2; x3]
              (Z.to_nat (to_Z shift)))).
      2: { unfold shift_right_words.
           cbn [shift_right_words WL.to_Z_words hd].
           rewrite shrd64_zero_high_spec.
           2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
                pose proof (spec_to_Z shift) as HshiftZ.
                apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
           reflexivity. }
      rewrite DP.shift_right_words_correct.
      2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
           pose proof (spec_to_Z shift) as HshiftZ.
           apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
      pose proof (spec_to_Z shift) as HshiftZ0.
      replace (Z.of_nat (Z.to_nat (to_Z shift))) with (to_Z shift)
        by (symmetry; apply Z2Nat.id; lia).
      reflexivity.
    * apply Z.ltb_ge in H64lt.
      assert (Hmask64 :
        to_Z (land shift (sub (shl one 6) one)) = to_Z shift - 64).
      { rewrite to_Z_land_shift_and_63.
        symmetry; apply Z.mod_unique with (q := 1); lia. }
      rewrite (bounded_shift_nat_correct word_width
        (land shift (sub (shl one 6) one))
        ltac:(lia)
        ltac:(unfold word_width; rewrite width_is_64, Hmask64; lia)).
      replace (Z.to_nat (to_Z (land shift (sub (shl one 6) one)))) with
        (Z.to_nat (to_Z shift - 64)) by (rewrite Hmask64; reflexivity).
      unfold uint256_to_words.
      cbn [w0 w1 w2 w3].
      replace
        (to_Z_words
           [shrd64 x2 x1 (Z.to_nat (to_Z shift - 64));
            shrd64 x3 x2 (Z.to_nat (to_Z shift - 64));
            shr x3 (Z.to_nat (to_Z shift - 64)); zero])
        with
        (to_Z_words
           (shift_right_words [x1; x2; x3]
              (Z.to_nat (to_Z shift - 64)))).
      2: { unfold shift_right_words.
           cbn [shift_right_words WL.to_Z_words hd].
           rewrite shrd64_zero_high_spec.
           2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
                pose proof (spec_to_Z shift) as HshiftZ.
                apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
           rewrite spec_zero.
           replace (base WL.U64.width * (0 + base WL.U64.width * 0)) with 0
             by ring.
           replace (base WL.U64.width * 0) with 0 by ring.
           reflexivity. }
      rewrite DP.shift_right_words_correct.
      2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
           pose proof (spec_to_Z shift) as HshiftZ.
           apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
      rewrite <- (to_Z_uint256_div_modulus_words_1 x0 x1 x2 x3).
      pose proof (spec_to_Z shift) as HshiftZ1.
      replace (Z.of_nat (Z.to_nat (to_Z shift - 64))) with (to_Z shift - 64)
        by (symmetry; apply Z2Nat.id; lia).
      rewrite Z.div_div.
      2: { rewrite modulus_words_1. lia. }
      2: { apply Z.pow_pos_nonneg; lia. }
      assert (Hpow64 : 2 ^ to_Z shift = modulus_words 1 * 2 ^ (to_Z shift - 64)).
      { rewrite modulus_words_1.
        replace (to_Z shift) with (64 + (to_Z shift - 64)) by lia.
        rewrite Z.pow_add_r by lia.
        replace (64 + (to_Z shift - 64) - 64) with (to_Z shift - 64) by lia.
        reflexivity. }
      rewrite Hpow64.
      reflexivity.
  + apply Z.ltb_ge in H128lt.
    destruct (to_Z shift <? 192) eqn:H192lt.
    * apply Z.ltb_lt in H192lt.
      assert (Hmask128_tail :
        to_Z (land shift (sub (shl one 6) one)) = to_Z shift - 128).
      { rewrite to_Z_land_shift_and_63.
        symmetry; apply Z.mod_unique with (q := 2); lia. }
      assert (Hmask128_local :
        to_Z (land shift (sub (shl one 7) one)) = to_Z shift - 128).
      { rewrite to_Z_land_shift_and_127.
        symmetry; apply Z.mod_unique with (q := 1); lia. }
      rewrite (bounded_shift_nat_correct word_width
        (land shift (sub (shl one 6) one))
        ltac:(lia)
        ltac:(unfold word_width; rewrite width_is_64, Hmask128_tail; lia)).
      replace (Z.to_nat (to_Z (land shift (sub (shl one 6) one)))) with
        (Z.to_nat (to_Z shift - 128))
        by (rewrite Hmask128_tail; reflexivity).
      rewrite (bounded_shift_nat_correct word_width
        (land shift (sub (shl one 7) one))
        ltac:(lia)
        ltac:(unfold word_width; rewrite width_is_64, Hmask128_local; lia)).
      replace (Z.to_nat (to_Z (land shift (sub (shl one 7) one)))) with
        (Z.to_nat (to_Z shift - 128)) by (rewrite Hmask128_local; reflexivity).
      unfold uint256_to_words.
      cbn [w0 w1 w2 w3].
      replace
        (to_Z_words
           [shrd64 x3 x2 (Z.to_nat (to_Z shift - 128));
            shr x3 (Z.to_nat (to_Z shift - 128)); zero; zero])
        with
        (to_Z_words
           (shift_right_words [x2; x3]
              (Z.to_nat (to_Z shift - 128)))).
      2: { unfold shift_right_words.
           cbn [shift_right_words WL.to_Z_words hd].
           rewrite shrd64_zero_high_spec.
           2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
                pose proof (spec_to_Z shift) as HshiftZ.
                apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
           replace
             (base WL.U64.width * (base WL.U64.width * (base WL.U64.width * 0)))
             with 0 by ring.
           replace (base WL.U64.width * 0) with 0 by ring.
           rewrite !spec_zero.
           ring. }
      rewrite DP.shift_right_words_correct.
      2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
           pose proof (spec_to_Z shift) as HshiftZ.
           apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
      rewrite <- (to_Z_uint256_div_modulus_words_2 x0 x1 x2 x3).
      pose proof (spec_to_Z shift) as HshiftZ2.
      replace (Z.of_nat (Z.to_nat (to_Z shift - 128))) with (to_Z shift - 128)
        by (symmetry; apply Z2Nat.id; lia).
      rewrite Z.div_div.
      2: { rewrite modulus_words_2. lia. }
      2: { apply Z.pow_pos_nonneg; lia. }
      assert (Hpow128 : 2 ^ to_Z shift = modulus_words 2 * 2 ^ (to_Z shift - 128)).
      { rewrite modulus_words_2.
        replace (to_Z shift) with (128 + (to_Z shift - 128)) by lia.
        rewrite Z.pow_add_r by lia.
        replace (128 + (to_Z shift - 128) - 128) with (to_Z shift - 128) by lia.
        reflexivity. }
      rewrite Hpow128.
      reflexivity.
    * apply Z.ltb_ge in H192lt.
      assert (Hmask192 :
        to_Z (land shift (sub (shl one 6) one)) = to_Z shift - 192).
      { rewrite to_Z_land_shift_and_63.
        symmetry; apply Z.mod_unique with (q := 3); lia. }
      rewrite (bounded_shift_nat_correct word_width
        (land shift (sub (shl one 6) one))
        ltac:(lia)
        ltac:(unfold word_width; rewrite width_is_64, Hmask192; lia)).
      replace
        (Z.to_nat (to_Z (land shift (sub (shl one 6) one))))
        with (Z.to_nat (to_Z shift - 192))
        by (rewrite Hmask192; reflexivity).
      unfold uint256_to_words.
      cbn [w0 w1 w2 w3].
      replace
        (to_Z_words [shr x3 (Z.to_nat (to_Z shift - 192)); zero; zero; zero])
        with
        (to_Z_words
           (shift_right_words [x3]
              (Z.to_nat (to_Z shift - 192)))).
      2: { unfold shift_right_words.
           cbn [shift_right_words WL.to_Z_words hd].
           rewrite shrd64_zero_high_spec.
           2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
                pose proof (spec_to_Z shift) as HshiftZ.
                apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
           replace
             (base WL.U64.width *
                (base WL.U64.width * (base WL.U64.width * (base WL.U64.width * 0))))
             with 0 by ring.
           replace (base WL.U64.width * 0) with 0 by ring.
           rewrite !spec_zero.
           ring. }
      rewrite DP.shift_right_words_correct.
      2: { rewrite width_is_64. change (Pos.to_nat 64) with 64%nat.
           pose proof (spec_to_Z shift) as HshiftZ.
           apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. lia. }
      rewrite <- (to_Z_uint256_div_modulus_words_3 x0 x1 x2 x3).
      pose proof (spec_to_Z shift) as HshiftZ3.
      replace (Z.of_nat (Z.to_nat (to_Z shift - 192))) with (to_Z shift - 192)
        by (symmetry; apply Z2Nat.id; lia).
      rewrite Z.div_div.
      2: { rewrite modulus_words_3. lia. }
      2: { apply Z.pow_pos_nonneg; lia. }
      assert (Hpow192 : 2 ^ to_Z shift = modulus_words 3 * 2 ^ (to_Z shift - 192)).
      { rewrite modulus_words_3.
        replace (to_Z shift) with (192 + (to_Z shift - 192)) by lia.
        rewrite Z.pow_add_r by lia.
        replace (192 + (to_Z shift - 192) - 192) with (to_Z shift - 192) by lia.
        reflexivity. }
      rewrite Hpow192.
      reflexivity.
Qed.

Theorem shift_right_uint256_correct : forall x shift,
  to_Z_uint256 (shift_right_uint256 x shift) =
    if Z.ltb (to_Z_uint256 shift) (base width)
    then to_Z_uint256 x / 2 ^ to_Z_uint256 shift
    else 0.
Proof.
  intros x [s0 s1 s2 s3].
  pose proof (to_Z_shl_one 8 ltac:(rewrite width_is_64; simpl; lia)) as H256.
  unfold shift_right_uint256.
  cbn [w0 w1 w2 w3 andb].
  destruct (s1 =? 0)%Uint eqn:Hs1;
    destruct (s2 =? 0)%Uint eqn:Hs2;
    destruct (s3 =? 0)%Uint eqn:Hs3;
    cbn [andb].
  - destruct (s0 <? shl 1 8)%Uint eqn:Hs0.
    + rewrite spec_eqb in Hs1. apply Z.eqb_eq in Hs1. rewrite spec_zero in Hs1.
      rewrite spec_eqb in Hs2. apply Z.eqb_eq in Hs2. rewrite spec_zero in Hs2.
      rewrite spec_eqb in Hs3. apply Z.eqb_eq in Hs3. rewrite spec_zero in Hs3.
      rewrite spec_ltb in Hs0.
      rewrite H256 in Hs0.
      replace (2 ^ Z.of_nat 8) with 256 in Hs0 by reflexivity.
      rewrite shift_right_uint256_aux_correct.
      2: { apply Z.ltb_lt in Hs0. lia. }
      rewrite (to_Z_uint256_zero_high s0 s1 s2 s3 Hs1 Hs2 Hs3).
      assert (Hltbase : (to_Z s0 <? base width) = true).
      { apply Z.ltb_lt.
        pose proof (spec_to_Z s0) as H0.
        lia. }
      rewrite Hltbase.
      reflexivity.
    + rewrite to_Z_zero_uint256.
      rewrite spec_eqb in Hs1. apply Z.eqb_eq in Hs1. rewrite spec_zero in Hs1.
      rewrite spec_eqb in Hs2. apply Z.eqb_eq in Hs2. rewrite spec_zero in Hs2.
      rewrite spec_eqb in Hs3. apply Z.eqb_eq in Hs3. rewrite spec_zero in Hs3.
      rewrite spec_ltb in Hs0.
      rewrite H256 in Hs0.
      replace (2 ^ Z.of_nat 8) with 256 in Hs0 by reflexivity.
      rewrite (to_Z_uint256_zero_high s0 s1 s2 s3 Hs1 Hs2 Hs3).
      assert (Hltbase : (to_Z s0 <? base width) = true).
      { apply Z.ltb_lt.
        pose proof (spec_to_Z s0) as H0.
        lia. }
      rewrite Hltbase.
      symmetry.
      apply Z.div_small.
      pose proof (to_Z_uint256_bounds x) as Hx.
      split.
      * lia.
      * assert (Hmod : modulus256 = 2 ^ 256).
        { unfold modulus256.
          change (modulus_words 4) with (modulus_words (3 + 1)).
          rewrite modulus_words_add, modulus_words_3, modulus_words_1.
          replace 256 with (192 + 64) by lia.
          rewrite Z.pow_add_r by lia.
          reflexivity. }
        rewrite Hmod in Hx.
        apply Z.ltb_ge in Hs0.
        assert (Hpow : 2 ^ 256 <= 2 ^ to_Z s0).
        { apply Z.pow_le_mono_r; lia. }
        lia.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs3. apply Z.eqb_neq in Hs3. rewrite spec_zero in Hs3.
    assert (Hs3p : 0 < to_Z s3).
    { pose proof (spec_to_Z s3) as H3.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      right. right. exact Hs3p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs2. apply Z.eqb_neq in Hs2. rewrite spec_zero in Hs2.
    assert (Hs2p : 0 < to_Z s2).
    { pose proof (spec_to_Z s2) as H2.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      right. left. exact Hs2p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs2. apply Z.eqb_neq in Hs2. rewrite spec_zero in Hs2.
    assert (Hs2p : 0 < to_Z s2).
    { pose proof (spec_to_Z s2) as H2.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      right. left. exact Hs2p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
  - rewrite to_Z_zero_uint256.
    rewrite spec_eqb in Hs1. apply Z.eqb_neq in Hs1. rewrite spec_zero in Hs1.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as H1.
      lia. }
    assert (Hltbase :
      (to_Z_uint256 {| w0 := s0; w1 := s1; w2 := s2; w3 := s3 |} <? base width)
        = false).
    { apply Z.ltb_ge.
      apply to_Z_uint256_high_ge_base.
      left. exact Hs1p. }
    rewrite Hltbase.
    reflexivity.
Qed.

Lemma to_Z_shr : forall x n,
  to_Z (shr x n) = to_Z x / 2 ^ Z.of_nat n.
Proof.
  intros x n.
  rewrite spec_shr.
  rewrite Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (spec_to_Z x) as Hx.
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound.
      * apply Z.pow_pos_nonneg; lia.
      * nia.
Qed.

Lemma to_Z_low_mask : forall n,
  (n < Pos.to_nat U64.width)%nat ->
  to_Z (sub (shl one n) one) = 2 ^ Z.of_nat n - 1.
Proof.
  intros n Hn.
  rewrite spec_sub, spec_shl, spec_one.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.mul_1_l.
  rewrite (Z.mod_small (2 ^ Z.of_nat n) (base width)).
  2:{
    split.
    + apply Z.pow_nonneg. lia.
    + pose proof Hn as Hn'.
      rewrite width_is_64 in Hn'.
      apply Nat2Z.inj_lt in Hn'.
      unfold base. rewrite width_is_64. simpl in *.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      apply Z.pow_lt_mono_r; lia. }
  rewrite (Z.mod_small (2 ^ Z.of_nat n - 1) (base width)).
  2:{
    split.
    + pose proof (Z.pow_pos_nonneg 2 (Z.of_nat n) ltac:(lia)) as Hpow.
      nia.
    + unfold base. rewrite width_is_64. simpl.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      pose proof Hn as Hn'.
      rewrite width_is_64 in Hn'.
      apply Nat2Z.inj_lt in Hn'.
      assert (Hltpow : 2 ^ Z.of_nat n < 2 ^ 64).
      { apply Z.pow_lt_mono_r; lia. }
      lia. }
  reflexivity.
Qed.

Lemma to_Z_land_low_mask : forall x n,
  (n < Pos.to_nat U64.width)%nat ->
  to_Z (land x (sub (shl one n) one)) = to_Z x mod 2 ^ Z.of_nat n.
Proof.
  intros x n Hn.
  rewrite spec_land, to_Z_low_mask by exact Hn.
  replace (2 ^ Z.of_nat n - 1) with (Z.ones (Z.of_nat n)).
  2:{ rewrite Z.ones_equiv. lia. }
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (spec_to_Z x) as Hx.
    split.
    + apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
    + pose proof Hn as Hn'.
      rewrite width_is_64 in Hn'.
      apply Nat2Z.inj_lt in Hn'.
      unfold base. rewrite width_is_64. simpl in *.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      assert (Hltpow : 2 ^ Z.of_nat n < 2 ^ 64).
      { apply Z.pow_lt_mono_r; lia. }
      eapply Z.lt_trans.
      * apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
      * exact Hltpow.
Qed.

Lemma to_Z_uint256_lt_base_zero_high : forall s0 s1 s2 s3,
  to_Z_uint256 (mk_uint256 s0 s1 s2 s3) < base width ->
  to_Z s1 = 0 /\ to_Z s2 = 0 /\ to_Z s3 = 0.
Proof.
  intros s0 s1 s2 s3 Hlt.
  assert (Hs1z : to_Z s1 = 0).
  { destruct (Z.eq_dec (to_Z s1) 0) as [Hs1z|Hs1nz]; auto.
    assert (Hs1p : 0 < to_Z s1).
    { pose proof (spec_to_Z s1) as Hs1. lia. }
    pose proof (to_Z_uint256_high_ge_base s0 s1 s2 s3 (or_introl Hs1p)) as Hge.
    lia. }
  assert (Hs2z : to_Z s2 = 0).
  { destruct (Z.eq_dec (to_Z s2) 0) as [Hs2z|Hs2nz]; auto.
    assert (Hs2p : 0 < to_Z s2).
    { pose proof (spec_to_Z s2) as Hs2. lia. }
    pose proof (to_Z_uint256_high_ge_base s0 s1 s2 s3 (or_intror (or_introl Hs2p)))
      as Hge.
    lia. }
  assert (Hs3z : to_Z s3 = 0).
  { destruct (Z.eq_dec (to_Z s3) 0) as [Hs3z|Hs3nz]; auto.
    assert (Hs3p : 0 < to_Z s3).
    { pose proof (spec_to_Z s3) as Hs3. lia. }
    pose proof (to_Z_uint256_high_ge_base s0 s1 s2 s3
      (or_intror (or_intror Hs3p))) as Hge.
    lia. }
  repeat split; assumption.
Qed.

Lemma to_Z_asr_63 : forall x,
  to_Z (asr x 63) =
    if to_Z x <? base width / 2 then 0 else base width - 1.
Proof.
  intro x.
  rewrite spec_asr.
  destruct (to_Z x <? base width / 2) eqn:Hltb.
  - apply Z.ltb_lt in Hltb.
    rewrite Z.sub_0_r.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hdiv : to_Z x / 2 ^ Z.of_nat 63 = 0).
    { apply Z.div_small.
      pose proof (spec_to_Z x) as Hx.
      unfold base in Hltb. rewrite width_is_64 in Hltb. simpl in Hltb.
      change (Z.pow_pos 2 64 / 2) with (2 ^ Z.of_nat 63) in Hltb.
      pose proof (Z.pow_pos_nonneg 2 (Z.of_nat 63) ltac:(lia)) as Hpow.
      lia. }
    rewrite Hdiv.
    rewrite Z.mod_small.
    + reflexivity.
    + split; [lia|].
      unfold base. rewrite width_is_64. simpl.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      pose proof (Z.pow_pos_nonneg 2 64 ltac:(lia)) as Hpow.
      nia.
  - apply Z.ltb_ge in Hltb.
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hdiv : (to_Z x - base width) / 2 ^ Z.of_nat 63 = -1).
    { pose proof (spec_to_Z x) as Hx.
      unfold base in Hltb |- *. rewrite width_is_64 in Hltb |- *. simpl in *.
      change (2 ^ 64 / 2) with (2 ^ Z.of_nat 63) in Hltb.
      assert (Hge63 : 2 ^ Z.of_nat 63 <= to_Z x) by exact Hltb.
      assert (Hrange : - 2 ^ Z.of_nat 63 <= to_Z x - 2 ^ 64 < 0).
      { split.
        - apply Z.add_le_mono_r with (p := - 2 ^ 64) in Hge63.
          replace (2 ^ Z.of_nat 63 + - 2 ^ 64) with
            (2 ^ Z.of_nat 63 - 2 ^ 64) in Hge63 by ring.
          exact Hge63.
        - pose proof (spec_to_Z x) as Hx_bound.
          unfold base in Hx_bound. rewrite width_is_64 in Hx_bound.
          simpl in Hx_bound.
          nia. }
      change (Z.pow_pos 2 63) with (2 ^ Z.of_nat 63).
      change (Z.pow_pos 2 64) with (2 ^ 64).
      symmetry.
      apply Z.div_unique with (r := to_Z x - 2 ^ Z.of_nat 63).
      - lia.
      - lia. }
    rewrite Hdiv.
    symmetry.
    apply Z.mod_unique with (q := -1).
    + left.
      unfold base. rewrite width_is_64. simpl.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      pose proof (Z.pow_pos_nonneg 2 64 ltac:(lia)) as Hpow.
      nia.
    + unfold base. rewrite width_is_64. simpl.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      lia.
Qed.

Lemma signextend_signed_byte64_correct : forall shifted,
  to_Z (asr (shl shifted 56) 56) =
    let byte := to_Z shifted mod 256 in
    if byte <? 128 then byte else base width - 256 + byte.
Proof.
  intro shifted.
  pose proof (spec_to_Z shifted) as Hshifted.
  rewrite spec_asr.
  assert (Htop :
    to_Z (shl shifted 56) =
      (to_Z shifted mod 256) * 2 ^ 56).
  { rewrite spec_shl.
    rewrite Z.shiftl_mul_pow2 by lia.
    change (Z.pow_pos 2 56) with (2 ^ 56).
    set (q := to_Z shifted / 256).
    set (r := to_Z shifted mod 256).
    assert (Hdecomp : to_Z shifted = 256 * q + r).
    { unfold q, r. apply Z.div_mod. lia. }
    rewrite Hdecomp.
    unfold base. rewrite width_is_64. simpl.
    change (Z.pow_pos 2 64) with (2 ^ 64).
    change (2 ^ Z.of_nat 56) with (2 ^ 56).
    change (((256 * q + r) * 2 ^ 56) mod 2 ^ 64 = r * 2 ^ 56).
    rewrite Z.mul_add_distr_r.
    change 256 with (2 ^ 8).
    replace (2 ^ 8 * q * 2 ^ 56) with (q * 2 ^ 64) by ring.
    rewrite Zplus_mod.
    rewrite Z.mod_mul by lia.
    rewrite Z.add_0_l.
    rewrite Z.mod_mod by lia.
    apply Z.mod_small.
    unfold r.
    pose proof (Z.mod_pos_bound (to_Z shifted) 256 ltac:(lia)) as Hbyte.
    split.
    - apply Z.mul_nonneg_nonneg; lia.
    - assert (Hrlt : (to_Z shifted mod 256) * 2 ^ 56 < 256 * 2 ^ 56).
      { apply Z.mul_lt_mono_pos_r; lia. }
      replace (256 * 2 ^ 56) with (2 ^ 64) in Hrlt by reflexivity.
      lia.
  }
  rewrite Htop.
  set (byte := to_Z shifted mod 256).
  assert (Hbyte : 0 <= byte < 256).
  { subst byte. apply Z.mod_pos_bound. lia. }
  destruct (Z.ltb_spec0 byte 128) as [Hbyte_lt|Hbyte_ge].
  - replace
      (let byte0 := byte in if byte0 <? 128 then byte0 else base width - 256 + byte0)
      with byte.
    2:{ cbn.
        replace (byte <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
        reflexivity. }
    replace (byte * 2 ^ 56 <? base width / 2) with true.
    2:{ symmetry. apply (proj2 (Z.ltb_lt (byte * 2 ^ 56) (base width / 2))).
        unfold base. rewrite width_is_64. simpl.
        change (Z.pow_pos 2 64 / 2) with (2 ^ 63).
        assert (Hlt : byte * 2 ^ 56 < 128 * 2 ^ 56).
        { apply Z.mul_lt_mono_pos_r; lia. }
        replace (128 * 2 ^ 56) with (2 ^ 63) in Hlt by reflexivity.
        exact Hlt. }
    rewrite Z.shiftr_div_pow2 by lia.
    rewrite Z.sub_0_r.
    rewrite Z.mod_small.
      change (2 ^ Z.of_nat 56) with (2 ^ 56).
    + replace (byte * 2 ^ 56 / 2 ^ 56) with byte by
        (symmetry; apply Z.div_mul; lia).
      reflexivity.
    + split.
      * apply Z.div_pos; lia.
      * unfold base. rewrite width_is_64. simpl.
        change (Z.pow_pos 2 64 / 2) with (2 ^ 63).
        apply Z.div_lt_upper_bound; lia.
  - replace
      (let byte0 := byte in if byte0 <? 128 then byte0 else base width - 256 + byte0)
      with (base width - 256 + byte).
    2:{ cbn.
        replace (byte <? 128) with false by (symmetry; apply Z.ltb_ge; lia).
        reflexivity. }
    replace (byte * 2 ^ 56 <? base width / 2) with false.
    2:{ symmetry. apply (proj2 (Z.ltb_ge (byte * 2 ^ 56) (base width / 2))).
        unfold base. rewrite width_is_64. simpl.
        change (Z.pow_pos 2 64 / 2) with (2 ^ 63).
        assert (Hge : 128 * 2 ^ 56 <= byte * 2 ^ 56).
        { apply Z.mul_le_mono_nonneg_r; lia. }
        replace (128 * 2 ^ 56) with (2 ^ 63) in Hge by reflexivity.
        exact Hge. }
    rewrite Z.shiftr_div_pow2 by lia.
    assert (Hdiv : (byte * 2 ^ 56 - base width) / 2 ^ 56 = byte - 256).
    { unfold base. rewrite width_is_64. simpl.
      change (Z.pow_pos 2 64) with (2 ^ 64).
      change (Z.pow_pos 2 56) with (2 ^ 56).
      replace (2 ^ 64) with (256 * 2 ^ 56) by reflexivity.
      replace (byte * 2 ^ 56 - 256 * 2 ^ 56) with ((byte - 256) * 2 ^ 56) by ring.
      replace ((byte - 256) * 2 ^ 56 / 2 ^ 56) with (byte - 256) by
        (symmetry; apply Z.div_mul; lia).
      reflexivity.
    }
    change (2 ^ Z.of_nat 56) with (2 ^ 56).
    rewrite Hdiv.
    symmetry.
    apply Z.mod_unique with (q := -1); [|lia].
    unfold base; rewrite width_is_64.
    lia.
Qed.

Lemma to_Z_signextend_limit :
  to_Z_uint256
    (mk_uint256 (sub (shl one 5) one) zero zero zero) = 31.
Proof.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3 WL.to_Z_words].
  rewrite to_Z_low_mask by (rewrite width_is_64; simpl; lia).
  rewrite !spec_zero.
  lia.
Qed.

Lemma Z_land_low_high_local : forall lo hi k,
  0 <= k ->
  0 <= lo < 2 ^ k ->
  0 <= hi ->
  hi mod 2 ^ k = 0 ->
  Z.land lo hi = 0.
Proof.
  intros lo hi k Hk Hlo Hhi Hmod.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases n k) as [Hlt|Hge].
  - rewrite Bool.andb_false_iff. right.
    assert (Hhi_eq : hi = Z.shiftl (hi / 2 ^ k) k).
    { rewrite Z.shiftl_mul_pow2 by lia.
      pose proof (Z_div_mod_eq_full hi (2 ^ k)).
      lia. }
    rewrite Hhi_eq.
    apply Z.shiftl_spec_low.
    lia.
  - rewrite Bool.andb_false_iff. left.
    destruct (Z.eq_dec lo 0) as [->|Hnz].
    + rewrite Z.bits_0. reflexivity.
    + apply Z.bits_above_log2; [lia|].
      pose proof
        (proj1 (Z.log2_lt_pow2 lo k ltac:(lia)) ltac:(lia)) as Hlog.
      lia.
Qed.

Lemma Z_lor_add_disjoint_local : forall lo hi k,
  0 <= k ->
  0 <= lo < 2 ^ k ->
  0 <= hi ->
  hi mod 2 ^ k = 0 ->
  Z.lor hi lo = hi + lo.
Proof.
  intros lo hi k Hk Hlo Hhi Hmod.
  pose proof (Z_land_low_high_local lo hi k Hk Hlo Hhi Hmod) as Hland.
  rewrite Z.lor_comm.
  pose proof (Z.add_lor_land lo hi) as Hlor.
  lia.
Qed.

Lemma mod_split_small_prefix : forall prefix hi m n,
  0 <= m ->
  0 <= n ->
  0 <= prefix < 2 ^ m ->
  (prefix + 2 ^ m * hi) mod 2 ^ (m + n) =
    prefix + 2 ^ m * (hi mod 2 ^ n).
Proof.
  intros prefix hi m n Hm Hn Hprefix.
  set (q := hi / 2 ^ n).
  set (r := hi mod 2 ^ n).
  assert (Hr : 0 <= r < 2 ^ n).
  { unfold r.
    pose proof
      (Z.mod_pos_bound hi (2 ^ n) ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
    exact Hmod. }
  rewrite Z.pow_add_r by lia.
  symmetry.
  apply Z.mod_unique with (q := q).
  - left. split; nia.
  - unfold q, r.
    pose proof (Z.div_mod hi (2 ^ n) ltac:(apply Z.pow_nonzero; lia)) as Hdiv.
    nia.
Qed.

Lemma ltb_shifted_prefix : forall prefix hi m n,
  0 <= m ->
  0 <= n ->
  0 <= prefix < 2 ^ m ->
  0 <= hi ->
  ((prefix + 2 ^ m * hi) <? 2 ^ (m + n)) = (hi <? 2 ^ n).
Proof.
  intros prefix hi m n Hm Hn Hprefix Hhi.
  destruct (hi <? 2 ^ n) eqn:Hcmp.
  - apply Z.ltb_lt in Hcmp.
    apply Z.ltb_lt.
    rewrite Z.pow_add_r by lia.
    assert (Hprefix_le : prefix <= 2 ^ m - 1) by lia.
    assert (Hhi_le : hi <= 2 ^ n - 1) by lia.
    assert (Hmul_le : 2 ^ m * hi <= 2 ^ m * (2 ^ n - 1)).
    { apply Z.mul_le_mono_nonneg_l.
      - apply Z.pow_nonneg. lia.
      - exact Hhi_le. }
    replace (2 ^ m * 2 ^ n) with (2 ^ m + 2 ^ m * (2 ^ n - 1)) by ring.
    lia.
  - apply Z.ltb_ge in Hcmp.
    apply Z.ltb_ge.
    rewrite Z.pow_add_r by lia.
    assert (Hmul_ge : 2 ^ m * 2 ^ n <= 2 ^ m * hi).
    { apply Z.mul_le_mono_nonneg_l.
      - apply Z.pow_nonneg. lia.
      - exact Hcmp. }
    lia.
Qed.

Lemma pow_mul_sub_pow : forall a b c,
  0 <= a ->
  0 <= b ->
  0 <= c ->
  2 ^ a * (2 ^ b - 2 ^ c) = 2 ^ (a + b) - 2 ^ (a + c).
Proof.
  intros a b c Ha Hb Hc.
  rewrite !Z.pow_add_r by lia.
  ring.
Qed.

Lemma pow_mul_sub_one : forall a b,
  0 <= a ->
  0 <= b ->
  2 ^ a * (2 ^ b - 1) = 2 ^ (a + b) - 2 ^ a.
Proof.
  intros a b Ha Hb.
  rewrite Z.pow_add_r by lia.
  ring.
Qed.

Lemma pow256_from_words :
  2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 1))) = 2 ^ 256.
Proof.
  change (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 1))))
    with (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))).
  rewrite <- Z.pow_add_r by lia.
  rewrite <- Z.pow_add_r by lia.
  rewrite <- Z.pow_add_r by lia.
  replace (64 + (64 + (64 + 64))) with 256 by lia.
  reflexivity.
Qed.

Lemma signextend_negative_word2 : forall prefix byte m,
  0 <= m ->
  prefix +
  2 ^ 128 * (byte + (2 ^ 64 - 2 ^ (m + 8)) + 2 ^ 64 * (2 ^ 64 - 1)) =
  prefix + 2 ^ 128 * byte + (2 ^ 256 - 2 ^ (m + 136)).
Proof.
  intros prefix byte m Hm.
  replace
    (2 ^ 128 * (byte + (2 ^ 64 - 2 ^ (m + 8)) + 2 ^ 64 * (2 ^ 64 - 1)))
    with
    (2 ^ 128 * byte + 2 ^ 128 * (2 ^ 64 - 2 ^ (m + 8)) +
     2 ^ 192 * (2 ^ 64 - 1)) by ring.
  rewrite (pow_mul_sub_pow 128 64 (m + 8)) by lia.
  rewrite (pow_mul_sub_one 192 64) by lia.
  replace (128 + (m + 8)) with (m + 136) by lia.
  replace (128 + 64) with 192 by lia.
  replace (192 + 64) with 256 by lia.
  lia.
Qed.

Lemma signextend_negative_word3 : forall prefix byte m,
  0 <= m ->
  prefix + 2 ^ 192 * (byte + (2 ^ 64 - 2 ^ (m + 8))) =
  prefix + 2 ^ 192 * byte + (2 ^ 256 - 2 ^ (m + 200)).
Proof.
  intros prefix byte m Hm.
  replace (2 ^ 192 * (byte + (2 ^ 64 - 2 ^ (m + 8))))
    with
    (2 ^ 192 * byte + 2 ^ 192 * (2 ^ 64 - 2 ^ (m + 8))) by ring.
  rewrite (pow_mul_sub_pow 192 64 (m + 8)) by lia.
  replace (192 + (m + 8)) with (m + 200) by lia.
  replace (192 + 64) with 256 by lia.
  lia.
Qed.

Lemma signextend_word_low_decompose : forall word s,
  to_Z word mod 2 ^ (Z.of_nat s + 8) =
    to_Z word mod 2 ^ Z.of_nat s +
    (to_Z (shr word s) mod 256) * 2 ^ Z.of_nat s.
Proof.
  intros word s.
  rewrite to_Z_shr.
  pose proof
    (Z.div_mod (to_Z word) (2 ^ Z.of_nat s)
       ltac:(apply Z.pow_nonzero; lia)) as Hdiv.
  replace (to_Z word) with
    (to_Z word mod 2 ^ Z.of_nat s +
     2 ^ Z.of_nat s * (to_Z word / 2 ^ Z.of_nat s)) at 1 by nia.
  replace
    ((to_Z word / 2 ^ Z.of_nat s) mod 256 * 2 ^ Z.of_nat s)
    with
    (2 ^ Z.of_nat s * ((to_Z word / 2 ^ Z.of_nat s) mod 256))
    by ring.
  apply mod_split_small_prefix; try lia.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma signextend_upper_negative_rhs : forall byte m,
  2 ^ 64 * (2 ^ m - 1) + (byte * 2 ^ m + (2 ^ 64 - 256 * 2 ^ m)) =
    2 ^ 64 * 2 ^ m + (- (256 * 2 ^ m) + byte * 2 ^ m).
Proof.
  intros byte m.
  rewrite Z.mul_sub_distr_l.
  rewrite Z.mul_1_r.
  rewrite (Z.add_comm (byte * 2 ^ m) (2 ^ 64 - 256 * 2 ^ m)).
  change (2 ^ 64 - 256 * 2 ^ m) with (2 ^ 64 + - (256 * 2 ^ m)).
  rewrite <- Z.add_assoc.
  rewrite Z.add_assoc.
  rewrite Z.sub_add.
  reflexivity.
Qed.

Lemma signextend_upper_negative_lhs : forall byte m,
  (2 ^ 64 - 256 + byte) * 2 ^ m =
    2 ^ 64 * 2 ^ m + (- (256 * 2 ^ m) + byte * 2 ^ m).
Proof.
  intros byte m.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_sub_distr_r.
  rewrite Z.add_assoc.
  reflexivity.
Qed.

Lemma signextend_current_word_correct : forall word s,
  (s <= 56)%nat ->
  let '(current, sign_bits) := signextend_current_word word s in
  (to_Z current =
     let low := to_Z word mod 2 ^ (Z.of_nat s + 8) in
     if low <? 2 ^ (Z.of_nat s + 7)
     then low
     else low + (base width - 2 ^ (Z.of_nat s + 8))) /\
  (to_Z sign_bits =
     let low := to_Z word mod 2 ^ (Z.of_nat s + 8) in
     if low <? 2 ^ (Z.of_nat s + 7)
     then 0
     else base width - 1).
Proof.
  intros word s Hs.
  unfold signextend_current_word.
  cbn zeta.
  set (m := Z.of_nat s).
  set (byte := to_Z (shr word s) mod 256).
  set (low0 := to_Z word mod 2 ^ m).
  set (low := to_Z word mod 2 ^ (m + 8)).
  assert (Hslt : (s < word_width)%nat).
  { unfold word_width. rewrite width_is_64.
    change (Pos.to_nat 64) with 64%nat. lia. }
  assert (Hm : 0 <= m).
  { subst m. lia. }
  assert (Hm_le56 : m <= 56).
  { subst m. change 56 with (Z.of_nat 56).
    apply Nat2Z.inj_le. exact Hs. }
  assert (Hbase64 : base width = 2 ^ 64).
  { unfold base. rewrite width_is_64. reflexivity. }
  assert (Hhalf64 : base width / 2 = 2 ^ 63).
  { rewrite Hbase64.
    change (2 ^ 64) with (2 ^ 63 * 2).
    rewrite Z.div_mul by discriminate.
    reflexivity. }
  assert (Hlow0 : 0 <= low0 < 2 ^ m).
  { subst low0. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  assert (Hbyte : 0 <= byte < 256).
  { subst byte. apply Z.mod_pos_bound. lia. }
  assert (Hlow_range : 0 <= low < 2 ^ (m + 8)).
  { subst low. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia. }
  assert (Hpow7 : 2 ^ (m + 7) = 128 * 2 ^ m).
  { rewrite Z.pow_add_r by lia. change (2 ^ 7) with 128. ring. }
  assert (Hpow8 : 2 ^ (m + 8) = 256 * 2 ^ m).
  { rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. ring. }
  assert (Hlow :
    low = low0 + byte * 2 ^ m).
  { subst low low0 byte m.
    rewrite signextend_word_low_decompose.
    lia. }
  assert (Hcmp : (byte <? 128) = (low <? 2 ^ (m + 7))).
  { destruct (Z.ltb_spec0 byte 128) as [Hlt|Hge].
    - replace (byte <? 128) with true by (symmetry; apply Z.ltb_lt; lia).
      symmetry. apply Z.ltb_lt. rewrite Hlow, Hpow7. nia.
    - replace (byte <? 128) with false by (symmetry; apply Z.ltb_ge; lia).
      symmetry. apply Z.ltb_ge. rewrite Hlow, Hpow7. nia. }
  assert (Hsigned :
    to_Z (asr (shl (shr word s) 56) 56) =
      if byte <? 128 then byte else base width - 256 + byte).
  { subst byte. apply signextend_signed_byte64_correct. }
  assert (Hupper :
    to_Z (shl (asr (shl (shr word s) 56) 56) s) =
      if byte <? 128
      then byte * 2 ^ m
      else byte * 2 ^ m + (base width - 2 ^ (m + 8))).
  { rewrite spec_shl, Hsigned.
    rewrite Z.shiftl_mul_pow2 by exact Hm.
    destruct (byte <? 128) eqn:Hbyte_lt.
    - apply Z.ltb_lt in Hbyte_lt.
      rewrite Z.mod_small.
      + reflexivity.
      + split.
        * assert (Hpow_nonneg : 0 <= 2 ^ m).
          { apply Z.pow_nonneg. now compute. }
          apply Z.mul_nonneg_nonneg.
          -- exact (proj1 Hbyte).
          -- exact Hpow_nonneg.
        * rewrite Hbase64.
          assert (Hm7_le63 : m + 7 <= 63).
          { apply Z.add_le_mono_r with (p := 7) in Hm_le56.
            change (56 + 7) with 63 in Hm_le56.
            exact Hm_le56. }
          assert (Hm7_le64 : m + 7 <= 64).
          { eapply Z.le_trans.
            - exact Hm7_le63.
            - now compute. }
          assert (Hpow_pos : 0 < 2 ^ m).
          { apply Z.pow_pos_nonneg.
            - now compute.
            - exact Hm. }
          assert (Hlt : byte * 2 ^ m < 2 ^ (m + 7)).
          { rewrite Hpow7.
            apply Z.mul_lt_mono_pos_r.
            - exact Hpow_pos.
            - exact Hbyte_lt. }
          assert (Hpow_le : 2 ^ (m + 7) <= 2 ^ 64).
          { apply Z.pow_le_mono_r.
            - now compute.
            - exact Hm7_le64. }
          exact (Z.lt_le_trans _ _ _ Hlt Hpow_le).
    - apply Z.ltb_ge in Hbyte_lt.
      symmetry.
      apply Z.mod_unique with (q := 2 ^ m - 1).
      + left. split.
        * rewrite Hbase64.
          rewrite Hpow8.
          assert (Hm8_le64 : m + 8 <= 64).
          { apply Z.add_le_mono_r with (p := 8) in Hm_le56.
            change (56 + 8) with 64 in Hm_le56.
            exact Hm_le56. }
          assert (Hpow_le : 256 * 2 ^ m <= 2 ^ 64).
          { rewrite <- Hpow8.
            apply Z.pow_le_mono_r.
            - now compute.
            - exact Hm8_le64. }
          assert (Hpow_nonneg : 0 <= 2 ^ m).
          { apply Z.pow_nonneg. now compute. }
          assert (Hbyte_nonneg : 0 <= byte * 2 ^ m).
          { apply Z.mul_nonneg_nonneg.
            - exact (proj1 Hbyte).
            - exact Hpow_nonneg. }
          assert (Htail_nonneg : 0 <= 2 ^ 64 - 256 * 2 ^ m).
          { apply Z.sub_nonneg. exact Hpow_le. }
          apply Z.add_nonneg_nonneg.
          -- exact Hbyte_nonneg.
          -- exact Htail_nonneg.
        * rewrite Hbase64.
          rewrite Hpow8.
          assert (Hpow_pos : 0 < 2 ^ m).
          { apply Z.pow_pos_nonneg.
            - now compute.
            - exact Hm. }
          assert (Hbyte_lt_mul : byte * 2 ^ m < 256 * 2 ^ m).
          { apply Z.mul_lt_mono_pos_r.
            - exact Hpow_pos.
            - exact (proj2 Hbyte). }
          apply Z.add_lt_mono_r with (p := 2 ^ 64 - 256 * 2 ^ m) in Hbyte_lt_mul.
          replace (256 * 2 ^ m + (2 ^ 64 - 256 * 2 ^ m)) with (2 ^ 64)
            in Hbyte_lt_mul.
          2:{ rewrite Z.add_comm.
              rewrite Z.sub_add.
              reflexivity. }
          exact Hbyte_lt_mul.
      + rewrite Hbase64.
        rewrite Hpow8.
        rewrite signextend_upper_negative_lhs.
        rewrite signextend_upper_negative_rhs.
        reflexivity. }
  assert (Hsign_bits :
    to_Z (asr (asr (shl (shr word s) 56) 56) 63) =
      if byte <? 128 then 0 else base width - 1).
  { rewrite to_Z_asr_63, Hsigned.
    destruct (byte <? 128) eqn:Hbyte_lt.
    - replace
        (byte <? base width / 2)
        with true.
      2:{ assert (Hbyte_lt_num : byte < 128).
          { apply Z.ltb_lt. exact Hbyte_lt. }
          symmetry. apply Z.ltb_lt.
          rewrite Hhalf64.
          change 128 with (2 ^ 7) in Hbyte_lt_num.
          eapply Z.lt_le_trans.
          - exact Hbyte_lt_num.
          - apply Z.pow_le_mono_r.
            + now compute.
            + now compute. }
      reflexivity.
    - replace
        (base width - 256 + byte <? base width / 2)
        with false.
      2:{ assert (Hbyte_ge_num : 128 <= byte).
          { apply Z.ltb_ge. exact Hbyte_lt. }
          symmetry. apply Z.ltb_ge.
          rewrite Hhalf64.
          nia. }
      reflexivity. }
  split.
  - rewrite spec_or, Hupper, to_Z_land_low_mask by exact Hslt.
    change (to_Z word mod 2 ^ Z.of_nat s) with low0.
    destruct (byte <? 128) eqn:Hbyte_lt.
    + rewrite (Z_lor_add_disjoint_local low0 (byte * 2 ^ m) m);
        try exact Hm; try exact Hlow0; try nia.
      2:{ rewrite Z.mod_mul by (apply Z.pow_nonzero; lia). reflexivity. }
      rewrite Z.mod_small.
      * cbn zeta.
        rewrite <- Hcmp, Hlow.
        rewrite Z.add_comm.
        reflexivity.
      * split.
        -- assert (Hpow_nonneg : 0 <= 2 ^ m).
           { apply Z.pow_nonneg. now compute. }
           apply Z.add_nonneg_nonneg.
           ++ apply Z.mul_nonneg_nonneg.
              ** exact (proj1 Hbyte).
              ** exact Hpow_nonneg.
           ++ exact (proj1 Hlow0).
        -- rewrite Z.add_comm.
           rewrite <- Hlow.
           assert (Hlow_lt : low < 2 ^ (m + 7)).
           { apply Z.ltb_lt. symmetry. exact Hcmp. }
           assert (Hm7_le64 : m + 7 <= 64).
           { apply Z.add_le_mono_r with (p := 7) in Hm_le56.
             change (56 + 7) with 63 in Hm_le56.
             eapply Z.le_trans.
             - exact Hm_le56.
             - now compute. }
           rewrite Hbase64.
           eapply Z.lt_le_trans.
           ++ exact Hlow_lt.
           ++ apply Z.pow_le_mono_r.
              ** now compute.
              ** exact Hm7_le64.
    + assert (Hm8_le64 : m + 8 <= 64).
      { apply Z.add_le_mono_r with (p := 8) in Hm_le56.
        change (56 + 8) with 64 in Hm_le56.
        exact Hm_le56. }
      assert (Hpow_le : 2 ^ (m + 8) <= 2 ^ 64).
      { apply Z.pow_le_mono_r.
        - now compute.
        - exact Hm8_le64. }
      assert (Hpow_nonneg : 0 <= 2 ^ m).
      { apply Z.pow_nonneg. now compute. }
      assert (Hupper_nonneg : 0 <= byte * 2 ^ m + (base width - 2 ^ (m + 8))).
      { rewrite Hbase64.
        assert (Hbyte_nonneg : 0 <= byte * 2 ^ m).
        { apply Z.mul_nonneg_nonneg.
          - exact (proj1 Hbyte).
          - exact Hpow_nonneg. }
        assert (Htail_nonneg : 0 <= 2 ^ 64 - 2 ^ (m + 8)).
        { apply Z.sub_nonneg. exact Hpow_le. }
        apply Z.add_nonneg_nonneg.
        - exact Hbyte_nonneg.
        - exact Htail_nonneg. }
      assert (Hupper_mod :
        (byte * 2 ^ m + (base width - 2 ^ (m + 8))) mod 2 ^ m = 0).
      { rewrite Zplus_mod.
        rewrite Z.mod_mul by (apply Z.pow_nonzero; lia).
        rewrite Hbase64.
        replace (2 ^ 64) with (2 ^ m * 2 ^ (64 - m)).
        2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
        rewrite Hpow8.
        rewrite Z.mul_comm with (n := 256) (m := 2 ^ m).
        rewrite <- Z.mul_sub_distr_l.
        rewrite Z.add_0_l.
        rewrite Z.mul_comm.
        rewrite Z.mod_mul by (apply Z.pow_nonzero; lia).
        rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
        reflexivity. }
      rewrite
        (Z_lor_add_disjoint_local low0
           (byte * 2 ^ m + (base width - 2 ^ (m + 8))) m);
        try exact Hm; try exact Hlow0; try exact Hupper_nonneg;
        try exact Hupper_mod.
      rewrite Z.mod_small.
      * cbn zeta.
        rewrite <- Hcmp, Hlow.
        rewrite <- Z.add_assoc.
        rewrite (Z.add_comm (base width - 2 ^ (m + 8)) low0).
        rewrite Z.add_assoc.
        rewrite (Z.add_comm (byte * 2 ^ m) low0).
        rewrite <- Z.add_assoc.
        reflexivity.
      * split.
        -- apply Z.add_nonneg_nonneg;
             [exact Hupper_nonneg | exact (proj1 Hlow0)].
        -- rewrite Hbase64.
           rewrite Hpow8.
           rewrite Hlow in Hlow_range.
           rewrite Hpow8 in Hlow_range.
           rewrite <- Z.add_assoc.
           rewrite (Z.add_comm (2 ^ 64 - 256 * 2 ^ m) low0).
           rewrite Z.add_assoc.
           rewrite (Z.add_comm (byte * 2 ^ m) low0).
           eapply Z.lt_le_trans;
             [apply Z.add_lt_mono_r; exact (proj2 Hlow_range) |].
           rewrite (Z.add_comm (256 * 2 ^ m) (2 ^ 64 - 256 * 2 ^ m)).
           rewrite Z.sub_add.
           apply Z.le_refl.
  - cbn zeta.
    rewrite Hsign_bits, <- Hcmp.
    reflexivity.
Qed.

Lemma fill_words_from_length : forall ws start v,
  length (fill_words_from ws start v) = length ws.
Proof.
  induction ws as [|w rest IH]; intros start v.
  - reflexivity.
  - destruct start; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma fill_words_from_ge_length : forall ws start v,
  (length ws <= start)%nat ->
  fill_words_from ws start v = ws.
Proof.
  induction ws as [|w rest IH]; intros start v Hstart.
  - reflexivity.
  - destruct start as [|start'].
    + simpl in Hstart. lia.
    + simpl. f_equal. apply IH.
      now apply Nat.succ_le_mono in Hstart.
Qed.

Lemma get_fill_words_from_before : forall ws start v i,
  (i < start)%nat ->
  get_word (fill_words_from ws start v) i = get_word ws i.
Proof.
  induction ws as [|w rest IH]; intros start v i Hi.
  - reflexivity.
  - destruct start as [|start'].
    + exfalso. lia.
    + destruct i as [|i'].
      * reflexivity.
      * simpl. apply IH.
        now apply Nat.succ_lt_mono in Hi.
Qed.

Lemma get_fill_words_from_after : forall ws start v i,
  (start <= i < length ws)%nat ->
  get_word (fill_words_from ws start v) i = v.
Proof.
  induction ws as [|w rest IH]; intros start v i Hi.
  - exfalso. destruct Hi as [_ Hi]. simpl in Hi. lia.
  - destruct start as [|start'].
    + destruct i as [|i'].
      * reflexivity.
      * simpl. apply IH.
        destruct Hi as [_ Hi].
        split.
        -- lia.
        -- now apply Nat.succ_lt_mono in Hi.
    + destruct i as [|i'].
      * exfalso. lia.
      * simpl. apply IH.
        destruct Hi as [Hstart Hi].
        split.
        -- now apply Nat.succ_le_mono in Hstart.
        -- now apply Nat.succ_lt_mono in Hi.
Qed.

Lemma signextend_word_index_nat_correct : forall word_index,
  0 <= to_Z word_index < 4 ->
  signextend_word_index_nat word_index = Z.to_nat (to_Z word_index).
Proof.
  intros word_index [Hword_ge Hword_lt].
  assert (Htwo : to_Z (add one one) = 2).
  { rewrite !spec_add, !spec_one.
    rewrite Z.mod_small.
    - reflexivity.
    - unfold base. rewrite width_is_64. lia. }
  unfold signextend_word_index_nat.
  destruct (Z.eq_dec (to_Z word_index) 0) as [H0|H0].
  - rewrite spec_eqb, spec_zero, H0. reflexivity.
  - rewrite spec_eqb, spec_zero.
    replace (to_Z word_index =? 0) with false.
    2:{ symmetry. apply Z.eqb_neq. exact H0. }
    destruct (Z.eq_dec (to_Z word_index) 1) as [H1|H1].
    + rewrite spec_eqb, spec_one, H1. reflexivity.
    + rewrite spec_eqb, spec_one.
      replace (to_Z word_index =? 1) with false.
      2:{ symmetry. apply Z.eqb_neq. exact H1. }
      destruct (Z.eq_dec (to_Z word_index) 2) as [H2|H2].
      * rewrite spec_eqb, Htwo, H2. reflexivity.
      * rewrite spec_eqb, Htwo.
        replace (to_Z word_index =? 2) with false.
        2:{ symmetry. apply Z.eqb_neq. exact H2. }
        assert (H3 : to_Z word_index = 3) by lia.
        rewrite H3. reflexivity.
Qed.

Lemma signextend_writeback_word0 :
  forall x0 x1 x2 x3 current sign_bits,
    words_to_uint256
      (fill_words_from (set_word [x0; x1; x2; x3] 0 current) 1 sign_bits) =
    mk_uint256 current sign_bits sign_bits sign_bits.
Proof.
  intros. reflexivity.
Qed.

Lemma signextend_writeback_word1 :
  forall x0 x1 x2 x3 current sign_bits,
    words_to_uint256
      (fill_words_from (set_word [x0; x1; x2; x3] 1 current) 2 sign_bits) =
    mk_uint256 x0 current sign_bits sign_bits.
Proof.
  intros. reflexivity.
Qed.

Lemma signextend_writeback_word2 :
  forall x0 x1 x2 x3 current sign_bits,
    words_to_uint256
      (fill_words_from (set_word [x0; x1; x2; x3] 2 current) 3 sign_bits) =
    mk_uint256 x0 x1 current sign_bits.
Proof.
  intros. reflexivity.
Qed.

Lemma signextend_writeback_word3 :
  forall x0 x1 x2 x3 current sign_bits,
    words_to_uint256
      (fill_words_from (set_word [x0; x1; x2; x3] 3 current) 4 sign_bits) =
    mk_uint256 x0 x1 x2 current.
Proof.
  intros. reflexivity.
Qed.

Theorem signextend_correct : forall byte_index_256 x,
  to_Z_uint256 (signextend byte_index_256 x) =
    signextend_Z (to_Z_uint256 byte_index_256) (to_Z_uint256 x).
Proof.
  intros [b0 b1 b2 b3] [x0 x1 x2 x3].
  set (idx := mk_uint256 b0 b1 b2 b3).
  remember
    (ltb_uint256 idx (mk_uint256 (sub (shl one 5) one) zero zero zero))
    as in_range eqn:Hidx.
  destruct in_range.
  2:{ symmetry in Hidx.
      pose proof Hidx as Hltb.
      rewrite ltb_uint256_correct in Hltb.
      rewrite to_Z_signextend_limit in Hltb.
      apply Z.ltb_ge in Hltb.
      unfold signextend, signextend_Z.
      rewrite Hidx.
      replace (to_Z_uint256 idx <? 31) with false.
      2:{ symmetry. apply Z.ltb_ge. exact Hltb. }
      reflexivity. }
  symmetry in Hidx.
  pose proof Hidx as Hltb.
  rewrite ltb_uint256_correct in Hltb.
  rewrite to_Z_signextend_limit in Hltb.
  apply Z.ltb_lt in Hltb.
  assert (Hlt_base : to_Z_uint256 idx < base width)
    by (unfold base; rewrite width_is_64; lia).
  destruct (to_Z_uint256_lt_base_zero_high b0 b1 b2 b3 Hlt_base)
    as [Hb1z [Hb2z Hb3z]].
  assert (Hb : to_Z_uint256 idx = to_Z b0).
  { unfold idx, to_Z_uint256, uint256_to_words.
    cbn [w0 w1 w2 w3 to_Z_words].
    rewrite Hb1z, Hb2z, Hb3z.
    rewrite ?Z.mul_0_r, ?Z.add_0_r.
    reflexivity. }
  assert (Hword_index : to_Z (shr b0 3) = to_Z b0 / 8)
    by now rewrite to_Z_shr.
  assert (Hword_range : 0 <= to_Z (shr b0 3) < 4).
  { pose proof (spec_to_Z b0) as Hb0_range.
    rewrite Hword_index.
    split.
    - now apply Z.div_pos.
    - apply Z.div_lt_upper_bound; lia. }
  assert (Hword_index_n :
    signextend_word_index_nat (shr b0 3) = Z.to_nat (to_Z (shr b0 3)))
   by (now apply signextend_word_index_nat_correct).
  unfold signextend.
  subst idx.
  rewrite Hidx.
  cbn [negb w0 w1 w2 w3].
  rewrite Hword_index_n, Hb.
  unfold signextend_Z.
  replace (2 ^ 256) with modulus256.
  2:{ unfold modulus256, modulus_words, WL.modulus_words, base.
      rewrite width_is_64.
      change (Z.pow_pos (2 ^ 64) 4) with ((2 ^ 64) ^ 4).
      rewrite <- Z.pow_mul_r by lia.
      replace (64 * 4) with 256 by lia.
      reflexivity. }
  replace (to_Z b0 <? 31) with true
    by (symmetry; apply Z.ltb_lt; lia).
  set (n := Z.to_nat (to_Z (shr b0 3))).
  set (s := bounded_shift_nat word_width
                              (shl (land b0 (shl 1 3 - 1)%Uint) 3)).
  assert (Hmask3 :
    to_Z (land b0 (shl 1 3 - 1)%Uint) = to_Z b0 mod 8).
  { change ((shl 1 3 - 1)%Uint) with (sub (shl one 3) one).
    assert (H3lt : (3 < Pos.to_nat U64.width)%nat).
    { rewrite width_is_64. compute. repeat constructor. }
    pose proof (to_Z_land_low_mask b0 3) as Hmask3'.
    specialize (Hmask3' H3lt).
    rewrite Hmask3'.
    change (2 ^ Z.of_nat 3) with 8.
    reflexivity. }
  assert (Hshift_bits :
    to_Z (shl (land b0 (shl 1 3 - 1)%Uint) 3) = 8 * (to_Z b0 mod 8)).
  { rewrite spec_shl, Hmask3.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small.
    2:{ split.
        - pose proof (Z.mod_pos_bound (to_Z b0) 8 ltac:(lia)) as Hmod8.
          nia.
        - unfold base. rewrite width_is_64. simpl.
          pose proof (Z.mod_pos_bound (to_Z b0) 8 ltac:(lia)) as Hmod8.
          nia. }
    change (2 ^ Z.of_nat 3) with 8.
    ring. }
  assert (Hs_eq : Z.of_nat s = 8 * (to_Z b0 mod 8)).
  { subst s.
    rewrite (bounded_shift_nat_correct word_width
               (shl (land b0 (shl 1 3 - 1)%Uint) 3)).
    2:{ apply Nat.le_refl. }
    2:{ rewrite Hshift_bits.
        unfold word_width.
        rewrite width_is_64.
        change (Z.of_nat 64) with 64.
        pose proof (Z.mod_pos_bound (to_Z b0) 8 ltac:(lia)) as Hmod8.
        nia. }
    assert (Hshift_nonneg : 0 <= to_Z (shl (land b0 (shl 1 3 - 1)%Uint) 3)).
    { rewrite Hshift_bits.
      pose proof (Z.mod_pos_bound (to_Z b0) 8 ltac:(lia)) as Hmod8.
      nia. }
    rewrite Z2Nat.id by exact Hshift_nonneg.
    exact Hshift_bits. }
  assert (Hs_le56 : (s <= 56)%nat).
  { apply Nat2Z.inj_le.
    change (Z.of_nat 56) with 56.
    rewrite Hs_eq.
    pose proof (Z.mod_pos_bound (to_Z b0) 8 ltac:(lia)) as Hmod8.
    nia. }
  assert (Hnlt : (n < 4)%nat).
  { subst n.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    lia. }
  set (word := get_word (uint256_to_words {| w0 := x0; w1 := x1; w2 := x2; w3 := x3 |}) n).
  destruct n as [|[|[|[|n']]]] eqn:Hn; try lia; cbn [get_word set_word uint256_to_words] in *;
    destruct (signextend_current_word_correct word s Hs_le56) as [Hcur Hsign].
  - unfold word in *.
    cbn [get_word uint256_to_words nth w0 w1 w2 w3] in Hcur, Hsign |- *.
    assert (Hb0_mod : to_Z b0 mod 8 = to_Z b0).
    { apply Z.mod_small.
      pose proof (Z.div_mod (to_Z b0) 8 ltac:(lia)) as Hdm.
      pose proof (spec_to_Z b0) as Hb0.
      lia. }
    assert (Hbits0 : 8 * (to_Z b0 + 1) = Z.of_nat s + 8)
      by (rewrite Hs_eq, Hb0_mod; ring).
    rewrite Hbits0.
    replace (Z.of_nat s + 8 - 1) with (Z.of_nat s + 7) by lia.
    destruct (signextend_current_word x0 s) as [current sign_bits] eqn:Hcw.
    cbn [fill_words_from words_to_uint256 fit_words firstn app repeat
       to_Z_words uint256_to_words to_Z_uint256 w0 w1 w2 w3] in |- *.
    unfold signextend_current_word in Hcw.
    cbn zeta in Hcw.
    inversion Hcw; subst current sign_bits; clear Hcw.
    assert (Hs_le64 : Z.of_nat s + 8 <= 64).
    { apply Nat2Z.inj_le in Hs_le56. lia. }
    set (hi := WL.U64.to_Z x1 +
               base WL.U64.width *
                 (WL.U64.to_Z x2 +
                  base WL.U64.width * (WL.U64.to_Z x3 + base WL.U64.width * 0))).
    assert (Hpow64 :
      base WL.U64.width = 2 ^ (Z.of_nat s + 8) * 2 ^ (64 - (Z.of_nat s + 8))).
    { unfold base.
      rewrite width_is_64.
      rewrite <- Z.pow_add_r by lia.
      replace (Z.of_nat s + 8 + (64 - (Z.of_nat s + 8))) with 64 by lia.
      reflexivity. }
    assert (Hmod_rhs :
      (WL.U64.to_Z x0 + base WL.U64.width * hi) mod 2 ^ (Z.of_nat s + 8) =
      WL.U64.to_Z x0 mod 2 ^ (Z.of_nat s + 8)).
    { rewrite Hpow64.
      rewrite <- Z.mul_assoc.
      rewrite Z.mul_comm.
      rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
      reflexivity. }
    rewrite Hmod_rhs.
    destruct (to_Z x0 mod 2 ^ (Z.of_nat s + 8) <? 2 ^ (Z.of_nat s + 7))
      eqn:Hcmp0.
    + rewrite Hcur, Hsign.
      rewrite ?Z.mul_0_r, ?Z.add_0_r.
      reflexivity.
    + rewrite Hcur, Hsign.
      rewrite Z.mul_0_r, Z.add_0_r.
      unfold modulus256.
      rewrite !WL.modulus_words_succ, ?WL.modulus_words_0.
      ring_simplify.
      lia.
  -
    unfold word in *.
    cbn [get_word uint256_to_words nth w0 w1 w2 w3] in Hcur, Hsign |- *.
    assert (Hb0_div1 : to_Z b0 / 8 = 1).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hb0_decomp : to_Z b0 = 8 + to_Z b0 mod 8).
    { pose proof (Z.div_mod (to_Z b0) 8 ltac:(lia)) as Hdm.
      rewrite Hb0_div1 in Hdm.
      lia. }
    assert (Hbits1 : 8 * (to_Z b0 + 1) = Z.of_nat s + 72).
    { rewrite Hs_eq, Hb0_decomp.
      replace (8 * (8 + to_Z b0 mod 8 + 1))
        with (72 + 8 * (to_Z b0 mod 8)) by ring.
      rewrite Z.add_mod by lia.
      change (8 mod 8) with 0.
      rewrite Z.add_0_l.
      rewrite Z.mod_mod by lia.
      rewrite Z.mod_mod by lia.
      lia. }
    rewrite Hbits1.
    replace (Z.of_nat s + 72 - 1) with (Z.of_nat s + 71) by lia.
    destruct (signextend_current_word x1 s) as [current sign_bits] eqn:Hcw.
    cbn [fill_words_from words_to_uint256 fit_words firstn app repeat
       to_Z_words uint256_to_words to_Z_uint256 w0 w1 w2 w3] in |- *.
    unfold signextend_current_word in Hcw.
    cbn zeta in Hcw.
    inversion Hcw; subst current sign_bits; clear Hcw.
    assert (Hs_le64 : Z.of_nat s + 8 <= 64).
    { apply Nat2Z.inj_le in Hs_le56. lia. }
    assert (Hbase64 : base WL.U64.width = 2 ^ 64).
    { unfold base. rewrite width_is_64. reflexivity. }
    set (tail := WL.U64.to_Z x2 +
                 base WL.U64.width *
                   (WL.U64.to_Z x3 + base WL.U64.width * 0)).
    set (hi := WL.U64.to_Z x1 + base WL.U64.width * tail).
    assert (Hmod_hi :
      hi mod 2 ^ (Z.of_nat s + 8) = WL.U64.to_Z x1 mod 2 ^ (Z.of_nat s + 8)).
    { unfold hi.
      rewrite Hbase64.
      assert (Hpow64 :
        2 ^ 64 = 2 ^ (Z.of_nat s + 8) * 2 ^ (56 - Z.of_nat s)).
      { rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat s + 8 + (56 - Z.of_nat s)) with 64 by lia.
        reflexivity. }
      rewrite Hpow64.
      replace
        (WL.U64.to_Z x1 + 2 ^ (Z.of_nat s + 8) * 2 ^ (56 - Z.of_nat s) * tail)
        with
        (WL.U64.to_Z x1 + (2 ^ (56 - Z.of_nat s) * tail) *
           2 ^ (Z.of_nat s + 8)) by ring.
      rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
      reflexivity. }
    assert (Hx0_range : 0 <= WL.U64.to_Z x0 < 2 ^ 64).
    { pose proof (spec_to_Z x0) as Hx0.
      rewrite Hbase64 in Hx0.
      exact Hx0. }
    assert (Hmod_rhs :
      (WL.U64.to_Z x0 + base WL.U64.width * hi) mod 2 ^ (Z.of_nat s + 72) =
      WL.U64.to_Z x0 +
      base WL.U64.width * (WL.U64.to_Z x1 mod 2 ^ (Z.of_nat s + 8))).
    { rewrite Hbase64.
      replace (Z.of_nat s + 72) with (64 + (Z.of_nat s + 8)) by lia.
      rewrite mod_split_small_prefix by (try lia; exact Hx0_range).
      rewrite Hmod_hi.
      reflexivity. }
    rewrite Hmod_rhs.
    assert (Hcmp_rhs :
      (WL.U64.to_Z x0 +
       base WL.U64.width *
         (WL.U64.to_Z x1 mod 2 ^ (Z.of_nat s + 8)) <? 2 ^ (Z.of_nat s + 71)) =
      (WL.U64.to_Z x1 mod 2 ^ (Z.of_nat s + 8) <? 2 ^ (Z.of_nat s + 7))).
    { rewrite Hbase64.
      replace (Z.of_nat s + 71) with (64 + (Z.of_nat s + 7)) by lia.
      apply ltb_shifted_prefix.
      - lia.
      - lia.
      - exact Hx0_range.
      - pose proof
          (Z.mod_pos_bound
             (WL.U64.to_Z x1) (2 ^ (Z.of_nat s + 8))
             ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
        lia. }
    rewrite Hcmp_rhs.
    destruct (WL.U64.to_Z x1 mod 2 ^ (Z.of_nat s + 8) <?
                2 ^ (Z.of_nat s + 7)) eqn:Hcmp.
    + rewrite Hcur, Hsign.
      rewrite ?Z.mul_0_r, ?Z.add_0_r.
      reflexivity.
    + rewrite Hcur, Hsign.
      rewrite Hbase64.
      replace
        (WL.U64.to_Z x0 +
         2 ^ 64 *
         (to_Z x1 mod 2 ^ (Z.of_nat s + 8) +
          (2 ^ 64 - 2 ^ (Z.of_nat s + 8)) +
          2 ^ 64 * (2 ^ 64 - 1 + 2 ^ 64 * (2 ^ 64 - 1 + 2 ^ 64 * 0))))
        with
        (WL.U64.to_Z x0 +
         2 ^ 64 * (to_Z x1 mod 2 ^ (Z.of_nat s + 8)) +
         2 ^ 64 * (2 ^ 64 - 2 ^ (Z.of_nat s + 8)) +
         2 ^ 128 * (2 ^ 64 - 1) +
         2 ^ 192 * (2 ^ 64 - 1)) by ring.
      unfold modulus256.
      rewrite !WL.modulus_words_succ, ?WL.modulus_words_0.
      rewrite Hbase64.
      rewrite (pow_mul_sub_pow 64 64 (Z.of_nat s + 8)) by lia.
      rewrite (pow_mul_sub_one 128 64) by lia.
      rewrite (pow_mul_sub_one 192 64) by lia.
      replace (64 + (Z.of_nat s + 8)) with (Z.of_nat s + 72) by lia.
      replace (64 + 64) with 128 by lia.
      replace (128 + 64) with 192 by lia.
      replace (192 + 64) with 256 by lia.
      change (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 1))))
        with (2 ^ 64 * (2 ^ 64 * (2 ^ 64 * 2 ^ 64))).
      rewrite <- Z.pow_add_r by lia.
      rewrite <- Z.pow_add_r by lia.
      rewrite <- Z.pow_add_r by lia.
      replace (64 + (64 + (64 + 64))) with 256 by lia.
      replace (192 + 64) with 256 by lia.
      lia.
  - unfold word in *.
    cbn [get_word uint256_to_words nth w0 w1 w2 w3] in Hcur, Hsign |- *.
    assert (Hb0_div2 : to_Z b0 / 8 = 2).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hb0_decomp : to_Z b0 = 16 + to_Z b0 mod 8).
    { pose proof (Z.div_mod (to_Z b0) 8 ltac:(lia)) as Hdm.
      rewrite Hb0_div2 in Hdm.
      lia. }
    assert (Hbits2 : 8 * (to_Z b0 + 1) = Z.of_nat s + 136).
    { rewrite Hs_eq, Hb0_decomp.
      replace (8 * (16 + to_Z b0 mod 8 + 1))
        with (136 + 8 * (to_Z b0 mod 8)) by ring.
      rewrite Z.add_mod by lia.
      change (136 mod 8) with 0.
      rewrite Z.add_0_l.
      rewrite Z.mod_mod by lia.
      rewrite Z.mod_mod by lia.
      lia. }
    rewrite Hbits2.
    replace (Z.of_nat s + 136 - 1) with (Z.of_nat s + 135) by lia.
    destruct (signextend_current_word x2 s) as [current sign_bits] eqn:Hcw.
    cbn [fill_words_from words_to_uint256 fit_words firstn app repeat
       to_Z_words uint256_to_words to_Z_uint256 w0 w1 w2 w3] in |- *.
    unfold signextend_current_word in Hcw.
    cbn zeta in Hcw.
    inversion Hcw; subst current sign_bits; clear Hcw.
    assert (Hs_le64 : Z.of_nat s + 8 <= 64).
    { apply Nat2Z.inj_le in Hs_le56. lia. }
    assert (Hbase64 : base WL.U64.width = 2 ^ 64).
    { unfold base. rewrite width_is_64. reflexivity. }
    set (prefix := WL.U64.to_Z x0 + base WL.U64.width * WL.U64.to_Z x1).
    assert (Hprefix_range : 0 <= prefix < 2 ^ 128).
    { unfold prefix.
      rewrite Hbase64.
      pose proof (spec_to_Z x0) as Hx0.
      pose proof (spec_to_Z x1) as Hx1.
      rewrite Hbase64 in Hx0, Hx1.
      split; lia. }
    set (hi := WL.U64.to_Z x2 + base WL.U64.width * WL.U64.to_Z x3).
    assert (Hmod_hi :
      hi mod 2 ^ (Z.of_nat s + 8) = WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8)).
    { unfold hi.
      rewrite Hbase64.
      assert (Hpow64 :
        2 ^ 64 = 2 ^ (Z.of_nat s + 8) * 2 ^ (56 - Z.of_nat s)).
      { rewrite <- Z.pow_add_r by lia.
        replace (Z.of_nat s + 8 + (56 - Z.of_nat s)) with 64 by lia.
        reflexivity. }
      rewrite Hpow64.
      replace
        (WL.U64.to_Z x2 + 2 ^ (Z.of_nat s + 8) * 2 ^ (56 - Z.of_nat s) *
           WL.U64.to_Z x3)
        with
        (WL.U64.to_Z x2 + (2 ^ (56 - Z.of_nat s) * WL.U64.to_Z x3) *
           2 ^ (Z.of_nat s + 8)) by ring.
      rewrite Z.mod_add by (apply Z.pow_nonzero; lia).
      reflexivity. }
    assert (Hmod_rhs :
      (prefix + 2 ^ 128 * hi) mod 2 ^ (Z.of_nat s + 136) =
      prefix + 2 ^ 128 * (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8))).
    { replace (Z.of_nat s + 136) with (128 + (Z.of_nat s + 8)) by lia.
      rewrite mod_split_small_prefix by (try lia; exact Hprefix_range).
      rewrite Hmod_hi.
      reflexivity. }
    rewrite Hbase64.
    assert (Hfull :
      WL.U64.to_Z x0 +
      2 ^ 64 *
      (WL.U64.to_Z x1 +
       2 ^ 64 *
       (WL.U64.to_Z x2 + 2 ^ 64 * (WL.U64.to_Z x3 + 2 ^ 64 * 0))) =
      prefix + 2 ^ 128 * hi).
    { unfold prefix, hi.
      replace (2 ^ 64 * 0) with 0 by ring.
      replace (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
      2:{ replace 128 with (64 + 64) by lia.
          rewrite Z.pow_add_r by lia.
          reflexivity. }
      repeat rewrite Z.mul_add_distr_l.
      repeat rewrite <- Z.mul_assoc.
      lia. }
    rewrite Hfull.
    rewrite Hmod_rhs.
    assert (Hlhs :
      WL.U64.to_Z x0 +
      2 ^ 64 *
      (WL.U64.to_Z x1 +
       2 ^ 64 *
       (WL.U64.to_Z
          (or (shl (asr (shl (shr x2 s) 56) 56) s) (land x2 (shl 1 s - 1)%Uint)) +
        2 ^ 64 * (WL.U64.to_Z (asr (asr (shl (shr x2 s) 56) 56) 63) +
                   2 ^ 64 * 0))) =
      prefix +
      2 ^ 128 *
      (WL.U64.to_Z
         (or (shl (asr (shl (shr x2 s) 56) 56) s) (land x2 (shl 1 s - 1)%Uint)) +
       2 ^ 64 * WL.U64.to_Z (asr (asr (shl (shr x2 s) 56) 56) 63))).
    { unfold prefix.
      replace (2 ^ 64 * 0) with 0 by ring.
      replace (2 ^ 128) with (2 ^ 64 * 2 ^ 64).
      2:{ replace 128 with (64 + 64) by lia.
          rewrite Z.pow_add_r by lia.
          reflexivity. }
      repeat rewrite Z.mul_add_distr_l.
      repeat rewrite <- Z.mul_assoc.
      lia. }
    rewrite Hlhs.
    assert (Hcmp_rhs :
      (prefix + 2 ^ 128 * (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8)) <?
         2 ^ (Z.of_nat s + 135)) =
      (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8) <? 2 ^ (Z.of_nat s + 7))).
    { replace (Z.of_nat s + 135) with (128 + (Z.of_nat s + 7)) by lia.
      apply ltb_shifted_prefix.
      - lia.
      - lia.
      - exact Hprefix_range.
      - pose proof
          (Z.mod_pos_bound
             (WL.U64.to_Z x2) (2 ^ (Z.of_nat s + 8))
             ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
        lia. }
    rewrite Hcmp_rhs.
    destruct (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8) <?
                2 ^ (Z.of_nat s + 7)) eqn:Hcmp.
    + rewrite Hcur, Hsign.
      rewrite ?Z.mul_0_r, ?Z.add_0_r.
      reflexivity.
    + rewrite Hcur, Hsign.
      replace
        (prefix +
         2 ^ 128 *
         (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8) +
          (2 ^ 64 - 2 ^ (Z.of_nat s + 8)) +
          2 ^ 64 * (2 ^ 64 - 1 + 2 ^ 64 * 0)))
        with
        (prefix +
         2 ^ 128 * (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8)) +
         2 ^ 128 * (2 ^ 64 - 2 ^ (Z.of_nat s + 8)) +
         2 ^ 192 * (2 ^ 64 - 1)) by ring.
      unfold modulus256.
      rewrite !WL.modulus_words_succ, ?WL.modulus_words_0.
      rewrite Hbase64.
      rewrite pow256_from_words.
      rewrite (signextend_negative_word2 prefix
                 (WL.U64.to_Z x2 mod 2 ^ (Z.of_nat s + 8))
                 (Z.of_nat s)) by lia.
      reflexivity.
  - unfold word in *.
    cbn [get_word uint256_to_words nth w0 w1 w2 w3] in Hcur, Hsign |- *.
    assert (Hb0_div3 : to_Z b0 / 8 = 3).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hb0_decomp : to_Z b0 = 24 + to_Z b0 mod 8).
    { pose proof (Z.div_mod (to_Z b0) 8 ltac:(lia)) as Hdm.
      rewrite Hb0_div3 in Hdm.
      lia. }
    assert (Hbits3 : 8 * (to_Z b0 + 1) = Z.of_nat s + 200).
    { rewrite Hs_eq, Hb0_decomp.
      replace (8 * (24 + to_Z b0 mod 8 + 1))
        with (200 + 8 * (to_Z b0 mod 8)) by ring.
      rewrite Z.add_mod by lia.
      change (200 mod 8) with 0.
      rewrite Z.add_0_l.
      rewrite Z.mod_mod by lia.
      rewrite Z.mod_mod by lia.
      lia. }
    rewrite Hbits3.
    replace (Z.of_nat s + 200 - 1) with (Z.of_nat s + 199) by lia.
    destruct (signextend_current_word x3 s) as [current sign_bits] eqn:Hcw.
    cbn [fill_words_from words_to_uint256 fit_words firstn app repeat
       to_Z_words uint256_to_words to_Z_uint256 w0 w1 w2 w3] in |- *.
    unfold signextend_current_word in Hcw.
    cbn zeta in Hcw.
    inversion Hcw; subst current sign_bits; clear Hcw.
    assert (Hs_le64 : Z.of_nat s + 8 <= 64).
    { apply Nat2Z.inj_le in Hs_le56. lia. }
    assert (Hbase64 : base WL.U64.width = 2 ^ 64).
    { unfold base. rewrite width_is_64. reflexivity. }
    set (prefix :=
      WL.U64.to_Z x0 +
      base WL.U64.width *
      (WL.U64.to_Z x1 + base WL.U64.width * WL.U64.to_Z x2)).
    assert (Hprefix_range : 0 <= prefix < 2 ^ 192).
    { unfold prefix.
      rewrite Hbase64.
      pose proof (spec_to_Z x0) as Hx0.
      pose proof (spec_to_Z x1) as Hx1.
      pose proof (spec_to_Z x2) as Hx2.
      rewrite Hbase64 in Hx0, Hx1, Hx2.
      split; lia. }
    assert (Hmod_rhs :
      (prefix + 2 ^ 192 * WL.U64.to_Z x3) mod 2 ^ (Z.of_nat s + 200) =
      prefix + 2 ^ 192 * (WL.U64.to_Z x3 mod 2 ^ (Z.of_nat s + 8))).
    { replace (Z.of_nat s + 200) with (192 + (Z.of_nat s + 8)) by lia.
      rewrite mod_split_small_prefix by (try lia; exact Hprefix_range).
      reflexivity. }
    rewrite Hbase64.
    assert (Hfull :
      WL.U64.to_Z x0 +
      2 ^ 64 *
      (WL.U64.to_Z x1 +
       2 ^ 64 * (WL.U64.to_Z x2 + 2 ^ 64 * (WL.U64.to_Z x3 + 2 ^ 64 * 0))) =
      prefix + 2 ^ 192 * WL.U64.to_Z x3).
    { unfold prefix.
      replace (2 ^ 64 * 0) with 0 by ring.
      replace (2 ^ 192) with (2 ^ 64 * 2 ^ 64 * 2 ^ 64).
      2:{ replace 192 with (64 + (64 + 64)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.pow_add_r by lia.
          reflexivity. }
      repeat rewrite Z.mul_add_distr_l.
      repeat rewrite <- Z.mul_assoc.
      lia. }
    rewrite Hfull.
    rewrite Hmod_rhs.
    assert (Hlhs :
      WL.U64.to_Z x0 +
      2 ^ 64 *
      (WL.U64.to_Z x1 +
       2 ^ 64 *
       (WL.U64.to_Z x2 +
        2 ^ 64 *
        (WL.U64.to_Z
           (or (shl (asr (shl (shr x3 s) 56) 56) s) (land x3 (shl 1 s - 1)%Uint)) +
         2 ^ 64 * 0))) =
      prefix +
      2 ^ 192 *
      WL.U64.to_Z
        (or (shl (asr (shl (shr x3 s) 56) 56) s) (land x3 (shl 1 s - 1)%Uint))).
    { unfold prefix.
      replace (2 ^ 64 * 0) with 0 by ring.
      replace (2 ^ 192) with (2 ^ 64 * 2 ^ 64 * 2 ^ 64).
      2:{ replace 192 with (64 + (64 + 64)) by lia.
          rewrite Z.pow_add_r by lia.
          rewrite Z.pow_add_r by lia.
          reflexivity. }
      repeat rewrite Z.mul_add_distr_l.
      repeat rewrite <- Z.mul_assoc.
      lia. }
    rewrite Hlhs.
    assert (Hcmp_rhs :
      (prefix + 2 ^ 192 * (WL.U64.to_Z x3 mod 2 ^ (Z.of_nat s + 8)) <?
         2 ^ (Z.of_nat s + 199)) =
      (WL.U64.to_Z x3 mod 2 ^ (Z.of_nat s + 8) <? 2 ^ (Z.of_nat s + 7))).
    { replace (Z.of_nat s + 199) with (192 + (Z.of_nat s + 7)) by lia.
      apply ltb_shifted_prefix.
      - lia.
      - lia.
      - exact Hprefix_range.
      - pose proof
          (Z.mod_pos_bound
             (WL.U64.to_Z x3) (2 ^ (Z.of_nat s + 8))
             ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
        lia. }
    rewrite Hcmp_rhs.
    destruct (WL.U64.to_Z x3 mod 2 ^ (Z.of_nat s + 8) <?
                2 ^ (Z.of_nat s + 7)) eqn:Hcmp.
    + rewrite Hcur.
      rewrite ?Z.mul_0_r, ?Z.add_0_r.
      reflexivity.
    + rewrite Hcur.
      unfold modulus256.
      rewrite !WL.modulus_words_succ, ?WL.modulus_words_0.
      rewrite Hbase64.
      rewrite pow256_from_words.
      rewrite (signextend_negative_word3 prefix
                 (WL.U64.to_Z x3 mod 2 ^ (Z.of_nat s + 8))
                 (Z.of_nat s)) by lia.
      reflexivity.
Qed.

Lemma to_Z_byte_limit :
  to_Z_uint256 (mk_uint256 (shl one 5) zero zero zero) = 32.
Proof.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3 WL.to_Z_words].
  rewrite to_Z_shl_one by (rewrite width_is_64; simpl; lia).
  rewrite !spec_zero.
  lia.
Qed.

Lemma byte_word_index_nat_correct : forall word_index,
  0 <= to_Z word_index < 4 ->
  byte_word_index_nat word_index = Z.to_nat (to_Z word_index).
Proof.
  intros word_index [Hword_ge Hword_lt].
  assert (Htwo : to_Z (add one one) = 2).
  { rewrite !spec_add, !spec_one.
    rewrite Z.mod_small.
    - reflexivity.
    - unfold base. rewrite width_is_64. lia. }
  unfold byte_word_index_nat.
  destruct (Z.eq_dec (to_Z word_index) 0) as [H0|H0].
  - rewrite spec_eqb, spec_zero, H0. reflexivity.
  - rewrite spec_eqb, spec_zero.
    replace (to_Z word_index =? 0) with false.
    2:{ symmetry. apply Z.eqb_neq. exact H0. }
    destruct (Z.eq_dec (to_Z word_index) 1) as [H1|H1].
    + rewrite spec_eqb, spec_one, H1. reflexivity.
    + rewrite spec_eqb, spec_one.
      replace (to_Z word_index =? 1) with false.
      2:{ symmetry. apply Z.eqb_neq. exact H1. }
      destruct (Z.eq_dec (to_Z word_index) 2) as [H2|H2].
      * rewrite spec_eqb, Htwo, H2. reflexivity.
      * rewrite spec_eqb, Htwo.
        replace (to_Z word_index =? 2) with false.
        2:{ symmetry. apply Z.eqb_neq. exact H2. }
        assert (H3 : to_Z word_index = 3) by lia.
        rewrite H3. reflexivity.
Qed.

Lemma byte_value_to_Z : forall word s,
  to_Z (land (shr word s) (sub (shl one 8) one)) =
    (to_Z word / 2 ^ Z.of_nat s) mod 256.
Proof.
  intros word s.
  rewrite to_Z_land_low_mask by (rewrite width_is_64; simpl; lia).
  rewrite to_Z_shr.
  change (2 ^ Z.of_nat 8) with 256.
  reflexivity.
Qed.

Lemma to_Z_uint256_low_word : forall word,
  to_Z_uint256 (mk_uint256 word zero zero zero) = to_Z word.
Proof.
  intro word.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3 WL.to_Z_words].
  rewrite !spec_zero.
  rewrite ?Z.mul_0_r, ?Z.add_0_r.
  reflexivity.
Qed.

Lemma byte_extract_low_word : forall low tail m,
  0 <= m <= 56 ->
  ((to_Z low + 2 ^ 64 * tail) / 2 ^ m) mod 256 =
    (to_Z low / 2 ^ m) mod 256.
Proof.
  intros low tail m Hm.
  replace (2 ^ 64 * tail) with ((2 ^ (64 - m) * tail) * 2 ^ m).
  2:{ replace ((2 ^ (64 - m) * tail) * 2 ^ m)
        with (2 ^ (64 - m) * 2 ^ m * tail) by ring.
      rewrite <- Z.pow_add_r by lia.
      replace (64 - m + m) with 64 by lia.
      ring. }
  rewrite Z.div_add by (apply Z.pow_nonzero; lia).
  replace (2 ^ (64 - m) * tail) with ((2 ^ (56 - m) * tail) * 256).
  2:{ change 256 with (2 ^ 8).
      replace ((2 ^ (56 - m) * tail) * 2 ^ 8)
        with (2 ^ (56 - m) * 2 ^ 8 * tail) by ring.
      rewrite <- Z.pow_add_r by lia.
      replace (56 - m + 8) with (64 - m) by lia.
      ring. }
  rewrite Z.mod_add by lia.
  reflexivity.
Qed.

Lemma byte_extract_low_words : forall low rest m,
  0 <= m <= 56 ->
  (to_Z_words (low :: rest) / 2 ^ m) mod 256 =
    (to_Z low / 2 ^ m) mod 256.
Proof.
  intros low rest m Hm.
  cbn [WL.to_Z_words].
  unfold base.
  rewrite width_is_64.
  now apply byte_extract_low_word.
Qed.

Lemma byte_extract_uint256_word0 : forall x0 x1 x2 x3 m,
  0 <= m <= 56 ->
  (to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / 2 ^ m) mod 256 =
    (to_Z x0 / 2 ^ m) mod 256.
Proof.
  intros x0 x1 x2 x3 m Hm.
  unfold to_Z_uint256, uint256_to_words.
  cbn [w0 w1 w2 w3].
  now apply byte_extract_low_words.
Qed.

Lemma byte_extract_uint256_word1 : forall x0 x1 x2 x3 m,
  0 <= m <= 56 ->
  (to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / 2 ^ (64 + m)) mod 256 =
    (to_Z x1 / 2 ^ m) mod 256.
Proof.
  intros x0 x1 x2 x3 m Hm.
  replace (2 ^ (64 + m)) with (2 ^ 64 * 2 ^ m)
    by (rewrite Z.pow_add_r by lia; reflexivity).
  rewrite <- Z.div_div by
    (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  replace (2 ^ 64) with (modulus_words 1) by
    (rewrite modulus_words_1; reflexivity).
  rewrite to_Z_uint256_div_modulus_words_1.
  now apply byte_extract_low_words.
Qed.

Lemma byte_extract_uint256_word2 : forall x0 x1 x2 x3 m,
  0 <= m <= 56 ->
  (to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / 2 ^ (128 + m)) mod 256 =
    (to_Z x2 / 2 ^ m) mod 256.
Proof.
  intros x0 x1 x2 x3 m Hm.
  replace (2 ^ (128 + m)) with (2 ^ 128 * 2 ^ m)
    by (rewrite Z.pow_add_r by lia; reflexivity).
  rewrite <- Z.div_div by
    (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  replace (2 ^ 128) with (modulus_words 2) by
    (rewrite modulus_words_2; reflexivity).
  rewrite to_Z_uint256_div_modulus_words_2.
  now apply byte_extract_low_words.
Qed.

Lemma byte_extract_uint256_word3 : forall x0 x1 x2 x3 m,
  0 <= m <= 56 ->
  (to_Z_uint256 (mk_uint256 x0 x1 x2 x3) / 2 ^ (192 + m)) mod 256 =
    (to_Z x3 / 2 ^ m) mod 256.
Proof.
  intros x0 x1 x2 x3 m Hm.
  replace (2 ^ (192 + m)) with (2 ^ 192 * 2 ^ m)
    by (rewrite Z.pow_add_r by lia; reflexivity).
  rewrite <- Z.div_div by
    (try apply Z.pow_nonzero; try apply Z.pow_pos_nonneg; lia).
  replace (2 ^ 192) with (modulus_words 3) by
    (rewrite modulus_words_3; reflexivity).
  rewrite to_Z_uint256_div_modulus_words_3.
  now apply byte_extract_low_words.
Qed.

Theorem byte_correct : forall byte_index_256 x,
  to_Z_uint256 (byte byte_index_256 x) =
    byte_Z (to_Z_uint256 byte_index_256) (to_Z_uint256 x).
Proof.
  intros [b0 b1 b2 b3] [x0 x1 x2 x3].
  set (idx := mk_uint256 b0 b1 b2 b3).
  remember (ltb_uint256 idx (mk_uint256 (shl one 5) zero zero zero))
    as in_range eqn:Hidx.
  destruct in_range.
  2:{ symmetry in Hidx.
      pose proof Hidx as Hltb.
      rewrite ltb_uint256_correct in Hltb.
      rewrite to_Z_byte_limit in Hltb.
      apply Z.ltb_ge in Hltb.
      unfold byte.
      rewrite Hidx.
      cbn [negb zero_uint256 to_Z_uint256 uint256_to_words w0 w1 w2 w3
           WL.to_Z_words].
      rewrite !spec_zero.
      rewrite ?Z.mul_0_r, ?Z.add_0_r.
      cbn [to_Z_uint256 uint256_to_words w0 w1 w2 w3 WL.to_Z_words]
        in Hltb.
      rewrite ?Z.mul_0_r, ?Z.add_0_r in Hltb.
      unfold byte_Z.
      match goal with
      | |- 0 = (if ?cond then _ else _) => destruct cond eqn:Hcmp
      end.
      - apply Z.ltb_lt in Hcmp. lia.
      - reflexivity. }
  symmetry in Hidx.
  pose proof Hidx as Hltb.
  rewrite ltb_uint256_correct in Hltb.
  rewrite to_Z_byte_limit in Hltb.
  apply Z.ltb_lt in Hltb.
  assert (Hlt_base : to_Z_uint256 idx < base width).
  { unfold base. rewrite width_is_64. lia. }
  destruct (to_Z_uint256_lt_base_zero_high b0 b1 b2 b3 Hlt_base)
    as [Hb1z [Hb2z Hb3z]].
  assert (Hb : to_Z_uint256 idx = to_Z b0).
  { unfold idx, to_Z_uint256, uint256_to_words.
    cbn [w0 w1 w2 w3 to_Z_words].
    rewrite Hb1z, Hb2z, Hb3z.
    rewrite ?Z.mul_0_r, ?Z.add_0_r.
    reflexivity. }
  assert (Hb0_range : 0 <= to_Z b0 < 32).
  { pose proof (spec_to_Z b0) as Hb0.
    lia. }
  set (byte_index := ((shl 1 5 - 1) - b0)%Uint).
  assert (Hbyte_index : to_Z byte_index = 31 - to_Z b0).
  { subst byte_index.
    rewrite spec_sub.
    rewrite to_Z_low_mask by (rewrite width_is_64; simpl; lia).
    rewrite Z.mod_small.
    - reflexivity.
    - split.
      + lia.
      + unfold base. rewrite width_is_64. lia. }
  assert (Hword_index : to_Z (shr byte_index 3) = to_Z byte_index / 8)
    by now rewrite to_Z_shr.
  assert (Hword_range : 0 <= to_Z (shr byte_index 3) < 4).
  { rewrite Hword_index, Hbyte_index.
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound; lia. }
  assert (Hword_index_n :
    byte_word_index_nat (shr byte_index 3) =
      Z.to_nat (to_Z (shr byte_index 3)))
    by (now apply byte_word_index_nat_correct).
  unfold byte.
  subst idx.
  rewrite Hidx.
  cbn [negb w0 w1 w2 w3].
  fold byte_index.
  rewrite Hword_index_n, Hb.
  unfold byte_Z.
  replace (to_Z b0 <? 32) with true
    by (symmetry; apply Z.ltb_lt; lia).
  set (n := Z.to_nat (to_Z (shr byte_index 3))).
  set (s := bounded_shift_nat word_width
                              (shl (land byte_index (shl 1 3 - 1)%Uint) 3)).
  assert (Hmask3 :
    to_Z (land byte_index (shl 1 3 - 1)%Uint) = to_Z byte_index mod 8).
  { change ((shl 1 3 - 1)%Uint) with (sub (shl one 3) one).
    rewrite to_Z_land_low_mask by (rewrite width_is_64; simpl; lia).
    change (2 ^ Z.of_nat 3) with 8.
    reflexivity. }
  assert (Hshift_bits :
    to_Z (shl (land byte_index (shl 1 3 - 1)%Uint) 3) =
      8 * (to_Z byte_index mod 8)).
  { rewrite spec_shl, Hmask3.
    rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small.
    2:{ split.
        - pose proof (Z.mod_pos_bound (to_Z byte_index) 8 ltac:(lia)) as Hmod.
          lia.
        - unfold base. rewrite width_is_64.
          pose proof (Z.mod_pos_bound (to_Z byte_index) 8 ltac:(lia)) as Hmod.
          lia. }
    change (2 ^ Z.of_nat 3) with 8.
    ring. }
  assert (Hs_eq : Z.of_nat s = 8 * (to_Z byte_index mod 8)).
  { subst s.
    rewrite (bounded_shift_nat_correct word_width
               (shl (land byte_index (shl 1 3 - 1)%Uint) 3)).
    2:{ apply Nat.le_refl. }
    2:{ rewrite Hshift_bits.
        unfold word_width.
        rewrite width_is_64.
        change (Z.of_nat 64) with 64.
        pose proof (Z.mod_pos_bound (to_Z byte_index) 8 ltac:(lia)) as Hmod.
        lia. }
    assert (Hshift_nonneg :
      0 <= to_Z (shl (land byte_index (shl 1 3 - 1)%Uint) 3)).
    { rewrite Hshift_bits.
      pose proof (Z.mod_pos_bound (to_Z byte_index) 8 ltac:(lia)) as Hmod.
      lia. }
    rewrite Z2Nat.id by exact Hshift_nonneg.
    exact Hshift_bits. }
  assert (Hs_range : 0 <= Z.of_nat s <= 56).
  { rewrite Hs_eq.
    pose proof (Z.mod_pos_bound (to_Z byte_index) 8 ltac:(lia)) as Hmod.
    lia. }
  assert (Hnlt : (n < 4)%nat).
  { subst n.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    lia. }
  destruct n as [|[|[|[|n']]]] eqn:Hn; try lia;
    cbn [get_word uint256_to_words nth w0 w1 w2 w3] in |- *;
    rewrite to_Z_uint256_low_word;
    rewrite byte_value_to_Z.
  - assert (Hbyte_div0 : to_Z byte_index / 8 = 0).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hbyte_decomp : to_Z byte_index = to_Z byte_index mod 8).
    { pose proof (Z.div_mod (to_Z byte_index) 8 ltac:(lia)) as Hdm.
      rewrite Hbyte_div0 in Hdm.
      lia. }
    assert (Hbits0 : 8 * (31 - to_Z b0) = Z.of_nat s).
    { rewrite <- Hbyte_index.
      rewrite Hs_eq.
      rewrite Hbyte_decomp at 1.
      reflexivity. }
    rewrite Hbits0.
    rewrite byte_extract_uint256_word0 by exact Hs_range.
    reflexivity.
  - assert (Hbyte_div1 : to_Z byte_index / 8 = 1).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hbyte_decomp : to_Z byte_index = 8 + to_Z byte_index mod 8).
    { pose proof (Z.div_mod (to_Z byte_index) 8 ltac:(lia)) as Hdm.
      rewrite Hbyte_div1 in Hdm.
      lia. }
    assert (Hbits1 : 8 * (31 - to_Z b0) = 64 + Z.of_nat s).
    { rewrite <- Hbyte_index.
      rewrite Hs_eq.
      rewrite Hbyte_decomp at 1.
      lia. }
    rewrite Hbits1.
    rewrite byte_extract_uint256_word1 by exact Hs_range.
    reflexivity.
  - assert (Hbyte_div2 : to_Z byte_index / 8 = 2).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hbyte_decomp : to_Z byte_index = 16 + to_Z byte_index mod 8).
    { pose proof (Z.div_mod (to_Z byte_index) 8 ltac:(lia)) as Hdm.
      rewrite Hbyte_div2 in Hdm.
      lia. }
    assert (Hbits2 : 8 * (31 - to_Z b0) = 128 + Z.of_nat s).
    { rewrite <- Hbyte_index.
      rewrite Hs_eq.
      rewrite Hbyte_decomp at 1.
      lia. }
    rewrite Hbits2.
    rewrite byte_extract_uint256_word2 by exact Hs_range.
    reflexivity.
  - assert (Hbyte_div3 : to_Z byte_index / 8 = 3).
    { subst n.
      apply (f_equal Z.of_nat) in Hn.
      cbn in Hn.
      rewrite Z2Nat.id in Hn by lia.
      rewrite <- Hword_index.
      exact Hn. }
    assert (Hbyte_decomp : to_Z byte_index = 24 + to_Z byte_index mod 8).
    { pose proof (Z.div_mod (to_Z byte_index) 8 ltac:(lia)) as Hdm.
      rewrite Hbyte_div3 in Hdm.
      lia. }
    assert (Hbits3 : 8 * (31 - to_Z b0) = 192 + Z.of_nat s).
    { rewrite <- Hbyte_index.
      rewrite Hs_eq.
      rewrite Hbyte_decomp at 1.
      lia. }
    rewrite Hbits3.
    rewrite byte_extract_uint256_word3 by exact Hs_range.
    reflexivity.
Qed.

Lemma countl_zero_to_Z_zero : forall x,
  to_Z x = 0 ->
  countl_zero x = word_width.
Proof.
  intros x Hx.
  assert (Hgo : forall n, countl_zero_go x n = n).
  { induction n as [|n IH].
    - reflexivity.
    - cbn [countl_zero_go].
      assert (Hshr : (shr x n =? zero)%Uint = true).
      { rewrite spec_eqb, spec_shr, spec_zero, Hx.
        rewrite Z.shiftr_0_l.
        rewrite Z.mod_0_l by (unfold base; pose proof width_is_64; lia).
        reflexivity. }
      rewrite Hshr.
      now f_equal. }
  unfold countl_zero, word_width.
  apply Hgo.
Qed.

Lemma countl_zero_nonzero_lt_width : forall x,
  to_Z x > 0 ->
  (countl_zero x < word_width)%nat.
Proof.
  intros x Hx.
  unfold word_width.
  now apply DP.countl_zero_bound.
Qed.

Theorem countl_zero_uint256_correct : forall x,
  countl_zero_uint256 x =
    match count_significant_words (uint256_to_words x) with
    | O => (4 * word_width)%nat
    | S words_before =>
        (((4 - S words_before) * word_width) +
          countl_zero (get_word (uint256_to_words x) words_before))%nat
    end.
Proof.
  intros [x0 x1 x2 x3].
  unfold countl_zero_uint256, count_significant_words, uint256_to_words.
  cbn [w0 w1 w2 w3 rev skip_leading_zeros length get_word nth].
  destruct (x3 =? zero)%Uint eqn:Hx3.
  - pose proof Hx3 as Hx3z.
    rewrite spec_eqb in Hx3z. apply Z.eqb_eq in Hx3z.
    rewrite spec_zero in Hx3z.
    rewrite (countl_zero_to_Z_zero x3 Hx3z).
    replace (Nat.eqb word_width (1 * word_width)) with true
      by (symmetry; apply Nat.eqb_eq; lia).
    destruct (x2 =? zero)%Uint eqn:Hx2.
    + pose proof Hx2 as Hx2z.
      rewrite spec_eqb in Hx2z. apply Z.eqb_eq in Hx2z.
      rewrite spec_zero in Hx2z.
      rewrite (countl_zero_to_Z_zero x2 Hx2z).
      replace (Nat.eqb (word_width + word_width) (2 * word_width))
        with true by (symmetry; apply Nat.eqb_eq; lia).
      destruct (x1 =? zero)%Uint eqn:Hx1.
      * pose proof Hx1 as Hx1z.
        rewrite spec_eqb in Hx1z. apply Z.eqb_eq in Hx1z.
        rewrite spec_zero in Hx1z.
        rewrite (countl_zero_to_Z_zero x1 Hx1z).
        replace (Nat.eqb (word_width + word_width + word_width)
          (3 * word_width)) with true
          by (symmetry; apply Nat.eqb_eq; lia).
        destruct (x0 =? zero)%Uint eqn:Hx0.
        -- pose proof Hx0 as Hx0z.
           rewrite spec_eqb in Hx0z. apply Z.eqb_eq in Hx0z.
           rewrite spec_zero in Hx0z.
           rewrite (countl_zero_to_Z_zero x0 Hx0z).
           cbn [app skip_leading_zeros length get_word nth].
           rewrite Hx3, Hx2, Hx1, Hx0.
           cbn.
           lia.
        -- pose proof Hx0 as Hx0z.
           rewrite spec_eqb in Hx0z. apply Z.eqb_neq in Hx0z.
           rewrite spec_zero in Hx0z.
           pose proof (spec_to_Z x0) as Hx0_bounds.
           pose proof (countl_zero_nonzero_lt_width x0 ltac:(lia))
             as Hx0_clz.
           cbn [app skip_leading_zeros length get_word nth].
           rewrite Hx3, Hx2, Hx1, Hx0.
           cbn.
           lia.
      * pose proof Hx1 as Hx1z.
        rewrite spec_eqb in Hx1z. apply Z.eqb_neq in Hx1z.
        rewrite spec_zero in Hx1z.
        pose proof (spec_to_Z x1) as Hx1_bounds.
        pose proof (countl_zero_nonzero_lt_width x1 ltac:(lia))
          as Hx1_clz.
        replace (Nat.eqb (word_width + word_width + countl_zero x1)
          (3 * word_width)) with false.
        2:{ symmetry. apply Nat.eqb_neq. lia. }
        cbn [app skip_leading_zeros length get_word nth].
        rewrite Hx3, Hx2, Hx1.
        cbn.
        lia.
    + pose proof Hx2 as Hx2z.
      rewrite spec_eqb in Hx2z. apply Z.eqb_neq in Hx2z.
      rewrite spec_zero in Hx2z.
      pose proof (spec_to_Z x2) as Hx2_bounds.
      pose proof (countl_zero_nonzero_lt_width x2 ltac:(lia))
        as Hx2_clz.
      replace (Nat.eqb (word_width + countl_zero x2) (2 * word_width))
        with false.
      2:{ symmetry. apply Nat.eqb_neq. lia. }
      cbn [app skip_leading_zeros length get_word nth].
      rewrite Hx3, Hx2.
      cbn.
      lia.
  - pose proof Hx3 as Hx3z.
    rewrite spec_eqb in Hx3z. apply Z.eqb_neq in Hx3z.
    rewrite spec_zero in Hx3z.
    pose proof (spec_to_Z x3) as Hx3_bounds.
    pose proof (countl_zero_nonzero_lt_width x3 ltac:(lia)) as Hx3_clz.
    replace (Nat.eqb (countl_zero x3) (1 * word_width)) with false.
    2:{ symmetry. apply Nat.eqb_neq. lia. }
    cbn [app skip_leading_zeros length get_word nth].
    rewrite Hx3.
    cbn.
    lia.
Qed.

Theorem count_significant_bytes_correct : forall x,
  count_significant_bytes x =
    (((4 * word_width - countl_zero_uint256 x) + 7) / 8)%nat.
Proof.
  intro x.
  rewrite countl_zero_uint256_correct.
  unfold count_significant_bytes.
  set (ws := uint256_to_words x).
  pose proof (DP.count_significant_words_bound ws) as Hbound.
  assert (Hlen : length ws = 4%nat).
  { subst ws. apply uint256_to_words_length. }
  rewrite Hlen in Hbound.
  destruct (count_significant_words ws) as [|words_before] eqn:Hcsw.
  - replace (4 * word_width - 4 * word_width)%nat with 0%nat by lia.
    reflexivity.
  - pose proof (DP.count_significant_words_msw_nonzero ws) as Hmsw.
    cbv zeta in Hmsw.
    rewrite Hcsw in Hmsw.
    specialize (Hmsw ltac:(lia)).
    replace (S words_before - 1)%nat with words_before in Hmsw by lia.
    pose proof (countl_zero_nonzero_lt_width
      (get_word ws words_before) Hmsw) as Hclz.
    set (c := countl_zero (get_word ws words_before)) in *.
    unfold word_width in *.
    rewrite width_is_64 in *.
    change (Pos.to_nat 64) with 64%nat in *.
    destruct words_before as [|[|[|[|words_before]]]]; try lia.
    + replace (4 * 64 - ((4 - 1) * 64 + c))%nat
        with (64 - c)%nat by lia.
      lia.
    + replace (4 * 64 - ((4 - 2) * 64 + c) + 7)%nat
        with ((64 - c + 7) + 8 * 8)%nat by lia.
      rewrite Nat.div_add by lia.
      lia.
    + replace (4 * 64 - ((4 - 3) * 64 + c) + 7)%nat
        with ((64 - c + 7) + 16 * 8)%nat by lia.
      rewrite Nat.div_add by lia.
      lia.
    + replace (4 * 64 - ((4 - 4) * 64 + c) + 7)%nat
        with ((64 - c + 7) + 24 * 8)%nat by lia.
      rewrite Nat.div_add by lia.
      lia.
Qed.

Lemma is_two_uint256_true : forall x,
  is_two_uint256 x = true ->
  to_Z_uint256 x = 2.
Proof.
  intros [x0 x1 x2 x3] Htwo.
  unfold is_two_uint256 in Htwo.
  cbn [w0 w1 w2 w3 andb] in Htwo.
  repeat rewrite Bool.andb_true_iff in Htwo.
  destruct Htwo as [[[Hx0 Hx1] Hx2] Hx3].
  rewrite spec_eqb in *. apply Z.eqb_eq in Hx0,Hx1,Hx2,Hx3.
  rewrite spec_add, !spec_one in Hx0.
  change ((1 + 1) mod base width) with (2 mod base width) in Hx0.
  rewrite Z.mod_small in Hx0
      by (unfold base; rewrite width_is_64; lia).
  unfold to_Z_uint256, uint256_to_words; cbn [w0 w1 w2 w3].
  cbn [WL.to_Z_words].
  rewrite Hx0, Hx1, Hx2, Hx3, !spec_zero.
  lia.
Qed.

Lemma to_Z_words_one_words_generic_4 :
  to_Z_words (one_words_generic 4) = 1.
Proof.
  unfold one_words_generic.
  rewrite WL.to_Z_words_set_word.
  2:{ rewrite WL.extend_words_length. lia. }
  rewrite WL.to_Z_extend_words.
  rewrite WL.get_extend_words_zero by lia.
  rewrite spec_zero, spec_one.
  rewrite Z.pow_0_r by lia.
  lia.
Qed.

Lemma truncating_mul_runtime_exact_4 : forall xs ys,
  length xs = 4%nat ->
  length ys = 4%nat ->
  to_Z_words (RM.truncating_mul_runtime xs ys 4) =
    (to_Z_words xs * to_Z_words ys) mod modulus256.
Proof.
  intros xs ys Hx Hy.
  pose proof (RMP.truncating_mul256_runtime_correct xs ys Hx Hy) as Hmul.
  pose proof (WL.to_Z_words_bound (RM.truncating_mul_runtime xs ys 4)) as Hbound.
  rewrite RMP.truncating_mul_runtime_length in Hbound by lia.
  change (WL.modulus_words 4) with modulus256 in Hmul.
  change (WL.modulus_words 4) with modulus256 in Hbound.
  rewrite Z.mod_small in Hmul by lia.
  exact Hmul.
Qed.
Lemma to_Z_shr_1 : forall x,
  to_Z (shr x 1) = to_Z x / 2.
Proof.
  intro x.
  rewrite spec_shr.
  rewrite Z.shiftr_div_pow2 by lia.
  change (2 ^ Z.of_nat 1) with 2.
  rewrite Z.mod_small.
  - reflexivity.
  - pose proof (spec_to_Z x) as Hx.
    split.
    + apply Z.div_pos; lia.
    + apply Z.div_lt_upper_bound.
      * lia.
      * nia.
Qed.

Lemma to_Z_shl_shr_1 : forall x,
  to_Z (shl (shr x 1) 1) = 2 * to_Z (shr x 1).
Proof.
  intro x.
  rewrite spec_shl.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite Z.pow_1_r.
  rewrite Z.mod_small.
  - ring.
  - pose proof (spec_to_Z x) as Hx.
    rewrite to_Z_shr_1.
    assert (Hle : 2 * (to_Z x / 2) <= to_Z x).
    { pose proof (Z.div_mod (to_Z x) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (to_Z x) 2 ltac:(lia)) as Hmod.
      lia. }
    split.
    + apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia|lia].
    + lia.
Qed.

Lemma odd_word_shr_decompose : forall x,
  to_Z x = 2 * to_Z (shr x 1) + if odd_word x then 1 else 0.
Proof.
  intro x.
  unfold odd_word.
  destruct ((x =? shl (shr x 1) 1)%Uint) eqn:Heq.
  - rewrite spec_eqb in Heq.
    apply Z.eqb_eq in Heq.
    rewrite Heq.
    rewrite to_Z_shl_shr_1.
    cbn. lia.
  - rewrite spec_eqb in Heq.
    apply Z.eqb_neq in Heq.
    rewrite to_Z_shr_1.
    assert (Hdiv : to_Z x = 2 * (to_Z x / 2) + to_Z x mod 2).
    { pose proof (Z.div_mod (to_Z x) 2 ltac:(lia)) as Hdiv.
      lia. }
    assert (Hrem : 0 <= to_Z x mod 2 < 2).
    { apply Z.mod_pos_bound. lia. }
    assert (Hneq : to_Z x <> 2 * (to_Z x / 2)).
    { intro Hcontra.
      apply Heq.
      rewrite to_Z_shl_shr_1, to_Z_shr_1.
      exact Hcontra. }
    assert (Hr1 : to_Z x mod 2 = 1) by lia.
    cbn [negb]. rewrite Hr1 in Hdiv. exact Hdiv.
Qed.

Lemma two_pow_nat_succ : forall n,
  2 ^ Z.of_nat (S n) = 2 * 2 ^ Z.of_nat n.
Proof.
  intro n.
  replace (Z.of_nat (S n)) with (Z.of_nat n + 1) by lia.
  rewrite Z.pow_add_r by lia.
  rewrite Z.pow_1_r.
  ring.
Qed.

Lemma square_pow : forall b q,
  0 <= q ->
  (b * b) ^ q = b ^ (2 * q).
Proof.
  intros b q Hq.
  replace (b * b) with (b ^ 2) by (rewrite Z.pow_2_r; ring).
  rewrite <- Z.pow_mul_r by lia.
  reflexivity.
Qed.

Lemma shr_lt_two_pow : forall bits x,
  to_Z x < 2 ^ Z.of_nat (S bits) ->
  to_Z (shr x 1) < 2 ^ Z.of_nat bits.
Proof.
  intros bits x Hlt.
  rewrite to_Z_shr_1.
  rewrite two_pow_nat_succ in Hlt.
  apply Z.div_lt_upper_bound; lia.
Qed.

Lemma truncating_mul_runtime_semantic_4 : forall xs ys a b,
  length xs = 4%nat ->
  length ys = 4%nat ->
  to_Z_words xs = a mod modulus256 ->
  to_Z_words ys = b mod modulus256 ->
  to_Z_words (RM.truncating_mul_runtime xs ys 4) = (a * b) mod modulus256.
Proof.
  intros xs ys a b Hx Hy Hxs Hys.
  rewrite (truncating_mul_runtime_exact_4 xs ys Hx Hy).
  rewrite Hxs, Hys.
  rewrite <- Z.mul_mod by (pose proof modulus256_pos; lia).
  reflexivity.
Qed.

Lemma exp_sigbit_loop_correct_4 :
  forall bits word_exp base result b r,
  length base = 4%nat ->
  length result = 4%nat ->
  to_Z_words base = b mod modulus256 ->
  to_Z_words result = r mod modulus256 ->
  to_Z word_exp < 2 ^ Z.of_nat bits ->
  let '(base', result') := exp_sigbit_loop 4 bits word_exp base result in
  length base' = 4%nat /\
  length result' = 4%nat /\
  to_Z_words base' = b ^ (2 ^ Z.of_nat bits) mod modulus256 /\
  to_Z_words result' = (r * b ^ to_Z word_exp) mod modulus256.
Proof.
  induction bits as [|bits IH];
    intros word_exp base result b r Hbase_len Hresult_len Hbase Hresult Hexp.
  - simpl in Hexp.
    assert (Hz : to_Z word_exp = 0).
    { pose proof (spec_to_Z word_exp) as Hword. lia. }
    simpl.
    rewrite Hz, Z.pow_0_r, Z.mul_1_r.
    change (Z.pow_pos b 1 mod modulus256) with (b ^ 1 mod modulus256).
    rewrite Z.pow_1_r.
    repeat split; assumption.
  - simpl exp_sigbit_loop.
    remember (odd_word word_exp) as odd eqn:Hodd.
    set (result0 := if odd then RM.truncating_mul_runtime result base 4 else result).
    set (base0 := RM.truncating_mul_runtime base base 4).
    assert (Hbase0_len : length base0 = 4%nat).
    { subst base0. apply RMP.truncating_mul_runtime_length. lia. }
    assert (Hbase0 : to_Z_words base0 = (b * b) mod modulus256).
    { subst base0.
      apply truncating_mul_runtime_semantic_4; assumption. }
    assert (Hshr_bound : to_Z (shr word_exp 1) < 2 ^ Z.of_nat bits).
    { apply shr_lt_two_pow. exact Hexp. }
    assert (Hpow_nonneg : 0 <= 2 ^ Z.of_nat bits) by (apply Z.pow_nonneg; lia).
    assert (Hshr_nonneg : 0 <= to_Z (shr word_exp 1)).
    { pose proof (spec_to_Z (shr word_exp 1)) as Hshr. lia. }
    destruct odd.
    + assert (Hresult0_len : length result0 = 4%nat).
      { subst result0. apply RMP.truncating_mul_runtime_length. lia. }
      assert (Hresult0 : to_Z_words result0 = (r * b) mod modulus256).
      { subst result0.
        apply truncating_mul_runtime_semantic_4; assumption. }
      specialize (IH (shr word_exp 1) base0 result0 (b * b) (r * b)
        Hbase0_len Hresult0_len Hbase0 Hresult0 Hshr_bound).
      destruct (exp_sigbit_loop 4 bits (shr word_exp 1) base0 result0)
        as [base' result'] eqn:Hloop.
      simpl in IH.
      destruct IH as [Hbase'_len [Hresult'_len [Hbase' Hresult']]].
      pose proof (odd_word_shr_decompose word_exp) as Hoddexp.
      rewrite <- Hodd in Hoddexp.
      repeat split.
      * exact Hbase'_len.
      * exact Hresult'_len.
      * rewrite Hbase'.
        rewrite square_pow by exact Hpow_nonneg.
        rewrite two_pow_nat_succ.
        reflexivity.
      * rewrite Hresult'.
        rewrite square_pow by exact Hshr_nonneg.
        rewrite Hoddexp.
        replace (2 * to_Z (shr word_exp 1) + 1) with
          (1 + 2 * to_Z (shr word_exp 1)) by lia.
        rewrite Z.pow_add_r by lia.
        rewrite Z.pow_1_r.
        replace (r * b * b ^ (2 * to_Z (shr word_exp 1))) with
          (r * (b * b ^ (2 * to_Z (shr word_exp 1)))) by ring.
        reflexivity.
    + assert (Hresult0_len : length result0 = 4%nat).
      { subst result0. exact Hresult_len. }
      assert (Hresult0 : to_Z_words result0 = r mod modulus256).
      { subst result0. exact Hresult. }
      specialize (IH (shr word_exp 1) base0 result0 (b * b) r
        Hbase0_len Hresult0_len Hbase0 Hresult0 Hshr_bound).
      destruct (exp_sigbit_loop 4 bits (shr word_exp 1) base0 result0)
        as [base' result'] eqn:Hloop.
      simpl in IH.
      destruct IH as [Hbase'_len [Hresult'_len [Hbase' Hresult']]].
      pose proof (odd_word_shr_decompose word_exp) as Hoddexp.
      rewrite <- Hodd in Hoddexp.
      repeat split.
      * exact Hbase'_len.
      * exact Hresult'_len.
      * rewrite Hbase'.
        rewrite square_pow by exact Hpow_nonneg.
        rewrite two_pow_nat_succ.
        reflexivity.
      * rewrite Hresult'.
        rewrite square_pow by exact Hshr_nonneg.
        rewrite Hoddexp.
        replace (2 * to_Z (shr word_exp 1) + 0) with
          (2 * to_Z (shr word_exp 1)) by lia.
        reflexivity.
Qed.

Lemma two_pow_ge_256_mod_modulus256 : forall e,
  256 <= e ->
  2 ^ e mod modulus256 = 0.
Proof.
  intros e He.
  assert (Hmod : modulus256 = 2 ^ 256).
  { unfold modulus256, modulus_words, WL.modulus_words, base.
    rewrite width_is_64.
    change (Z.pow_pos (2 ^ 64) 4) with ((2 ^ 64) ^ 4).
    replace 256 with (64 * 4) by lia.
    rewrite <- Z.pow_mul_r by lia.
    reflexivity. }
  rewrite Hmod.
  replace e with (256 + (e - 256)) by lia.
  rewrite Z.pow_add_r by lia.
  rewrite Z.mul_comm.
  rewrite Z.mod_mul by (apply Z.pow_nonzero; lia).
  reflexivity.
Qed.
Lemma exp_words_loop_correct_4 :
  forall exponent base result b r,
    length base = 4%nat ->
    length result = 4%nat ->
    to_Z_words base = b mod modulus256 ->
    to_Z_words result = r mod modulus256 ->
    length (exp_words_loop 4 exponent base result) = 4%nat /\
    to_Z_words (exp_words_loop 4 exponent base result) =
      (r * b ^ to_Z_words exponent) mod modulus256.
Proof.
  induction exponent as [|word_exp rest IH];
    intros base result b r Hbase_len Hresult_len Hbase Hresult.
  - simpl. split.
    + exact Hresult_len.
    + cbn [WL.to_Z_words].
      rewrite Z.mul_1_r. exact Hresult.  - destruct rest as [|word_exp' rest'].
    + simpl.
      set (bits := (word_width - countl_zero word_exp)%nat).
      destruct (exp_sigbit_loop 4 bits word_exp base result)
        as [base' result'] eqn:Hloop.
      assert (Hbound : to_Z word_exp < 2 ^ Z.of_nat bits).
      { subst bits. apply DP.countl_zero_upper. }
      pose proof (exp_sigbit_loop_correct_4 bits word_exp base result
        b r Hbase_len Hresult_len Hbase Hresult Hbound) as Hsig.
      rewrite Hloop in Hsig.
      cbn in Hsig.
      destruct Hsig as [Hbase'_len [Hresult'_len [Hbase' Hresult']]].
      split.
      * exact Hresult'_len.
      * rewrite Hresult'.
        cbn [WL.to_Z_words].
        rewrite Z.mul_0_r, Z.add_0_r.
        reflexivity.
    + simpl.
      set (bits := word_width).
      destruct (exp_sigbit_loop 4 bits word_exp base result)
        as [base' result'] eqn:Hloop.
      assert (Hbound : to_Z word_exp < 2 ^ Z.of_nat bits).
      { subst bits.
        pose proof (spec_to_Z word_exp) as Hword.
        assert (Hbase64 : DoubleType.base width = 2 ^ 64).
        { unfold DoubleType.base. rewrite width_is_64. reflexivity. }
        rewrite Hbase64 in Hword.
        unfold word_width. rewrite width_is_64. simpl.
        lia. }
      pose proof (exp_sigbit_loop_correct_4 bits word_exp base result
        b r Hbase_len Hresult_len Hbase Hresult Hbound) as Hsig.
      rewrite Hloop in Hsig.
      cbn in Hsig.
      destruct Hsig as [Hbase'_len [Hresult'_len [Hbase' Hresult']]].
      specialize (IH base' result'
        (b ^ (2 ^ Z.of_nat bits))
        (r * b ^ to_Z word_exp)
        Hbase'_len Hresult'_len Hbase' Hresult').
      destruct IH as [Hlen Hval].
      split.
      * exact Hlen.
      * unfold bits in Hval |- *.
        cbn [exp_words_loop] in Hval |- *.
        rewrite Hval.
        assert (Hbase64 : DoubleType.base WL.U64.width = 2 ^ 64).
        { unfold DoubleType.base. rewrite width_is_64. reflexivity. }
        rewrite Hbase64.
        unfold word_width.
        rewrite width_is_64.
        change (Z.of_nat (Pos.to_nat 64)) with 64.
        replace
          (WL.U64.to_Z word_exp +
             2 ^ 64 * (WL.U64.to_Z word_exp' + 2 ^ 64 * to_Z_words rest'))
          with
          (WL.U64.to_Z word_exp + 2 ^ 64 * to_Z_words (word_exp' :: rest'))
          by (cbn [WL.to_Z_words]; rewrite Hbase64; reflexivity).
        pose proof (spec_to_Z word_exp) as Hword.
        pose proof (WL.to_Z_words_bound (word_exp' :: rest')) as Htail.
        replace
          ((b ^ (2 ^ 64)) ^ to_Z_words (word_exp' :: rest'))
          with
          (b ^ (2 ^ 64 * to_Z_words (word_exp' :: rest')))
          by (rewrite <- Z.pow_mul_r by (destruct Htail; lia); reflexivity).
        replace
          (r * b ^ to_Z word_exp *
             b ^ (2 ^ 64 * to_Z_words (word_exp' :: rest')))
          with
          (r * (b ^ to_Z word_exp *
             b ^ (2 ^ 64 * to_Z_words (word_exp' :: rest'))))
          by ring.
        rewrite <- Z.pow_add_r by (destruct Hword; destruct Htail; lia).
        reflexivity.
Qed.

Theorem exp_correct : forall base exponent,
  to_Z_uint256 (exp base exponent) =
    Z.pow (to_Z_uint256 base) (to_Z_uint256 exponent) mod modulus256.
Proof.
  intros base exponent.
  unfold exp.
  destruct (is_two_uint256 base) eqn:Htwo.
  - pose proof (is_two_uint256_true base Htwo) as Hbase2.
    rewrite shift_left_uint256_correct.
    rewrite to_Z_one_uint256.
    rewrite Hbase2.
    set (e := to_Z_uint256 exponent).
    destruct (Z.ltb e (DoubleType.base width)) eqn:Hltbase.
    + destruct (Z.ltb e 256) eqn:Hlt256.
      * rewrite Z.mul_1_l. reflexivity.
      * apply Z.ltb_ge in Hlt256.
        rewrite two_pow_ge_256_mod_modulus256 by exact Hlt256.
        reflexivity.
    + apply Z.ltb_ge in Hltbase.
      rewrite two_pow_ge_256_mod_modulus256.
      * reflexivity.
      * unfold e in Hltbase |- *.
        unfold DoubleType.base in Hltbase |- *.
        rewrite width_is_64 in Hltbase.
        simpl in Hltbase.
        lia.
  - remember (count_significant_words (uint256_to_words exponent))
      as sig_words eqn:Hsig_words.
    set (res :=
      exp_words_loop 4
        (firstn sig_words (uint256_to_words exponent))
        (uint256_to_words base)
        (one_words_generic 4)).
    assert (Hone_len : length (one_words_generic 4) = 4%nat).
    { unfold one_words_generic.
      rewrite WL.set_word_length, WL.extend_words_length.
      reflexivity. }
    assert (Hbase_mod :
      to_Z_words (uint256_to_words base) =
      to_Z_uint256 base mod modulus256).
    { unfold to_Z_uint256.
      rewrite Z.mod_small by apply to_Z_uint256_bounds.
      reflexivity. }
    assert (Hone_mod :
      to_Z_words (one_words_generic 4) = 1 mod modulus256).
    { rewrite to_Z_words_one_words_generic_4.
      rewrite Z.mod_small.
      2:{ split.
          - lia.
          - unfold modulus256, modulus_words, WL.modulus_words, DoubleType.base.
            rewrite width_is_64. simpl. lia. }
      reflexivity. }
    pose proof (exp_words_loop_correct_4
      (firstn sig_words (uint256_to_words exponent))
      (uint256_to_words base) (one_words_generic 4)
      (to_Z_uint256 base) 1
      (uint256_to_words_length base) Hone_len Hbase_mod Hone_mod)
      as Hloop.
    destruct Hloop as [Hres_len Hres_val].
    assert (Hres_bound : 0 <= to_Z_words res < modulus256).
    { unfold res.
      pose proof (WL.to_Z_words_bound
        (exp_words_loop 4
           (firstn sig_words (uint256_to_words exponent))
           (uint256_to_words base)
           (one_words_generic 4))) as Hbound.
      rewrite Hres_len in Hbound.
      change (WL.modulus_words 4) with modulus256 in Hbound.
      exact Hbound. }
    rewrite (to_Z_uint256_words_to_uint256_small res Hres_bound).
    unfold res.
    rewrite Hres_val.
    subst sig_words.
    rewrite DP.count_significant_words_preserves_value.
    unfold to_Z_uint256 at 2.
    rewrite Z.mul_1_l.
    reflexivity.
Qed.


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
