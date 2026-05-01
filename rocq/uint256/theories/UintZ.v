(** * Concrete Z-based Uint64 and Uint128 Models

    Consistency witness: instantiating the abstract [Uint64], [Uint128],
    and [UintWiden] signatures with concrete Z-based definitions proves
    the axiom set is satisfiable.

    [t := Z], [to_Z x := x mod 2^width].  All operations are defined
    via Z arithmetic and all specs follow from standard library lemmas.

    This file is not performance-relevant — it exists solely to audit
    that the axioms used in RuntimeMulProofs.v, DivisionProofs.v, and
    BarrettProofs.v do not introduce unsoundness. *)

From Stdlib Require Import ZArith PArith Bool Lia List.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint RuntimeMulProofs DivisionProofs.
From Uint256 Require Import Arithmetic Barrett BarrettProofs.

#[local] Open Scope Z_scope.

(** * Shared helpers *)

Definition wB (w : positive) : Z := base w.

Lemma wB_pos : forall w, 0 < wB w.
Proof. intro w. unfold wB, base. apply Z.pow_pos_nonneg; lia. Qed.

Lemma wB_ge_2 : forall w, (2 <= Pos.to_nat w)%nat -> 2 <= wB w.
Proof.
  intros w Hw. unfold wB, base. change 2 with (2 ^ 1).
  apply Z.pow_le_mono_r; lia.
Qed.

(** Normalize into [0, 2^width) *)
Definition norm (w : positive) (z : Z) : Z := z mod wB w.

Lemma norm_range : forall w z, 0 <= norm w z < wB w.
Proof. intros. apply Z.mod_pos_bound. apply wB_pos. Qed.

Lemma norm_mod : forall w x, norm w (norm w x) = norm w x.
Proof.
  intros. unfold norm.
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma norm_small : forall w x, 0 <= x < wB w -> norm w x = x.
Proof. intros. unfold norm. apply Z.mod_small. assumption. Qed.

Lemma wB_square_double : forall w,
  wB (2 * w)%positive = wB w * wB w.
Proof.
  intro w. unfold wB, base.
  rewrite Pos2Z.inj_mul.
  change (Z.pos 2%positive) with 2.
  replace (2 * Z.pos w) with (Z.pos w + Z.pos w) by lia.
  rewrite Z.pow_add_r by lia.
  ring.
Qed.

Lemma div_mod_decompose : forall z m, 0 < m ->
  z / m * m + z mod m = z.
Proof.
  intros z m Hm.
  replace (z / m * m) with (m * (z / m)) by ring.
  symmetry. apply Z.div_mod. lia.
Qed.

Lemma div_in_range : forall z d q,
  0 <= z < d * q ->
  0 < d ->
  0 <= z / d < q.
Proof.
  intros z d q [Hz0 Hzq] Hd. split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

Lemma mod_square_mod : forall z m, 0 < m ->
  (z mod (m * m)) mod m = z mod m.
Proof.
  intros z m Hm.
  rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm.
  rewrite Z.mod_add by lia.
  rewrite Z.mod_mod by lia.
  reflexivity.
Qed.

Lemma div_mod_square : forall z m, 0 < m ->
  (z / m) mod m = (z mod (m * m)) / m.
Proof.
  intros z m Hm.
  rewrite Z.rem_mul_r by lia.
  replace (z mod m + m * ((z / m) mod m))
    with (((z / m) mod m) * m + z mod m) by ring.
  rewrite Z.div_add_l by lia.
  replace (z mod m / m) with 0.
  - lia.
  - symmetry. apply Z.div_small.
    apply Z.mod_pos_bound. lia.
Qed.

(** * Concrete Uint64 Module *)

Module ZUint64.

  Definition t := Z.
  Definition width := 64%positive.
  Lemma width_is_64 : width = 64%positive.
  Proof. reflexivity. Qed.

  Definition to_Z (x : t) : Z := norm width x.

  (** Constants *)
  Definition zero : t := 0.
  Definition one : t := 1.

  (** Wrapping arithmetic *)
  Definition add (x y : t) : t := x + y.
  Definition sub (x y : t) : t := x - y.
  Definition mul (x y : t) : t := x * y.

  (** Double-width division *)
  Definition div (u_hi u_lo v : t) : option (t * t) :=
    let hi := norm width u_hi in
    let lo := norm width u_lo in
    let d  := norm width v in
    if d =? 0 then None
    else if hi >=? d then None
    else let dividend := hi * wB width + lo in
         Some (dividend / d, dividend mod d).

  (** Shifts *)
  Definition shl (x : t) (n : nat) : t := Z.shiftl x (Z.of_nat n).
  Definition shr (x : t) (n : nat) : t :=
    Z.shiftr (norm width x) (Z.of_nat n).
  Definition asr (x : t) (n : nat) : t :=
    let v := norm width x in
    Z.shiftr (v - (if v <? wB width / 2 then 0 else wB width))
             (Z.of_nat n).

  Definition land (x y : t) : t := Z.land x y.

  (** Bitwise OR *)
  Definition or (x y : t) : t := Z.lor x y.

  (** Comparison *)
  Definition eqb (x y : t) : bool := (norm width x =? norm width y).
  Definition ltb (x y : t) : bool := (norm width x <? norm width y).
  Definition leb (x y : t) : bool := (norm width x <=? norm width y).
  Definition gtb (x y : t) : bool := (norm width x >? norm width y).

  (** Bool injection *)
  Definition of_bool (b : bool) : t := if b then 1 else 0.

  (** Multi-precision primitives *)

  Definition mulx (x y : t) : t * t :=
    let p := norm width x * norm width y in
    (p / wB width, p mod wB width).

  Definition adc_2_short (x1 x0 y0 : t) : t * t :=
    let s := norm width x1 * wB width + norm width x0 + norm width y0 in
    let r := s mod (wB width * wB width) in
    (r / wB width, r mod wB width).

  Definition adc_2_full (x1 x0 y1 y0 : t) : t * t :=
    let s := norm width x1 * wB width + norm width x0
           + norm width y1 * wB width + norm width y0 in
    let r := s mod (wB width * wB width) in
    (r / wB width, r mod wB width).

  Definition adc_3 (x2 x1 x0 y1 y0 : t) : t * t * t :=
    let s := norm width x2 * wB width * wB width
           + norm width x1 * wB width + norm width x0
           + norm width y1 * wB width + norm width y0 in
    let r2 := s / (wB width * wB width) in
    let rem := s mod (wB width * wB width) in
    (r2, rem / wB width, rem mod wB width).

  (** ** Specs to prove *)

  Lemma spec_to_Z : forall x, 0 <= to_Z x < base width.
  Proof. intro x. apply norm_range. Qed.

  Lemma spec_zero : to_Z zero = 0.
  Proof. reflexivity. Qed.

  Lemma spec_one : to_Z one = 1.
  Proof. reflexivity. Qed.

  Lemma spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, add, norm.
    rewrite Zplus_mod. reflexivity.
  Qed.

  Lemma spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, sub, norm.
    rewrite Zminus_mod. reflexivity.
  Qed.

  Lemma spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, mul, norm.
    rewrite Zmult_mod. reflexivity.
  Qed.

  Lemma spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.
  Proof.
    intros u_hi u_lo v Hv Hhi.
    unfold div, to_Z in *.
    set (hi := norm width u_hi).
    set (lo := norm width u_lo).
    set (d := norm width v).
    assert (Hhi_range : 0 <= hi < wB width).
    { subst hi. apply norm_range. }
    assert (Hlo_range : 0 <= lo < wB width).
    { subst lo. apply norm_range. }
    assert (Hd_range : 0 <= d < wB width).
    { subst d. apply norm_range. }
    assert (Hd : 0 < d) by lia.
    destruct (d =? 0) eqn:Hd0.
    - apply Z.eqb_eq in Hd0. lia.
    - destruct (hi >=? d) eqn:Hhid.
      + apply Z.geb_le in Hhid. lia.
      + set (dividend := hi * wB width + lo).
        assert (Hdividend : 0 <= dividend < d * wB width).
        { subst dividend. nia. }
        assert (Hq_range : 0 <= dividend / d < wB width).
        { apply div_in_range; lia. }
        assert (Hr_range : 0 <= dividend mod d < d).
        { apply Z.mod_pos_bound. lia. }
        assert (Hr_small : 0 <= dividend mod d < wB width).
        { split.
          - lia.
          - eapply Z.lt_trans.
            + exact (proj2 Hr_range).
            + exact (proj2 Hd_range). }
        exists (dividend / d), (dividend mod d).
        split.
        * reflexivity.
        * split.
          -- rewrite (norm_small _ _ Hq_range).
             rewrite (norm_small _ _ Hr_small).
             subst dividend. symmetry. apply div_mod_decompose. lia.
          -- rewrite (norm_small _ _ Hr_small).
             exact Hr_range.
  Qed.

  Lemma spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.
  Proof.
    intros u_hi u_lo v H.
    unfold div, to_Z in *.
    destruct (norm width v =? 0) eqn:Hd0.
    - reflexivity.
    - destruct H as [H0|Hhi].
      + apply Z.eqb_neq in Hd0. contradiction.
      + assert (Hcmp : (norm width u_hi >=? norm width v) = true).
        { apply Z.geb_le. lia. }
        rewrite Hcmp. reflexivity.
  Qed.

  Lemma spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros. unfold to_Z, shl, norm.
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite Zmult_mod_idemp_l. reflexivity.
  Qed.

  Lemma spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros. unfold to_Z, shr. reflexivity.
  Qed.

  Lemma spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x - (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.
  Proof.
    intros. unfold to_Z, asr, norm. reflexivity.
  Qed.

  Lemma spec_land : forall x y,
    to_Z (land x y) = Z.land (to_Z x) (to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, land, norm, wB, base.
    apply Z.bits_inj'. intros n Hn.
    destruct (Z_lt_ge_dec n (Z.pos width)).
    - rewrite !Z.mod_pow2_bits_low by lia.
      rewrite !Z.land_spec.
      rewrite !Z.mod_pow2_bits_low by lia.
      reflexivity.
    - rewrite !Z.mod_pow2_bits_high by lia.
      reflexivity.
  Qed.

  Lemma spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, or, norm.
    unfold wB, base.
    rewrite <- (Z.land_ones (Z.lor x y) (Z.pos width)) by lia.
    rewrite <- (Z.land_ones (Z.lor (x mod 2 ^ Z.pos width)
                                   (y mod 2 ^ Z.pos width))
                            (Z.pos width)) by lia.
    rewrite !Z.land_lor_distr_l.
    rewrite !Z.land_ones by lia.
    rewrite !Z.mod_mod by lia.
    reflexivity.
  Qed.

  Lemma spec_eqb : forall x y, eqb x y = (to_Z x =? to_Z y).
  Proof. reflexivity. Qed.

  Lemma spec_ltb : forall x y, ltb x y = (to_Z x <? to_Z y).
  Proof. reflexivity. Qed.

  Lemma spec_leb : forall x y, leb x y = (to_Z x <=? to_Z y).
  Proof. reflexivity. Qed.

  Lemma spec_gtb : forall x y, gtb x y = (to_Z x >? to_Z y).
  Proof. reflexivity. Qed.

  Lemma spec_of_bool : forall b, to_Z (of_bool b) = if b then 1 else 0.
  Proof. destruct b; reflexivity. Qed.

  Lemma spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.
  Proof.
    intros x y. unfold mulx, to_Z.
    set (m := wB width).
    set (p := norm width x * norm width y).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hp : 0 <= p < m * m).
    { subst p m. pose proof (norm_range width x). pose proof (norm_range width y).
      nia. }
    assert (Hhi : 0 <= p / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= p mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (p / m * m + p mod m = p).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.
  Proof.
    intros x1 x0 y0 Hx1. unfold adc_2_short, to_Z in *.
    set (m := wB width).
    set (s := norm width x1 * m + norm width x0 + norm width y0).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hs : 0 <= s < m * m).
    { change (base width) with (wB width) in Hx1.
      subst s m.
      pose proof (norm_range width x1).
      pose proof (norm_range width x0).
      pose proof (norm_range width y0).
      nia. }
    rewrite Z.mod_small by exact Hs.
    assert (Hhi : 0 <= s / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= s mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (s / m * m + s mod m = s).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_2_short_mod : forall x1 x0 y0,
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 + to_Z y0)
        mod (base width * base width).
  Proof.
    intros x1 x0 y0. unfold adc_2_short, to_Z.
    set (m := wB width).
    set (s := norm width x1 * m + norm width x0 + norm width y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).
  Proof.
    intros x1 x0 y1 y0. unfold adc_2_full, to_Z.
    set (m := wB width).
    set (s := norm width x1 * m + norm width x0
            + norm width y1 * m + norm width y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.
  Proof.
    intros x2 x1 x0 y1 y0 Hx2. unfold adc_3, to_Z in *.
    set (m := wB width).
    set (s := norm width x2 * m * m
            + norm width x1 * m + norm width x0
            + norm width y1 * m + norm width y0).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hs : 0 <= s < (m * m) * m).
    { change (base width) with (wB width) in Hx2.
      subst s m.
      pose proof (norm_range width x2).
      pose proof (norm_range width x1).
      pose proof (norm_range width x0).
      pose proof (norm_range width y1).
      pose proof (norm_range width y0).
      nia. }
    assert (H2 : 0 <= s / (m * m) < m).
    { apply div_in_range; lia. }
    assert (Hrem : 0 <= s mod (m * m) < m * m).
    { apply Z.mod_pos_bound. lia. }
    assert (H1 : 0 <= s mod (m * m) / m < m).
    { apply div_in_range; lia. }
    assert (H0 : 0 <= s mod (m * m) mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ H2).
    rewrite (norm_small _ _ H1).
    rewrite (norm_small _ _ H0).
    change (base width) with m.
    change (base width * base width) with (wB width * wB width).
    replace (s / (m * m) * m * m + s mod (m * m) / m * m +
             s mod (m * m) mod m)
      with (s / (m * m) * (m * m) +
            (s mod (m * m) / m * m + s mod (m * m) mod m)) by ring.
    replace (s / (m * m) * (m * m) +
             (s mod (m * m) / m * m + s mod (m * m) mod m))
      with (s / (m * m) * (m * m) + s mod (m * m)).
    2:{ rewrite (div_mod_decompose (s mod (m * m)) m Hm). reflexivity. }
    change (s / (m * m) * (m * m) + s mod (m * m) = s).
    apply div_mod_decompose. lia.
  Qed.

End ZUint64.

(** * Concrete Uint128 Module *)

Module ZUint128.

  Definition t := Z.
  Definition width := 128%positive.
  Lemma width_is_128 : width = 128%positive.
  Proof. reflexivity. Qed.

  Definition to_Z (x : t) : Z := norm width x.
  Definition zero : t := 0.
  Definition one : t := 1.
  Definition add (x y : t) : t := x + y.
  Definition sub (x y : t) : t := x - y.
  Definition mul (x y : t) : t := x * y.

  Definition div (u_hi u_lo v : t) : option (t * t) :=
    let hi := norm width u_hi in
    let lo := norm width u_lo in
    let d  := norm width v in
    if d =? 0 then None
    else if hi >=? d then None
    else let dividend := hi * wB width + lo in
         Some (dividend / d, dividend mod d).

  Definition shl (x : t) (n : nat) : t := Z.shiftl x (Z.of_nat n).
  Definition shr (x : t) (n : nat) : t :=
    Z.shiftr (norm width x) (Z.of_nat n).
  Definition asr (x : t) (n : nat) : t :=
    let v := norm width x in
    Z.shiftr (v - (if v <? wB width / 2 then 0 else wB width))
             (Z.of_nat n).
  Definition land (x y : t) : t := Z.land x y.
  Definition or (x y : t) : t := Z.lor x y.
  Definition eqb (x y : t) : bool := (norm width x =? norm width y).
  Definition ltb (x y : t) : bool := (norm width x <? norm width y).
  Definition leb (x y : t) : bool := (norm width x <=? norm width y).
  Definition gtb (x y : t) : bool := (norm width x >? norm width y).
  Definition of_bool (b : bool) : t := if b then 1 else 0.

  Definition mulx (x y : t) : t * t :=
    let p := norm width x * norm width y in
    (p / wB width, p mod wB width).

  Definition adc_2_short (x1 x0 y0 : t) : t * t :=
    let s := norm width x1 * wB width + norm width x0 + norm width y0 in
    let r := s mod (wB width * wB width) in
    (r / wB width, r mod wB width).

  Definition adc_2_full (x1 x0 y1 y0 : t) : t * t :=
    let s := norm width x1 * wB width + norm width x0
           + norm width y1 * wB width + norm width y0 in
    let r := s mod (wB width * wB width) in
    (r / wB width, r mod wB width).

  Definition adc_3 (x2 x1 x0 y1 y0 : t) : t * t * t :=
    let s := norm width x2 * wB width * wB width
           + norm width x1 * wB width + norm width x0
           + norm width y1 * wB width + norm width y0 in
    let r2 := s / (wB width * wB width) in
    let rem := s mod (wB width * wB width) in
    (r2, rem / wB width, rem mod wB width).

  (** All specs — same structure as ZUint64, width = 128 *)

  Lemma spec_to_Z : forall x, 0 <= to_Z x < base width.
  Proof. intro x. apply norm_range. Qed.

  Lemma spec_zero : to_Z zero = 0. Proof. reflexivity. Qed.
  Lemma spec_one : to_Z one = 1. Proof. reflexivity. Qed.
  Lemma spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, add, norm.
    rewrite Zplus_mod. reflexivity.
  Qed.

  Lemma spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, sub, norm.
    rewrite Zminus_mod. reflexivity.
  Qed.

  Lemma spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, mul, norm.
    rewrite Zmult_mod. reflexivity.
  Qed.

  Lemma spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.
  Proof.
    intros u_hi u_lo v Hv Hhi.
    unfold div, to_Z in *.
    set (hi := norm width u_hi).
    set (lo := norm width u_lo).
    set (d := norm width v).
    assert (Hhi_range : 0 <= hi < wB width).
    { subst hi. apply norm_range. }
    assert (Hlo_range : 0 <= lo < wB width).
    { subst lo. apply norm_range. }
    assert (Hd_range : 0 <= d < wB width).
    { subst d. apply norm_range. }
    assert (Hd : 0 < d) by lia.
    destruct (d =? 0) eqn:Hd0.
    - apply Z.eqb_eq in Hd0. lia.
    - destruct (hi >=? d) eqn:Hhid.
      + apply Z.geb_le in Hhid. lia.
      + set (dividend := hi * wB width + lo).
        assert (Hdividend : 0 <= dividend < d * wB width).
        { subst dividend. nia. }
        assert (Hq_range : 0 <= dividend / d < wB width).
        { apply div_in_range; lia. }
        assert (Hr_range : 0 <= dividend mod d < d).
        { apply Z.mod_pos_bound. lia. }
        assert (Hr_small : 0 <= dividend mod d < wB width).
        { split.
          - lia.
          - eapply Z.lt_trans.
            + exact (proj2 Hr_range).
            + exact (proj2 Hd_range). }
        exists (dividend / d), (dividend mod d).
        split.
        * reflexivity.
        * split.
          -- rewrite (norm_small _ _ Hq_range).
             rewrite (norm_small _ _ Hr_small).
             subst dividend. symmetry. apply div_mod_decompose. lia.
          -- rewrite (norm_small _ _ Hr_small).
             exact Hr_range.
  Qed.

  Lemma spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.
  Proof.
    intros u_hi u_lo v H.
    unfold div, to_Z in *.
    destruct (norm width v =? 0) eqn:Hd0.
    - reflexivity.
    - destruct H as [H0|Hhi].
      + apply Z.eqb_neq in Hd0. contradiction.
      + assert (Hcmp : (norm width u_hi >=? norm width v) = true).
        { apply Z.geb_le. lia. }
        rewrite Hcmp. reflexivity.
  Qed.

  Lemma spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros. unfold to_Z, shl, norm.
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite Zmult_mod_idemp_l. reflexivity.
  Qed.

  Lemma spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros. unfold to_Z, shr. reflexivity.
  Qed.

  Lemma spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x -
                (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.
  Proof.
    intros. unfold to_Z, asr, norm. reflexivity.
  Qed.

  Lemma spec_land : forall x y,
    to_Z (land x y) = Z.land (to_Z x) (to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, land, norm, wB, base.
    apply Z.bits_inj'. intros n Hn.
    destruct (Z_lt_ge_dec n (Z.pos width)).
    - rewrite !Z.mod_pow2_bits_low by lia.
      rewrite !Z.land_spec.
      rewrite !Z.mod_pow2_bits_low by lia.
      reflexivity.
    - rewrite !Z.mod_pow2_bits_high by lia.
      reflexivity.
  Qed.

  Lemma spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.
  Proof.
    intros. unfold to_Z, or, norm.
    unfold wB, base.
    rewrite <- (Z.land_ones (Z.lor x y) (Z.pos width)) by lia.
    rewrite <- (Z.land_ones (Z.lor (x mod 2 ^ Z.pos width)
                                   (y mod 2 ^ Z.pos width))
                            (Z.pos width)) by lia.
    rewrite !Z.land_lor_distr_l.
    rewrite !Z.land_ones by lia.
    rewrite !Z.mod_mod by lia.
    reflexivity.
  Qed.
  Lemma spec_eqb : forall x y, eqb x y = (to_Z x =? to_Z y). Proof. reflexivity. Qed.
  Lemma spec_ltb : forall x y, ltb x y = (to_Z x <? to_Z y). Proof. reflexivity. Qed.
  Lemma spec_leb : forall x y, leb x y = (to_Z x <=? to_Z y). Proof. reflexivity. Qed.
  Lemma spec_gtb : forall x y, gtb x y = (to_Z x >? to_Z y). Proof. reflexivity. Qed.
  Lemma spec_of_bool : forall b, to_Z (of_bool b) = if b then 1 else 0. Proof. destruct b; reflexivity. Qed.
  Lemma spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.
  Proof.
    intros x y. unfold mulx, to_Z.
    set (m := wB width).
    set (p := norm width x * norm width y).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hp : 0 <= p < m * m).
    { subst p m. pose proof (norm_range width x). pose proof (norm_range width y).
      nia. }
    assert (Hhi : 0 <= p / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= p mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (p / m * m + p mod m = p).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.
  Proof.
    intros x1 x0 y0 Hx1. unfold adc_2_short, to_Z in *.
    set (m := wB width).
    set (s := norm width x1 * m + norm width x0 + norm width y0).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hs : 0 <= s < m * m).
    { change (base width) with (wB width) in Hx1.
      subst s m.
      pose proof (norm_range width x1).
      pose proof (norm_range width x0).
      pose proof (norm_range width y0).
      nia. }
    rewrite Z.mod_small by exact Hs.
    assert (Hhi : 0 <= s / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= s mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (s / m * m + s mod m = s).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_2_short_mod : forall x1 x0 y0,
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 + to_Z y0)
        mod (base width * base width).
  Proof.
    intros x1 x0 y0. unfold adc_2_short, to_Z.
    set (m := wB width).
    set (s := norm width x1 * m + norm width x0 + norm width y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).
  Proof.
    intros x1 x0 y1 y0. unfold adc_2_full, to_Z.
    set (m := wB width).
    set (s := norm width x1 * m + norm width x0
            + norm width y1 * m + norm width y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ Hhi).
    rewrite (norm_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose. exact Hm.
  Qed.

  Lemma spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.
  Proof.
    intros x2 x1 x0 y1 y0 Hx2. unfold adc_3, to_Z in *.
    set (m := wB width).
    set (s := norm width x2 * m * m
            + norm width x1 * m + norm width x0
            + norm width y1 * m + norm width y0).
    assert (Hm : 0 < m).
    { subst m. apply wB_pos. }
    assert (Hs : 0 <= s < (m * m) * m).
    { change (base width) with (wB width) in Hx2.
      subst s m.
      pose proof (norm_range width x2).
      pose proof (norm_range width x1).
      pose proof (norm_range width x0).
      pose proof (norm_range width y1).
      pose proof (norm_range width y0).
      nia. }
    assert (H2 : 0 <= s / (m * m) < m).
    { apply div_in_range; lia. }
    assert (Hrem : 0 <= s mod (m * m) < m * m).
    { apply Z.mod_pos_bound. lia. }
    assert (H1 : 0 <= s mod (m * m) / m < m).
    { apply div_in_range; lia. }
    assert (H0 : 0 <= s mod (m * m) mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (norm_small _ _ H2).
    rewrite (norm_small _ _ H1).
    rewrite (norm_small _ _ H0).
    change (base width) with m.
    change (base width * base width) with (wB width * wB width).
    replace (s / (m * m) * m * m + s mod (m * m) / m * m +
             s mod (m * m) mod m)
      with (s / (m * m) * (m * m) +
            (s mod (m * m) / m * m + s mod (m * m) mod m)) by ring.
    replace (s / (m * m) * (m * m) +
             (s mod (m * m) / m * m + s mod (m * m) mod m))
      with (s / (m * m) * (m * m) + s mod (m * m)).
    2:{ rewrite (div_mod_decompose (s mod (m * m)) m Hm). reflexivity. }
    change (s / (m * m) * (m * m) + s mod (m * m) = s).
    apply div_mod_decompose. lia.
  Qed.

End ZUint128.

(** * Concrete Widen Bridge *)

Module ZBridge.

  Lemma width_relation : ZUint128.width = (2 * ZUint64.width)%positive.
  Proof. reflexivity. Qed.

  Definition widen (x : ZUint64.t) : ZUint128.t :=
    norm ZUint64.width x.
  Definition trunc (x : ZUint128.t) : ZUint64.t := x.
  Definition hi (x : ZUint128.t) : ZUint64.t := x / wB ZUint64.width.
  Definition combine (h l : ZUint64.t) : ZUint128.t :=
    norm ZUint64.width h * wB ZUint64.width + norm ZUint64.width l.

  Lemma wide_base_square :
    wB ZUint128.width = wB ZUint64.width * wB ZUint64.width.
  Proof.
    rewrite width_relation.
    apply wB_square_double.
  Qed.

  Lemma spec_widen : forall x,
    ZUint128.to_Z (widen x) = ZUint64.to_Z x.
  Proof.
    intro x.
    unfold ZUint128.to_Z, widen, ZUint64.to_Z, norm.
    rewrite wide_base_square.
    pose proof (ZUint64.spec_to_Z x) as Hx.
    change (base ZUint64.width) with (wB ZUint64.width) in Hx.
    pose proof (wB_pos ZUint64.width) as Hm.
    apply Z.mod_small.
    split.
    - exact (proj1 Hx).
    - eapply Z.lt_le_trans.
      + exact (proj2 Hx).
      + assert (H1 : 1 <= wB ZUint64.width) by lia.
        replace (wB ZUint64.width) with (wB ZUint64.width * 1) by ring.
        apply Z.mul_le_mono_nonneg_l; lia.
  Qed.

  Lemma spec_trunc : forall x,
    ZUint64.to_Z (trunc x) = ZUint128.to_Z x mod base ZUint64.width.
  Proof.
    intro x.
    unfold ZUint64.to_Z, trunc, ZUint128.to_Z, norm.
    rewrite wide_base_square.
    symmetry. apply mod_square_mod. apply wB_pos.
  Qed.

  Lemma spec_hi : forall x,
    ZUint64.to_Z (hi x) = ZUint128.to_Z x / base ZUint64.width.
  Proof.
    intro x.
    unfold ZUint64.to_Z, hi, ZUint128.to_Z, norm.
    rewrite wide_base_square.
    apply div_mod_square. apply wB_pos.
  Qed.

  Lemma spec_combine : forall h l,
    ZUint128.to_Z (combine h l) =
      ZUint64.to_Z h * base ZUint64.width + ZUint64.to_Z l.
  Proof.
    intros h l.
    unfold ZUint128.to_Z, combine, ZUint64.to_Z, norm.
    rewrite wide_base_square.
    change (base ZUint64.width) with (wB ZUint64.width).
    pose proof (ZUint64.spec_to_Z h) as Hh.
    change (0 <= h mod wB ZUint64.width < wB ZUint64.width) in Hh.
    pose proof (ZUint64.spec_to_Z l) as Hl.
    change (0 <= l mod wB ZUint64.width < wB ZUint64.width) in Hl.
    pose proof (wB_pos ZUint64.width) as Hm.
    destruct Hh as [Hh0 Hh1].
    destruct Hl as [Hl0 Hl1].
    apply Z.mod_small. split.
    - apply Z.add_nonneg_nonneg.
      + apply Z.mul_nonneg_nonneg.
        * exact Hh0.
        * apply Z.lt_le_incl. exact Hm.
      + exact Hl0.
    - eapply Z.lt_le_trans.
      + apply Z.add_lt_mono_l. exact Hl1.
      + replace (h mod wB ZUint64.width * wB ZUint64.width +
                  wB ZUint64.width)
          with ((h mod wB ZUint64.width + 1) * wB ZUint64.width) by ring.
        apply Z.mul_le_mono_nonneg_r.
        * apply Z.lt_le_incl. exact Hm.
        * lia.
  Qed.

End ZBridge.

(** * Instantiations — the consistency witnesses *)

(** RuntimeMul proofs with no axioms *)
Module RuntimeMulConsistency.
  Module B := Base.MakeProof(ZUint64).
  Module RM := RuntimeMul.MakeProof(B).
  Module WL := WordsLemmas.MakeProofs(B).
  Module P := RuntimeMulProofs.MakeProofs(B)(RM)(WL).
  Include P.
  (** This should print no assumptions once all Admitted above are filled *)
  Print Assumptions P.truncating_mul_runtime_correct.
End RuntimeMulConsistency.

(** Division proofs with no axioms *)
Module DivisionConsistency.
  Module B := Base.MakeProof(ZUint64).
  Module Div := Division.Make(B)(ZUint128)(ZBridge).
  Module WL := WordsLemmas.MakeProofs(B).
  Module P := DivisionProofs.MakeProofs(B)(ZUint128)(ZBridge)(Div)(WL).
  Include P.

  (** This should print no assumptions once all Admitted above are filled *)
  (* Print Assumptions P.<main_theorem>. *)
End DivisionConsistency.

(** Barrett proofs with no axioms *)
Module BarrettConsistency.
  Module B := Base.MakeProof(ZUint64).
  Module Div := Division.Make(B)(ZUint128)(ZBridge).
  Module RM := RuntimeMul.MakeProof(B).
  Module WL := WordsLemmas.MakeProofs(B).
  Module RMP := RuntimeMulProofs.MakeProofs(B)(RM)(WL).
  Module DP := DivisionProofs.MakeProofs(B)(ZUint128)(ZBridge)(Div)(WL).
  Module Arith := Arithmetic.Make(B)(ZUint128)(ZBridge)(Div)(RM).
  Module Bar := Barrett.Make(B)(ZUint128)(ZBridge)(Div)(RM)(Arith).
  Module P := BarrettProofs.MakeProofs(B)(ZUint128)(ZBridge)(WL)(Div)(DP)
    (RM)(RMP)(Arith)(Bar).
  Include P.

  Print Assumptions udivrem_correct.
  Print Assumptions signed_wrapper_correct.
  Print Assumptions addmod_correct.
  Print Assumptions mulmod_correct.
  Print Assumptions mulmod_const_correct.
  Print Assumptions udivrem_reciprocal_correct.
  Print Assumptions addmod_reciprocal_correct.
  Print Assumptions mulmod_reciprocal_correct.
  Print Assumptions mulmod_const_reciprocal_correct.
End BarrettConsistency.
