(** * Sigma-type Bounded Uint64 and Uint128 Models

    Alternative consistency witness: instantiating the abstract [Uint64],
    [Uint128], and [UintWiden] signatures with sigma-type based definitions
    where every inhabitant is intrinsically bounded.

    [t := { z : Z | 0 <= z < 2^width }], [to_Z x := proj1_sig x].
    The range invariant is enforced by the type, so [spec_to_Z] follows
    directly from the sigma proof.  Operations wrap via modular reduction
    using a [mk] smart constructor.

    This file mirrors UintZ.v but with a refined carrier type. *)

From Stdlib Require Import ZArith PArith Bool Lia List.
From Stdlib Require Import DoubleType.
From Uint256 Require Import Uint RuntimeMulProofs DivisionProofs.

#[local] Open Scope Z_scope.

(** * Shared helpers *)

(** The bounded type: integers in [0, 2^w) *)
Definition bounded (w : positive) := { z : Z | 0 <= z < base w }.

Lemma base_pos : forall w, 0 < base w.
Proof. intro w. unfold base. apply Z.pow_pos_nonneg; lia. Qed.

Lemma base_ge_2 : forall w, 2 <= base w.
Proof.
  intro w.
  unfold base.
  replace (Z.pos w) with (1 + (Z.pos w - 1)) by lia.
  rewrite Z.pow_add_r by lia.
  change (2 ^ 1) with 2.
  assert (0 < 2 ^ (Z.pos w - 1)).
  { apply Z.pow_pos_nonneg; lia. }
  lia.
Qed.

(** Smart constructor: wrap any Z into the bounded type via mod *)
Definition mk (w : positive) (z : Z) : bounded w :=
  exist _ (z mod base w) (Z.mod_pos_bound z (base w) (base_pos w)).

(** Projection to Z *)
Definition val {w : positive} (x : bounded w) : Z := proj1_sig x.

Lemma val_range : forall w (x : bounded w), 0 <= val x < base w.
Proof. intros w [z Hz]. exact Hz. Qed.

Lemma val_mk : forall w z, val (mk w z) = z mod base w.
Proof. reflexivity. Qed.

Lemma base_square_double : forall w,
  base (2 * w)%positive = base w * base w.
Proof.
  intro w. unfold base.
  rewrite Pos2Z.inj_mul.
  change (Z.pos 2%positive) with 2.
  replace (2 * Z.pos w) with (Z.pos w + Z.pos w) by lia.
  rewrite Z.pow_add_r by lia.
  ring.
Qed.

Lemma val_mk_small : forall w z, 0 <= z < base w -> val (mk w z) = z.
Proof.
  intros w z Hz.
  rewrite val_mk.
  apply Z.mod_small.
  exact Hz.
Qed.

Lemma div_mod_decompose : forall z m, 0 < m ->
  z / m * m + z mod m = z.
Proof.
  intros z m Hm.
  replace (z / m * m) with (m * (z / m)) by ring.
  symmetry.
  apply Z.div_mod.
  lia.
Qed.

Lemma div_in_range : forall z d q,
  0 <= z < d * q ->
  0 < d ->
  0 <= z / d < q.
Proof.
  intros z d q [Hz0 Hzq] Hd.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_lt_upper_bound; lia.
Qed.

(** * Concrete Uint64 Module *)

Module SigmaUint64.

  Definition width := 64%positive.
  Definition t := bounded width.

  Lemma width_is_64 : width = 64%positive.
  Proof. reflexivity. Qed.

  Definition to_Z (x : t) : Z := val x.

  (** Constants *)
  Definition zero : t := mk width 0.
  Definition one  : t := mk width 1.

  (** Wrapping arithmetic *)
  Definition add (x y : t) : t := mk width (val x + val y).
  Definition sub (x y : t) : t := mk width (val x - val y).
  Definition mul (x y : t) : t := mk width (val x * val y).

  (** Double-width division *)
  Definition div (u_hi u_lo v : t) : option (t * t) :=
    let hi := val u_hi in
    let lo := val u_lo in
    let d  := val v in
    if d =? 0 then None
    else if hi >=? d then None
    else let dividend := hi * base width + lo in
         Some (mk width (dividend / d), mk width (dividend mod d)).

  (** Shifts *)
  Definition shl (x : t) (n : nat) : t :=
    mk width (Z.shiftl (val x) (Z.of_nat n)).
  Definition shr (x : t) (n : nat) : t :=
    mk width (Z.shiftr (val x) (Z.of_nat n)).
  Definition asr (x : t) (n : nat) : t :=
    let v := val x in
    mk width (Z.shiftr (v - (if v <? base width / 2 then 0 else base width))
                       (Z.of_nat n)).

  (** Bitwise OR *)
  Definition or (x y : t) : t := mk width (Z.lor (val x) (val y)).

  (** Comparison *)
  Definition eqb (x y : t) : bool := (val x =? val y).
  Definition ltb (x y : t) : bool := (val x <? val y).
  Definition leb (x y : t) : bool := (val x <=? val y).
  Definition gtb (x y : t) : bool := (val x >? val y).

  (** Bool injection *)
  Definition of_bool (b : bool) : t := mk width (if b then 1 else 0).

  (** Multi-precision primitives *)

  Definition mulx (x y : t) : t * t :=
    let p := val x * val y in
    (mk width (p / base width), mk width (p mod base width)).

  Definition adc_2_short (x1 x0 y0 : t) : t * t :=
    let s := val x1 * base width + val x0 + val y0 in
    let r := s mod (base width * base width) in
    (mk width (r / base width), mk width (r mod base width)).

  Definition adc_2_full (x1 x0 y1 y0 : t) : t * t :=
    let s := val x1 * base width + val x0
           + val y1 * base width + val y0 in
    let r := s mod (base width * base width) in
    (mk width (r / base width), mk width (r mod base width)).

  Definition adc_3 (x2 x1 x0 y1 y0 : t) : t * t * t :=
    let s := val x2 * base width * base width
           + val x1 * base width + val x0
           + val y1 * base width + val y0 in
    let r2 := s / (base width * base width) in
    let rem := s mod (base width * base width) in
    (mk width r2, mk width (rem / base width), mk width (rem mod base width)).

  (** ** Specs *)

  Lemma spec_to_Z : forall x, 0 <= to_Z x < base width.
  Proof. exact (val_range width). Qed.

  Lemma spec_zero : to_Z zero = 0.
  Proof.
    unfold zero, to_Z.
    apply val_mk_small.
    split; [lia|apply base_pos].
  Qed.

  Lemma spec_one : to_Z one = 1.
  Proof.
    unfold one, to_Z.
    apply val_mk_small.
    split.
    - lia.
    - pose proof (base_ge_2 width). lia.
  Qed.

  Lemma spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Proof.
    intros x y.
    unfold add, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Proof.
    intros x y.
    unfold sub, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.
  Proof.
    intros x y.
    unfold mul, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.
  Proof.
    intros u_hi u_lo v Hv Hhi.
    unfold div, to_Z in *.
    set (hi := val u_hi).
    set (lo := val u_lo).
    set (d := val v).
    assert (Hhi_range : 0 <= hi < base width).
    { subst hi. apply val_range. }
    assert (Hlo_range : 0 <= lo < base width).
    { subst lo. apply val_range. }
    assert (Hd_range : 0 <= d < base width).
    { subst d. apply val_range. }
    assert (Hd : 0 < d) by lia.
    destruct (d =? 0) eqn:Hd0.
    - apply Z.eqb_eq in Hd0. lia.
    - destruct (hi >=? d) eqn:Hhid.
      + apply Z.geb_le in Hhid. lia.
      + set (dividend := hi * base width + lo).
        assert (Hdividend : 0 <= dividend < d * base width).
        { subst dividend. nia. }
        assert (Hq_range : 0 <= dividend / d < base width).
        { apply div_in_range; lia. }
        assert (Hr_range : 0 <= dividend mod d < d).
        { apply Z.mod_pos_bound. lia. }
        assert (Hr_small : 0 <= dividend mod d < base width).
        { split.
          - lia.
          - eapply Z.lt_trans.
            + exact (proj2 Hr_range).
            + exact (proj2 Hd_range). }
        exists (mk width (dividend / d)), (mk width (dividend mod d)).
        split.
        * reflexivity.
        * split.
          -- rewrite (val_mk_small _ _ Hq_range).
             rewrite (val_mk_small _ _ Hr_small).
             subst dividend.
             symmetry.
             apply div_mod_decompose.
             lia.
          -- rewrite (val_mk_small _ _ Hr_small).
             exact Hr_range.
  Qed.

  Lemma spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.
  Proof.
    intros u_hi u_lo v H.
    unfold div, to_Z in *.
    destruct (val v =? 0) eqn:Hd0.
    - reflexivity.
    - destruct H as [H0|Hhi].
      + apply Z.eqb_neq in Hd0. contradiction.
      + assert (Hcmp : (val u_hi >=? val v) = true).
        { apply Z.geb_le. lia. }
        rewrite Hcmp.
        reflexivity.
  Qed.

  Lemma spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros x n.
    unfold shl, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros x n.
    unfold shr, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x - (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.
  Proof.
    intros x n.
    unfold asr, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.
  Proof.
    intros x y.
    unfold or, to_Z.
    rewrite val_mk.
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
  Proof.
    destruct b.
    - apply spec_one.
    - apply spec_zero.
  Qed.

  Lemma spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.
  Proof.
    intros x y.
    unfold mulx, to_Z.
    set (m := base width).
    set (p := val x * val y).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hp : 0 <= p < m * m).
    { subst p m.
      pose proof (val_range width x).
      pose proof (val_range width y).
      nia. }
    assert (Hhi : 0 <= p / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= p mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (p / m * m + p mod m = p).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.
  Proof.
    intros x1 x0 y0 Hx1.
    unfold adc_2_short, to_Z in *.
    set (m := base width).
    set (s := val x1 * m + val x0 + val y0).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hs : 0 <= s < m * m).
    { subst s m.
      pose proof (val_range width x1).
      pose proof (val_range width x0).
      pose proof (val_range width y0).
      nia. }
    rewrite Z.mod_small by exact Hs.
    assert (Hhi : 0 <= s / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= s mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (s / m * m + s mod m = s).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_2_short_mod : forall x1 x0 y0,
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 + to_Z y0)
        mod (base width * base width).
  Proof.
    intros x1 x0 y0.
    unfold adc_2_short, to_Z.
    set (m := base width).
    set (s := val x1 * m + val x0 + val y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).
  Proof.
    intros x1 x0 y1 y0.
    unfold adc_2_full, to_Z.
    set (m := base width).
    set (s := val x1 * m + val x0 + val y1 * m + val y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.
  Proof.
    intros x2 x1 x0 y1 y0 Hx2.
    unfold adc_3, to_Z in *.
    set (m := base width).
    set (s := val x2 * m * m + val x1 * m + val x0 + val y1 * m + val y0).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hs : 0 <= s < (m * m) * m).
    { subst s m.
      pose proof (val_range width x2).
      pose proof (val_range width x1).
      pose proof (val_range width x0).
      pose proof (val_range width y1).
      pose proof (val_range width y0).
      nia. }
    assert (H2 : 0 <= s / (m * m) < m).
    { apply div_in_range; lia. }
    assert (Hrem : 0 <= s mod (m * m) < m * m).
    { apply Z.mod_pos_bound. lia. }
    assert (H1 : 0 <= s mod (m * m) / m < m).
    { apply div_in_range; lia. }
    assert (H0 : 0 <= s mod (m * m) mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ H2).
    rewrite (val_mk_small _ _ H1).
    rewrite (val_mk_small _ _ H0).
    change (base width) with m.
    change (base width * base width) with (m * m).
    replace (s / (m * m) * m * m + s mod (m * m) / m * m +
             s mod (m * m) mod m)
      with (s / (m * m) * (m * m) +
            (s mod (m * m) / m * m + s mod (m * m) mod m)) by ring.
    replace (s / (m * m) * (m * m) +
             (s mod (m * m) / m * m + s mod (m * m) mod m))
      with (s / (m * m) * (m * m) + s mod (m * m)).
    2:{ rewrite (div_mod_decompose (s mod (m * m)) m Hm). reflexivity. }
    change (s / (m * m) * (m * m) + s mod (m * m) = s).
    apply div_mod_decompose.
    lia.
  Qed.

End SigmaUint64.

(** * Concrete Uint128 Module *)

Module SigmaUint128.

  Definition width := 128%positive.
  Definition t := bounded width.

  Lemma width_is_128 : width = 128%positive.
  Proof. reflexivity. Qed.

  Definition to_Z (x : t) : Z := val x.

  Definition zero : t := mk width 0.
  Definition one  : t := mk width 1.

  Definition add (x y : t) : t := mk width (val x + val y).
  Definition sub (x y : t) : t := mk width (val x - val y).
  Definition mul (x y : t) : t := mk width (val x * val y).

  Definition div (u_hi u_lo v : t) : option (t * t) :=
    let hi := val u_hi in
    let lo := val u_lo in
    let d  := val v in
    if d =? 0 then None
    else if hi >=? d then None
    else let dividend := hi * base width + lo in
         Some (mk width (dividend / d), mk width (dividend mod d)).

  Definition shl (x : t) (n : nat) : t :=
    mk width (Z.shiftl (val x) (Z.of_nat n)).
  Definition shr (x : t) (n : nat) : t :=
    mk width (Z.shiftr (val x) (Z.of_nat n)).
  Definition asr (x : t) (n : nat) : t :=
    let v := val x in
    mk width (Z.shiftr (v - (if v <? base width / 2 then 0 else base width))
                       (Z.of_nat n)).

  Definition or (x y : t) : t := mk width (Z.lor (val x) (val y)).

  Definition eqb (x y : t) : bool := (val x =? val y).
  Definition ltb (x y : t) : bool := (val x <? val y).
  Definition leb (x y : t) : bool := (val x <=? val y).
  Definition gtb (x y : t) : bool := (val x >? val y).

  Definition of_bool (b : bool) : t := mk width (if b then 1 else 0).

  Definition mulx (x y : t) : t * t :=
    let p := val x * val y in
    (mk width (p / base width), mk width (p mod base width)).

  Definition adc_2_short (x1 x0 y0 : t) : t * t :=
    let s := val x1 * base width + val x0 + val y0 in
    let r := s mod (base width * base width) in
    (mk width (r / base width), mk width (r mod base width)).

  Definition adc_2_full (x1 x0 y1 y0 : t) : t * t :=
    let s := val x1 * base width + val x0
           + val y1 * base width + val y0 in
    let r := s mod (base width * base width) in
    (mk width (r / base width), mk width (r mod base width)).

  Definition adc_3 (x2 x1 x0 y1 y0 : t) : t * t * t :=
    let s := val x2 * base width * base width
           + val x1 * base width + val x0
           + val y1 * base width + val y0 in
    let r2 := s / (base width * base width) in
    let rem := s mod (base width * base width) in
    (mk width r2, mk width (rem / base width), mk width (rem mod base width)).

  (** ** Specs *)

  Lemma spec_to_Z : forall x, 0 <= to_Z x < base width.
  Proof. exact (val_range width). Qed.

  Lemma spec_zero : to_Z zero = 0.
  Proof.
    unfold zero, to_Z.
    apply val_mk_small.
    split; [lia|apply base_pos].
  Qed.

  Lemma spec_one : to_Z one = 1.
  Proof.
    unfold one, to_Z.
    apply val_mk_small.
    split.
    - lia.
    - pose proof (base_ge_2 width). lia.
  Qed.

  Lemma spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Proof.
    intros x y.
    unfold add, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Proof.
    intros x y.
    unfold sub, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.
  Proof.
    intros x y.
    unfold mul, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.
  Proof.
    intros u_hi u_lo v Hv Hhi.
    unfold div, to_Z in *.
    set (hi := val u_hi).
    set (lo := val u_lo).
    set (d := val v).
    assert (Hhi_range : 0 <= hi < base width).
    { subst hi. apply val_range. }
    assert (Hlo_range : 0 <= lo < base width).
    { subst lo. apply val_range. }
    assert (Hd_range : 0 <= d < base width).
    { subst d. apply val_range. }
    assert (Hd : 0 < d) by lia.
    destruct (d =? 0) eqn:Hd0.
    - apply Z.eqb_eq in Hd0. lia.
    - destruct (hi >=? d) eqn:Hhid.
      + apply Z.geb_le in Hhid. lia.
      + set (dividend := hi * base width + lo).
        assert (Hdividend : 0 <= dividend < d * base width).
        { subst dividend. nia. }
        assert (Hq_range : 0 <= dividend / d < base width).
        { apply div_in_range; lia. }
        assert (Hr_range : 0 <= dividend mod d < d).
        { apply Z.mod_pos_bound. lia. }
        assert (Hr_small : 0 <= dividend mod d < base width).
        { split.
          - lia.
          - eapply Z.lt_trans.
            + exact (proj2 Hr_range).
            + exact (proj2 Hd_range). }
        exists (mk width (dividend / d)), (mk width (dividend mod d)).
        split.
        * reflexivity.
        * split.
          -- rewrite (val_mk_small _ _ Hq_range).
             rewrite (val_mk_small _ _ Hr_small).
             subst dividend.
             symmetry.
             apply div_mod_decompose.
             lia.
          -- rewrite (val_mk_small _ _ Hr_small).
             exact Hr_range.
  Qed.

  Lemma spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.
  Proof.
    intros u_hi u_lo v H.
    unfold div, to_Z in *.
    destruct (val v =? 0) eqn:Hd0.
    - reflexivity.
    - destruct H as [H0|Hhi].
      + apply Z.eqb_neq in Hd0. contradiction.
      + assert (Hcmp : (val u_hi >=? val v) = true).
        { apply Z.geb_le. lia. }
        rewrite Hcmp.
        reflexivity.
  Qed.

  Lemma spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros x n.
    unfold shl, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.
  Proof.
    intros x n.
    unfold shr, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x - (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.
  Proof.
    intros x n.
    unfold asr, to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.
  Proof.
    intros x y.
    unfold or, to_Z.
    rewrite val_mk.
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
  Proof.
    destruct b.
    - apply spec_one.
    - apply spec_zero.
  Qed.

  Lemma spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.
  Proof.
    intros x y.
    unfold mulx, to_Z.
    set (m := base width).
    set (p := val x * val y).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hp : 0 <= p < m * m).
    { subst p m.
      pose proof (val_range width x).
      pose proof (val_range width y).
      nia. }
    assert (Hhi : 0 <= p / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= p mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (p / m * m + p mod m = p).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.
  Proof.
    intros x1 x0 y0 Hx1.
    unfold adc_2_short, to_Z in *.
    set (m := base width).
    set (s := val x1 * m + val x0 + val y0).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hs : 0 <= s < m * m).
    { subst s m.
      pose proof (val_range width x1).
      pose proof (val_range width x0).
      pose proof (val_range width y0).
      nia. }
    rewrite Z.mod_small by exact Hs.
    assert (Hhi : 0 <= s / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= s mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (s / m * m + s mod m = s).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_2_short_mod : forall x1 x0 y0,
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 + to_Z y0)
        mod (base width * base width).
  Proof.
    intros x1 x0 y0.
    unfold adc_2_short, to_Z.
    set (m := base width).
    set (s := val x1 * m + val x0 + val y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).
  Proof.
    intros x1 x0 y1 y0.
    unfold adc_2_full, to_Z.
    set (m := base width).
    set (s := val x1 * m + val x0 + val y1 * m + val y0).
    set (r := s mod (m * m)).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hr : 0 <= r < m * m).
    { subst r. apply Z.mod_pos_bound. lia. }
    assert (Hhi : 0 <= r / m < m).
    { apply div_in_range; lia. }
    assert (Hlo : 0 <= r mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ Hhi).
    rewrite (val_mk_small _ _ Hlo).
    change (base width) with m.
    change (base width * base width) with (m * m).
    change (r / m * m + r mod m = r).
    apply div_mod_decompose.
    exact Hm.
  Qed.

  Lemma spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.
  Proof.
    intros x2 x1 x0 y1 y0 Hx2.
    unfold adc_3, to_Z in *.
    set (m := base width).
    set (s := val x2 * m * m + val x1 * m + val x0 + val y1 * m + val y0).
    assert (Hm : 0 < m).
    { subst m. apply base_pos. }
    assert (Hs : 0 <= s < (m * m) * m).
    { subst s m.
      pose proof (val_range width x2).
      pose proof (val_range width x1).
      pose proof (val_range width x0).
      pose proof (val_range width y1).
      pose proof (val_range width y0).
      nia. }
    assert (H2 : 0 <= s / (m * m) < m).
    { apply div_in_range; lia. }
    assert (Hrem : 0 <= s mod (m * m) < m * m).
    { apply Z.mod_pos_bound. lia. }
    assert (H1 : 0 <= s mod (m * m) / m < m).
    { apply div_in_range; lia. }
    assert (H0 : 0 <= s mod (m * m) mod m < m).
    { apply Z.mod_pos_bound. lia. }
    rewrite (val_mk_small _ _ H2).
    rewrite (val_mk_small _ _ H1).
    rewrite (val_mk_small _ _ H0).
    change (base width) with m.
    change (base width * base width) with (m * m).
    replace (s / (m * m) * m * m + s mod (m * m) / m * m +
             s mod (m * m) mod m)
      with (s / (m * m) * (m * m) +
            (s mod (m * m) / m * m + s mod (m * m) mod m)) by ring.
    replace (s / (m * m) * (m * m) +
             (s mod (m * m) / m * m + s mod (m * m) mod m))
      with (s / (m * m) * (m * m) + s mod (m * m)).
    2:{ rewrite (div_mod_decompose (s mod (m * m)) m Hm). reflexivity. }
    change (s / (m * m) * (m * m) + s mod (m * m) = s).
    apply div_mod_decompose.
    lia.
  Qed.

End SigmaUint128.

(** * Concrete Widen Bridge *)

Module SigmaBridge.

  Lemma width_relation : SigmaUint128.width = (2 * SigmaUint64.width)%positive.
  Proof. reflexivity. Qed.

  Lemma wide_base_square :
    base SigmaUint128.width =
      base SigmaUint64.width * base SigmaUint64.width.
  Proof.
    rewrite width_relation.
    apply base_square_double.
  Qed.

  (** Zero-extend: embed a 64-bit bounded value into 128-bit *)
  Definition widen (x : SigmaUint64.t) : SigmaUint128.t :=
    mk SigmaUint128.width (val x).

  (** Truncate: low 64 bits of a 128-bit value *)
  Definition trunc (x : SigmaUint128.t) : SigmaUint64.t :=
    mk SigmaUint64.width (val x).

  (** High 64 bits of a 128-bit value *)
  Definition hi (x : SigmaUint128.t) : SigmaUint64.t :=
    mk SigmaUint64.width (val x / base SigmaUint64.width).

  (** Combine high and low halves into a 128-bit value *)
  Definition combine (h l : SigmaUint64.t) : SigmaUint128.t :=
    mk SigmaUint128.width (val h * base SigmaUint64.width + val l).

  Lemma spec_widen : forall x,
    SigmaUint128.to_Z (widen x) = SigmaUint64.to_Z x.
  Proof.
    intro x.
    unfold widen, SigmaUint128.to_Z, SigmaUint64.to_Z.
    apply val_mk_small.
    pose proof (SigmaUint64.spec_to_Z x) as Hx.
    rewrite wide_base_square.
    destruct Hx as [Hx0 Hx1].
    split.
    - exact Hx0.
    - pose proof (base_ge_2 SigmaUint64.width) as Hm.
      eapply Z.lt_le_trans.
      + exact Hx1.
      + nia.
  Qed.

  Lemma spec_trunc : forall x,
    SigmaUint64.to_Z (trunc x) = SigmaUint128.to_Z x mod base SigmaUint64.width.
  Proof.
    intro x.
    unfold trunc, SigmaUint64.to_Z, SigmaUint128.to_Z.
    rewrite val_mk.
    reflexivity.
  Qed.

  Lemma spec_hi : forall x,
    SigmaUint64.to_Z (hi x) = SigmaUint128.to_Z x / base SigmaUint64.width.
  Proof.
    intro x.
    unfold hi, SigmaUint64.to_Z, SigmaUint128.to_Z.
    rewrite val_mk.
    apply Z.mod_small.
    pose proof (SigmaUint128.spec_to_Z x) as Hx.
    rewrite wide_base_square in Hx.
    apply div_in_range.
    - exact Hx.
    - apply base_pos.
  Qed.

  Lemma spec_combine : forall h l,
    SigmaUint128.to_Z (combine h l) =
      SigmaUint64.to_Z h * base SigmaUint64.width + SigmaUint64.to_Z l.
  Proof.
    intros h l.
    unfold combine, SigmaUint128.to_Z, SigmaUint64.to_Z.
    set (m := base SigmaUint64.width).
    set (vh := val h).
    set (vl := val l).
    apply val_mk_small.
    pose proof (SigmaUint64.spec_to_Z h) as Hh.
    pose proof (SigmaUint64.spec_to_Z l) as Hl.
    pose proof (base_pos SigmaUint64.width) as Hm.
    change (0 <= vh < m) in Hh.
    change (0 <= vl < m) in Hl.
    change (0 < m) in Hm.
    rewrite wide_base_square.
    change (0 <= vh * m + vl < m * m).
    nia.
  Qed.

End SigmaBridge.

(** * Instantiations — the consistency witnesses *)

Module RuntimeMulConsistency.
  Module P := RuntimeMulProofs.MakeProofs(SigmaUint64).
  Include P.
  Print Assumptions truncating_mul_runtime_correct.
End RuntimeMulConsistency.

Module DivisionConsistency.
  Module P := DivisionProofs.MakeProofs(SigmaUint64)(SigmaUint128)(SigmaBridge).
  Include P.
  Print Assumptions udivrem_correct.
End DivisionConsistency.
