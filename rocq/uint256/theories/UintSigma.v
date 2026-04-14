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

(** * Concrete Uint64 Module *)

Module SigmaUint64.

  Definition width := 64%positive.
  Definition t := bounded width.

  Lemma width_is_64 : width = 64%positive.
  Proof. reflexivity. Qed.

  Definition to_Z (x : t) : Z := val x.

  (** Decidable equality *)
  Lemma t_eq_dec : forall x y : t, {x = y} + {x <> y}.
  Admitted.

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

  (** ** Specs — all Admitted for now *)

  Lemma spec_to_Z : forall x, 0 <= to_Z x < base width.
  Admitted.

  Lemma spec_zero : to_Z zero = 0.
  Admitted.

  Lemma spec_one : to_Z one = 1.
  Admitted.

  Lemma spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Admitted.

  Lemma spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Admitted.

  Lemma spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.
  Admitted.

  Lemma spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.
  Admitted.

  Lemma spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.
  Admitted.

  Lemma spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Admitted.

  Lemma spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.
  Admitted.

  Lemma spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x - (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.
  Admitted.

  Lemma spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.
  Admitted.

  Lemma spec_eqb : forall x y, eqb x y = (to_Z x =? to_Z y).
  Admitted.

  Lemma spec_ltb : forall x y, ltb x y = (to_Z x <? to_Z y).
  Admitted.

  Lemma spec_leb : forall x y, leb x y = (to_Z x <=? to_Z y).
  Admitted.

  Lemma spec_gtb : forall x y, gtb x y = (to_Z x >? to_Z y).
  Admitted.

  Lemma spec_of_bool : forall b, to_Z (of_bool b) = if b then 1 else 0.
  Admitted.

  Lemma spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.
  Admitted.

  Lemma spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.
  Admitted.

  Lemma spec_adc_2_short_mod : forall x1 x0 y0,
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 + to_Z y0)
        mod (base width * base width).
  Admitted.

  Lemma spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).
  Admitted.

  Lemma spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.
  Admitted.

End SigmaUint64.

(** * Concrete Uint128 Module *)

Module SigmaUint128.

  Definition width := 128%positive.
  Definition t := bounded width.

  Lemma width_is_128 : width = 128%positive.
  Proof. reflexivity. Qed.

  Definition to_Z (x : t) : Z := val x.

  Lemma t_eq_dec : forall x y : t, {x = y} + {x <> y}.
  Admitted.

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

  (** ** Specs — all Admitted for now *)

  Lemma spec_to_Z : forall x, 0 <= to_Z x < base width.
  Admitted.

  Lemma spec_zero : to_Z zero = 0.
  Admitted.

  Lemma spec_one : to_Z one = 1.
  Admitted.

  Lemma spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Admitted.

  Lemma spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Admitted.

  Lemma spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.
  Admitted.

  Lemma spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.
  Admitted.

  Lemma spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.
  Admitted.

  Lemma spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Admitted.

  Lemma spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.
  Admitted.

  Lemma spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x - (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.
  Admitted.

  Lemma spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.
  Admitted.

  Lemma spec_eqb : forall x y, eqb x y = (to_Z x =? to_Z y).
  Admitted.

  Lemma spec_ltb : forall x y, ltb x y = (to_Z x <? to_Z y).
  Admitted.

  Lemma spec_leb : forall x y, leb x y = (to_Z x <=? to_Z y).
  Admitted.

  Lemma spec_gtb : forall x y, gtb x y = (to_Z x >? to_Z y).
  Admitted.

  Lemma spec_of_bool : forall b, to_Z (of_bool b) = if b then 1 else 0.
  Admitted.

  Lemma spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.
  Admitted.

  Lemma spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.
  Admitted.

  Lemma spec_adc_2_short_mod : forall x1 x0 y0,
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 + to_Z y0)
        mod (base width * base width).
  Admitted.

  Lemma spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).
  Admitted.

  Lemma spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.
  Admitted.

End SigmaUint128.

(** * Concrete Widen Bridge *)

Module SigmaBridge.

  Lemma width_relation : SigmaUint128.width = (2 * SigmaUint64.width)%positive.
  Proof. reflexivity. Qed.

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
  Admitted.

  Lemma spec_trunc : forall x,
    SigmaUint64.to_Z (trunc x) = SigmaUint128.to_Z x mod base SigmaUint64.width.
  Admitted.

  Lemma spec_hi : forall x,
    SigmaUint64.to_Z (hi x) = SigmaUint128.to_Z x / base SigmaUint64.width.
  Admitted.

  Lemma spec_combine : forall h l,
    SigmaUint128.to_Z (combine h l) =
      SigmaUint64.to_Z h * base SigmaUint64.width + SigmaUint64.to_Z l.
  Admitted.

End SigmaBridge.

(** * Instantiations — the consistency witnesses *)

Module RuntimeMulConsistency.
  Module P := RuntimeMulProofs.MakeProofs(SigmaUint64).
  Include P.
End RuntimeMulConsistency.

Module DivisionConsistency.
  Module P := DivisionProofs.MakeProofs(SigmaUint64)(SigmaUint128)(SigmaBridge).
  Include P.
End DivisionConsistency.
