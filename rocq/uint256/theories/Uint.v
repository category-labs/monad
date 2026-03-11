(** * Finite-Width Unsigned Integer Type

    Provides a type-safe wrapper for bounded unsigned integers
    parameterized by bit width. Arithmetic operations wrap automatically
    mod 2^w.

    This is used by Division.v for modeling uint128_t intermediates in
    the Knuth division subtraction loop. The existing [uint64 := Z] in
    Primitives.v is unchanged; this module adds bounded types where
    type-level enforcement of modular arithmetic is desired.
*)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

(** ** Helper Lemma *)

Lemma two_pow_pos : forall w : positive, 0 < 2 ^ Z.pos w.
Proof.
  intros. apply Z.lt_le_trans with 1; [lia|].
  apply Z.le_trans with (2^1); [simpl; lia|].
  apply Z.pow_le_mono_r; lia.
Qed.

(** ** Core Type *)

(** A [uint w] is a non-negative integer strictly less than [2^w].
    The coercion [:>] lets [uint w] values be used directly as [Z]
    in arithmetic expressions and ZArith lemmas. *)
Record uint (w : positive) := mk_uint {
  to_Z :> Z;
  uint_range : 0 <= to_Z < 2^(Z.pos w)
}.

Arguments mk_uint {w} _ _.
Arguments to_Z {w} _.
Arguments uint_range {w} _.

(** ** Constructors *)

(** Wrap any Z value into the bounded range via [mod 2^w]. *)
Definition uint_wrap (w : positive) (z : Z) : uint w.
  refine (mk_uint (z mod 2^(Z.pos w)) _).
  apply Z.mod_pos_bound. apply two_pow_pos.
Defined.

(** Zero. *)
Definition uzero (w : positive) : uint w := uint_wrap w 0.

(** ** Wrapping Arithmetic *)

Definition uint_add {w} (a b : uint w) : uint w := uint_wrap w (a + b).
Definition uint_sub {w} (a b : uint w) : uint w := uint_wrap w (a - b).
Definition uint_mul {w} (a b : uint w) : uint w := uint_wrap w (a * b).

(** ** Notation Scope *)

Declare Scope uint_scope.
Delimit Scope uint_scope with uint.
Bind Scope uint_scope with uint.
Infix "+" := uint_add : uint_scope.
Infix "-" := uint_sub : uint_scope.
Infix "*" := uint_mul : uint_scope.

(** ** Bit Operations *)

(** Logical right shift. *)
Definition ushr {w} (x : uint w) (n : Z) : uint w :=
  uint_wrap w (Z.shiftr (to_Z x) n).

(** Truncation: narrow to fewer bits. *)
Definition uint_trunc {w1} (w2 : positive) (x : uint w1) : uint w2 :=
  uint_wrap w2 x.

(** ** 128-bit Specific Helpers *)

(** Low 64 bits of a [uint 128], kept as [uint 128].  Models
    [x & 0xffffffffffffffff] in C++: the returned [uint 128] has
    value in [0, 2^64) with bits 64-127 zero. *)
Definition lo128 (x : uint 128) : uint 128 :=
  uint_wrap 128 (to_Z x mod 2^64).

(** High 64 bits of a [uint 128], right-shifted into the low 64
    positions of the result.  Models [x >> 64] in C++: the returned
    [uint 128] has value in [0, 2^64) with bits 64-127 zero. *)
Definition hi128 (x : uint 128) : uint 128 := ushr x 64.

(** Arithmetic right shift by 64 of a signed 128-bit interpretation,
    cast back to unsigned.
    Models: [(uint128_t)((int128_t)t >> 64)]. *)
Definition signed_hi128 (t : uint 128) : uint 128 :=
  let v := to_Z t in
  let signed_v := if (v >=? 2^127) then v - 2^128 else v in
  uint_wrap 128 (Z.shiftr signed_v 64).

(** ** Core Specification Lemmas *)

Lemma uint_wrap_spec : forall w z,
  to_Z (uint_wrap w z) = z mod 2^(Z.pos w).
Proof. reflexivity. Qed.

Lemma uint_add_spec : forall w (a b : uint w),
  to_Z (a + b) = (to_Z a + to_Z b) mod 2^(Z.pos w).
Proof. reflexivity. Qed.

Lemma uint_sub_spec : forall w (a b : uint w),
  to_Z (a - b) = (to_Z a - to_Z b) mod 2^(Z.pos w).
Proof. reflexivity. Qed.

Lemma uint_mul_spec : forall w (a b : uint w),
  to_Z (a * b) = (to_Z a * to_Z b) mod 2^(Z.pos w).
Proof. reflexivity. Qed.

(** ** Bound Lemmas *)

Lemma uint_nonneg : forall w (x : uint w), 0 <= to_Z x.
Proof. intros. exact (proj1 (uint_range x)). Qed.

Lemma uint_bound : forall w (x : uint w), to_Z x < 2^(Z.pos w).
Proof. intros. exact (proj2 (uint_range x)). Qed.

(** ** Shift / Helper Specs *)

Lemma ushr_spec : forall w (x : uint w) n,
  0 <= n ->
  to_Z (ushr x n) = Z.shiftr (to_Z x) n mod 2^(Z.pos w).
Proof. reflexivity. Qed.

Lemma lo128_spec : forall (x : uint 128),
  to_Z (lo128 x) = to_Z x mod 2^64.
Proof.
  intros. unfold lo128. rewrite uint_wrap_spec.
  rewrite Z.mod_small; [reflexivity|].
  pose proof (Z.mod_pos_bound (to_Z x) (2^64) ltac:(lia)) as [H1 H2].
  split; [assumption|].
  apply Z.lt_trans with (2^64); [assumption|].
  apply Z.pow_lt_mono_r; lia.
Qed.

Lemma hi128_spec : forall (x : uint 128),
  to_Z (hi128 x) = Z.shiftr (to_Z x) 64.
Proof.
  intros. unfold hi128. rewrite ushr_spec by lia.
  rewrite Z.mod_small; [reflexivity|].
  split.
  - apply Z.shiftr_nonneg. apply uint_nonneg.
  - rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_lt_upper_bound.
    + lia.
    + pose proof (uint_bound _ x).
      apply Z.lt_le_trans with (2 ^ Z.pos 128); [assumption|].
      replace (2^128) with (2^64 * 2^64) by ring. lia.
Qed.

Lemma lo128_bound : forall (x : uint 128),
  0 <= to_Z (lo128 x) < 2^64.
Proof.
  intros. rewrite lo128_spec. apply Z.mod_pos_bound. lia.
Qed.

Lemma hi128_bound : forall (x : uint 128),
  0 <= to_Z (hi128 x) < 2^64.
Proof.
  intros. rewrite hi128_spec.
  split.
  - apply Z.shiftr_nonneg. apply (uint_nonneg _ x).
  - rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_lt_upper_bound; [lia|].
    pose proof (uint_bound _ x).
    apply Z.lt_le_trans with (2 ^ Z.pos 128); [assumption|].
    replace (2^128) with (2^64 * 2^64) by ring. lia.
Qed.

(** Wrapping a value already in range is identity. *)
Lemma uint_wrap_small : forall w z,
  0 <= z < 2^(Z.pos w) ->
  to_Z (uint_wrap w z) = z.
Proof.
  intros. rewrite uint_wrap_spec. apply Z.mod_small. assumption.
Qed.
