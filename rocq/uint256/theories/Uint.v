(** * Abstract Bounded Unsigned Integer Interface

    Module types for fixed-width unsigned integer operations,
    parameterized by bit width.  All model and proof files in
    this development are functors over these module types.

    The interface is split into two layers:

    - [UintOps]: operations only (no [to_Z], no specs).  Model
      functors (RuntimeMul.Make, Division.Make, Words.Make, etc.)
      take [UintOps] to structurally prevent escape into Z.

    - [Uint]: extends [UintOps] with a [to_Z] interpretation into
      Z and modular-arithmetic specifications.  Proof functors
      take [Uint] to access [to_Z] and the spec axioms.

    Width-specific variants ([Uint64], [Uint128], [Uint64Ops],
    [Uint128Ops]) fix the width via an axiom.

    [UintNotations] is a functor over [UintOps] providing infix
    notation for arithmetic and comparison in [uint_scope].

    Every operation wraps its result into [0, wB) where
    [wB = base width = 2^width]. *)

From Stdlib Require Import ZArith PArith Bool Lia.
From Stdlib Require Import DoubleType.
#[local] Open Scope Z_scope.

(** ** Operations layer — no [to_Z], no specs *)

Module Type UintOps.

  (** Carrier type representing unsigned integers *)
  Parameter t : Type.

  (** Fixed width in bits *)
  Parameter width : positive.

  (** Carrier type has decidable equality *)
  Parameter t_eq_dec : forall x y : t, {x = y} + {x <> y}.

  (** *** Constants *)
  Parameter zero : t.
  Parameter one : t.

  (** *** Wrapping arithmetic modelling C++ unsigned arithmetic. *)
  Parameter add : t -> t -> t.
  Parameter sub : t -> t -> t.
  Parameter mul : t -> t -> t.

  (** *** Unsigned division and modulo *)
  Parameter divw : t -> t -> t.
  Parameter modw : t -> t -> t.

  (** *** Shifts
      Shift amounts are [nat] (no Z dependency). *)
  Parameter shl : t -> nat -> t.
  Parameter shr : t -> nat -> t.

  (** *** Bitwise OR *)
  Parameter orw : t -> t -> t.

  (** *** Comparison *)
  Parameter eqb : t -> t -> bool.
  Parameter ltb : t -> t -> bool.
  Parameter leb : t -> t -> bool.
  Parameter gtb : t -> t -> bool.

  (** *** Bool injection *)
  Parameter of_bool : bool -> t.

  (** ** Multi-precision arithmetic primitives modelling hardware
      intrinsics (mulx, adc, div) that operate on values wider
      than a single [t]. *)

  (** [adc_2_short hi lo addend] returns [(r_hi, r_lo)] where
      [r_hi * wB + r_lo = hi * wB + lo + addend].
      Adds [addend] to the double-width value [(hi, lo)].
      The result is exact (no overflow) when [hi <= wB - 2].
      Models the 3-argument [adc_2] overload in uint256.hpp. *)
  Parameter adc_2_short : t -> t -> t -> t * t.

  (** [adc_2_full hi lo y_hi y_lo] returns [(r_hi, r_lo)] where
      [r_hi * wB + r_lo = (hi * wB + lo + y_hi * wB + y_lo) mod wB^2].
      Adds two double-width values, truncating to double-width (the
      top carry is discarded).
      Models the 4-argument [adc_2] overload in uint256.hpp. *)
  Parameter adc_2_full : t -> t -> t -> t -> t * t.

  (** [adc_3 x_2 x_1 x_0 y_1 y_0] returns [(r_2, r_1, r_0)] where
      [r_2 * wB^2 + r_1 * wB + r_0 =
       x_2 * wB^2 + x_1 * wB + x_0 + y_1 * wB + y_0].
      Adds a double-width value [(y_1, y_0)] to a triple-width value
      [(x_2, x_1, x_0)].  The result is exact (no overflow) when
      [x_2 <= wB - 2].
      Models [adc_3] in uint256.hpp. *)
  Parameter adc_3 : t -> t -> t -> t -> t -> t * t * t.

  (** [mulx x y] returns [(hi, lo)] where
      [hi * wB + lo = x * y].
      Full multiplication of two values, producing a double-width
      result.  Models the BMI2 [mulx] instruction in uint256.hpp. *)
  Parameter mulx : t -> t -> t * t.

  (** [div u_hi u_lo v] returns [(quot, rem)] where
      [u_hi * wB + u_lo = quot * v + rem] with [0 <= rem < v].
      Divides a double-width dividend [(u_hi, u_lo)] by [v].
      Precondition: [u_hi < v] (ensures the quotient fits in [t]).
      Models [div_intrinsic] / [div_constexpr] in uint256.hpp. *)
  Parameter div : t -> t -> t -> t * t.

End UintOps.

(** ** Specification layer — adds [to_Z] and specs *)

Module Type Uint <: UintOps.
  Include UintOps.

  (** *** Interpretation into Z (specification only) *)
  Parameter to_Z : t -> Z.

  (** ** Specifications *)

  (** Range: every value is in [0, wB) where [wB = base width = 2^width] *)
  Axiom spec_to_Z : forall x, 0 <= to_Z x < base width.

  (** [to_Z] is injective (equal values <-> equal elements) *)
  Axiom spec_to_Z_inj : forall x y, to_Z x = to_Z y -> x = y.

  (** Constant specifications *)
  Axiom spec_zero : to_Z zero = 0.
  Axiom spec_one  : to_Z one = 1.

  (** Wrapping arithmetic specifications *)
  Axiom spec_add : forall x y,
    to_Z (add x y) = (to_Z x + to_Z y) mod base width.
  Axiom spec_sub : forall x y,
    to_Z (sub x y) = (to_Z x - to_Z y) mod base width.
  Axiom spec_mul : forall x y,
    to_Z (mul x y) = (to_Z x * to_Z y) mod base width.

  (** Division and modulo specifications *)
  Axiom spec_divw : forall x y,
    to_Z (divw x y) = (to_Z x / to_Z y) mod base width.
  Axiom spec_modw : forall x y,
    to_Z (modw x y) = (to_Z x mod to_Z y) mod base width.

  (** Shift specifications *)
  Axiom spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Axiom spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.

  (** Bitwise OR specification *)
  Axiom spec_orw : forall x y,
    to_Z (orw x y) = Z.lor (to_Z x) (to_Z y) mod base width.

  (** Comparison specifications *)
  Axiom spec_eqb : forall x y, eqb x y = (to_Z x =? to_Z y).
  Axiom spec_ltb : forall x y, ltb x y = (to_Z x <? to_Z y).
  Axiom spec_leb : forall x y, leb x y = (to_Z x <=? to_Z y).
  Axiom spec_gtb : forall x y, gtb x y = (to_Z x >? to_Z y).

  (** Bool injection specification *)
  Axiom spec_of_bool : forall b, to_Z (of_bool b) = if b then 1 else 0.

End Uint.

(** ** Width-specific module types *)

Module Type Uint64 <: Uint.
  Include Uint.
  Axiom width_is_64 : width = 64%positive.
End Uint64.

Module Type Uint128 <: Uint.
  Include Uint.
  Axiom width_is_128 : width = 128%positive.
End Uint128.

(** ** Width-specific operations-only module types *)

Module Type Uint64Ops <: UintOps.
  Include UintOps.
  Axiom width_is_64 : width = 64%positive.
End Uint64Ops.

Module Type Uint128Ops <: UintOps.
  Include UintOps.
  Axiom width_is_128 : width = 128%positive.
End Uint128Ops.

(** ** Notations *)

Declare Scope uint_scope.
Delimit Scope uint_scope with Uint.

Module UintNotations (U : UintOps).
  Notation "0" := U.zero : uint_scope.
  Notation "1" := U.one : uint_scope.
  Infix "+" := U.add : uint_scope.
  Infix "-" := U.sub : uint_scope.
  Infix "*" := U.mul : uint_scope.
  Infix "mod" := U.modw : uint_scope.
  Infix "<?" := U.ltb : uint_scope.
  Infix "=?" := U.eqb : uint_scope.
  Infix "<=?" := U.leb : uint_scope.
  Infix ">?" := U.gtb : uint_scope.
End UintNotations.
