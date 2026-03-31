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

  (** [div u_hi u_lo v] returns [Some (quot, rem)] where
      [u_hi * wB + u_lo = quot * v + rem] with [0 <= rem < v],
      or [None] if [v = 0] or [u_hi >= v] (quotient overflow).
      Models the x86 [div] instruction / C++ [div_intrinsic]. *)
  Parameter div : t -> t -> t -> option (t * t).

  (** *** Shifts
      Shift amounts are [nat] (no Z dependency). *)
  Parameter shl : t -> nat -> t.
  Parameter shr : t -> nat -> t.

  (** *** Arithmetic right shift
      Like [shr] but sign-extends from the MSB.
      Models C++ signed right-shift on two's complement values. *)
  Parameter asr : t -> nat -> t.

  (** *** Bitwise OR *)
  Parameter or : t -> t -> t.

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

  (** [div] double-width division.
      Returns [Some (q, r)] when [v > 0] and [u_hi < v]. *)
  Axiom spec_div : forall u_hi u_lo v,
    to_Z v > 0 -> to_Z u_hi < to_Z v ->
    exists q r, div u_hi u_lo v = Some (q, r) /\
    to_Z u_hi * base width + to_Z u_lo = to_Z q * to_Z v + to_Z r /\
    0 <= to_Z r < to_Z v.

  (** [div] faults (returns [None]) on overflow or division by zero. *)
  Axiom spec_div_None : forall u_hi u_lo v,
    to_Z v = 0 \/ to_Z u_hi >= to_Z v ->
    div u_hi u_lo v = None.

  (** Shift specifications *)
  Axiom spec_shl : forall x n,
    to_Z (shl x n) = Z.shiftl (to_Z x) (Z.of_nat n) mod base width.
  Axiom spec_shr : forall x n,
    to_Z (shr x n) = Z.shiftr (to_Z x) (Z.of_nat n) mod base width.

  (** Arithmetic right shift specification.
      Interprets [x] as a signed two's complement value, shifts right
      by [n], and wraps the result back to [0, wB). *)
  Axiom spec_asr : forall x n,
    to_Z (asr x n) =
      Z.shiftr (to_Z x - (if to_Z x <? base width / 2 then 0 else base width))
               (Z.of_nat n)
      mod base width.

  (** Bitwise OR specification *)
  Axiom spec_or : forall x y,
    to_Z (or x y) = Z.lor (to_Z x) (to_Z y) mod base width.

  (** Comparison specifications *)
  Axiom spec_eqb : forall x y, eqb x y = (to_Z x =? to_Z y).
  Axiom spec_ltb : forall x y, ltb x y = (to_Z x <? to_Z y).
  Axiom spec_leb : forall x y, leb x y = (to_Z x <=? to_Z y).
  Axiom spec_gtb : forall x y, gtb x y = (to_Z x >? to_Z y).

  (** Bool injection specification *)
  Axiom spec_of_bool : forall b, to_Z (of_bool b) = if b then 1 else 0.

  (** ** Multi-precision primitive specifications *)

  (** [mulx] full multiplication: [hi * wB + lo = x * y] *)
  Axiom spec_mulx : forall x y,
    let '(hi, lo) := mulx x y in
    to_Z hi * base width + to_Z lo = to_Z x * to_Z y.

  (** [adc_2_short] exact double-width addition.
      Precondition: [to_Z x1 <= wB - 2] ensures no overflow. *)
  Axiom spec_adc_2_short : forall x1 x0 y0,
    to_Z x1 <= base width - 2 ->
    let '(r1, r0) := adc_2_short x1 x0 y0 in
    to_Z r1 * base width + to_Z r0 =
      to_Z x1 * base width + to_Z x0 + to_Z y0.

  (** [adc_2_full] truncating double-width addition.
      The result is the sum modulo [wB^2]. *)
  Axiom spec_adc_2_full : forall x1 x0 y1 y0,
    let '(r1, r0) := adc_2_full x1 x0 y1 y0 in
    to_Z r1 * base width + to_Z r0 =
      (to_Z x1 * base width + to_Z x0 +
       to_Z y1 * base width + to_Z y0) mod (base width * base width).

  (** [adc_3] exact triple-width addition.
      Precondition: [to_Z x2 <= wB - 2] ensures no overflow. *)
  Axiom spec_adc_3 : forall x2 x1 x0 y1 y0,
    to_Z x2 <= base width - 2 ->
    let '(r2, r1, r0) := adc_3 x2 x1 x0 y1 y0 in
    to_Z r2 * base width * base width + to_Z r1 * base width + to_Z r0 =
      to_Z x2 * base width * base width + to_Z x1 * base width + to_Z x0
      + to_Z y1 * base width + to_Z y0.

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

(** ** Double-width bridge — operations layer

    Witnesses that [W] is double the width of [N]:
    [W.width = 2 * N.width].

    [N] is the "narrow" word type (e.g., 32-bit or 64-bit).
    [W] is the "wide" intermediate type (e.g., 64-bit or 128-bit).

    Conversion operations model C++ implicit/explicit width casts
    between [narrow_t] and [wide_t]. *)

Module Type UintWidenOps (N : UintOps) (W : UintOps).

  (** Width relationship: wide is exactly double narrow *)
  Axiom width_relation : W.width = (2 * N.width)%positive.

  (** Zero-extend a narrow value into the wide type.
      Models: [(wide_t)x] implicit widening cast in C++. *)
  Parameter widen : N.t -> W.t.

  (** Extract the low half of a wide value.
      Models: [static_cast<narrow_t>(x)] truncation in C++. *)
  Parameter trunc : W.t -> N.t.

  (** Extract the high half of a wide value.
      Models: [x >> narrow_width] in C++. *)
  Parameter hi : W.t -> N.t.

  (** Construct a wide value from high and low halves.
      Inverse of [(hi x, trunc x)].
      Models: [(wide_t)h << narrow_width | (wide_t)l] in C++. *)
  Parameter combine : N.t -> N.t -> W.t.

End UintWidenOps.

(** ** Double-width bridge — specification layer *)

Module Type UintWiden (N : Uint) (W : Uint).
  Include UintWidenOps N W.

  Axiom spec_widen : forall x,
    W.to_Z (widen x) = N.to_Z x.

  Axiom spec_trunc : forall x,
    N.to_Z (trunc x) = W.to_Z x mod base N.width.

  Axiom spec_hi : forall x,
    N.to_Z (hi x) = W.to_Z x / base N.width.

  Axiom spec_combine : forall h l,
    W.to_Z (combine h l) = N.to_Z h * base N.width + N.to_Z l.

End UintWiden.

(** ** Notations *)

Declare Scope uint_scope.
Delimit Scope uint_scope with Uint.

Module UintNotations (U : UintOps).
  Notation "0" := U.zero : uint_scope.
  Notation "1" := U.one : uint_scope.
  Infix "+" := U.add : uint_scope.
  Infix "-" := U.sub : uint_scope.
  Infix "*" := U.mul : uint_scope.
  (* No infix notation for [or] and [and] — [|] conflicts with
     match-branch syntax and [&] has awkward precedence.
     Use [U.or x y] / [U.and x y] or unqualified when imported. *)
  Infix "<?" := U.ltb : uint_scope.
  Infix "=?" := U.eqb : uint_scope.
  Infix "<=?" := U.leb : uint_scope.
  Infix ">?" := U.gtb : uint_scope.
End UintNotations.
