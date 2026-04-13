(** * Primitive 64-bit Operations

    Definitions for composite 64-bit operations built from the
    [UintOps] interface.  These model the corresponding C++
    operations in uint256.hpp.

    The [Make] functor (parameterized by [Uint64Ops]) defines:
    - addc64: addition with carry (models addc_constexpr)
    - subb64: subtraction with borrow (models subb_constexpr)
    - shld64/shrd64: double-precision shifts (models shld/shrd_constexpr)

    Multi-precision primitives (mulx, adc_2, adc_3, div) are part
    of the [UintOps] interface itself (see Uint.v).

    Legacy concrete Z-based definitions and correctness lemmas
    are retained below the functor for backward compatibility. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Uint256 Require Import Uint.

Module Make (Import U64 : Uint64Ops).
Include UintNotations(U64).
Open Scope uint_scope.

(** 64-bit result with carry/borrow *)
Record result64 := {
  value64 : t;
  carry64 : bool
}.

(** ** Addition with Carry *)

(** Specification for addc (matches addc_constexpr from uint256.hpp)

    Computes: sum = lhs + rhs + carry_in
    Returns: (sum mod 2^64, carry_out)

    This matches the logic:
      uint64_t const sum = lhs + rhs;
      bool carry_out = sum < lhs;
      uint64_t const sum_carry = sum + carry_in;
      carry_out |= sum_carry < sum;
*)
Definition addc64 (lhs rhs : t) (carry_in : bool) : result64 :=
  let sum := lhs + rhs in
  let cout := sum <? lhs in
  let sum_carry := sum + of_bool carry_in in
  {|
    value64 := sum_carry;
    carry64 := (cout || (sum_carry <? sum))%bool
  |}.

(** ** Subtraction with Borrow *)

(** Specification for subb (matches subb_constexpr from uint256.hpp)

    Computes: diff = lhs - rhs - borrow_in
    Returns: (diff mod 2^64, borrow_out)

    This matches the logic:
      uint64_t const sub = lhs - rhs;
      bool borrow_out = rhs > lhs;
      uint64_t const sub_borrow = sub - borrow_in;
      borrow_out |= borrow_in > sub;
*)

Definition subb64 (lhs rhs : t) (borrow_in : bool) : result64 :=
  let bin := of_bool borrow_in in
  let sub := lhs - rhs in
  let bout := rhs >? lhs in
  let sub_borrow := sub - bin in
  {|
    value64 := sub_borrow;
    carry64 := (bout || (bin >? sub))%bool  (* borrow if result would be negative *)
  |}.

(** ** Double-Precision Shifts *)

(** Left shift with double precision (shld instruction)

    Computes: high bits of [(high || low) << shift]

    This matches shld_constexpr in uint256.hpp:
      return (high << shift) | ((low >> 1) >> (63 - shift));

    The formulation [(low >> 1) >> (63 - shift)] instead of
    [low >> (64 - shift)] avoids undefined behavior when
    [shift = 0] (x86 masks the shift count to 6 bits). *)
Definition shld64 (high low : t) (shift : nat) : t :=
  or (shl high shift) (shr (shr low 1) (63 - shift)).

(** Right shift with double precision (shrd instruction)

    Computes: low bits of [(high || low) >> shift]

    This matches shrd_constexpr in uint256.hpp:
      return (low >> shift) | ((high << 1) << (63 - shift)); *)
Definition shrd64 (high low : t) (shift : nat) : t :=
  or (shr low shift) (shl (shl high 1) (63 - shift)).

(** Note: [mulx] and [div] are part of the [UintOps] interface
    and do not need separate definitions here. *)

End Make.
