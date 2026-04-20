(** * Canonical Model Stack Assembly

    This file assembles the model-side uint256 stack from a single
    shared lower-level base instance.  Proof-side migration remains a
    later step. *)

From Uint256 Require Import Uint Base RuntimeMul Division Arithmetic.

Module Make (Import U64 : Uint64Ops) (U128 : Uint128Ops)
  (Import Bridge : UintWidenOps U64 U128).
Module Base := Base.Make(U64).
Module RM := RuntimeMul.MakeOn(Base).
Module Div := Division.MakeOn(Base)(U128)(Bridge).
End Make.
