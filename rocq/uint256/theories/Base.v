(** * Shared Lower-Level Assembly

    This file provides a canonical assembly of the 64-bit lower layers
    used throughout the uint256 development.  It is the first step in
    removing duplicate functor instantiations higher up the stack. *)

From Uint256 Require Import Uint Primitives Words.

Module Type BaseSig.
Declare Module U64 : Uint64Ops.

Record result64 : Type := {
  value64 : U64.t;
  carry64 : bool
}.

Parameter addc64 : U64.t -> U64.t -> bool -> result64.
Parameter subb64 : U64.t -> U64.t -> bool -> result64.
Parameter shld64 : U64.t -> U64.t -> nat -> U64.t.
Parameter shrd64 : U64.t -> U64.t -> nat -> U64.t.

Definition words := list U64.t.
Parameter get_word : words -> nat -> U64.t.
Parameter set_word : words -> nat -> U64.t -> words.
Parameter extend_words : nat -> words.
Parameter fit_words : nat -> words -> words.

Record uint256 : Type := mk_uint256 {
  w0 : U64.t;
  w1 : U64.t;
  w2 : U64.t;
  w3 : U64.t
}.

Parameter zero_uint256 : uint256.
Parameter uint256_to_words : uint256 -> words.
Parameter words_to_uint256 : words -> uint256.
End BaseSig.

Module Make (Import Word : Uint64Ops) <: BaseSig.
Module U64 := Word.
Include U64.
Include UintNotations(U64).
Include Primitives.Make(U64).
Include Words.Make(U64).
End Make.
