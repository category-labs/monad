(** * Shared Lower-Level Assembly

    This file provides a canonical assembly of the 64-bit lower layers
    used throughout the uint256 development.  It is the first step in
    removing duplicate functor instantiations higher up the stack. *)

From Uint256 Require Import Uint Primitives Words.

Module Type BaseSig.
Declare Module U64 : Uint64Ops.

Include Primitives.Make(U64).
Include Words.Make(U64).
End BaseSig.

Module Type BaseProofSig.
Declare Module U64 : Uint64.

Include Primitives.Make(U64).
Include Words.Make(U64).
End BaseProofSig.

Module Make (Import Word : Uint64Ops) <: BaseSig.
Module U64 := Word.
Include U64.
Include UintNotations(U64).
Include Primitives.Make(U64).
Include Words.Make(U64).
End Make.

Module MakeProof (Import Word : Uint64) <: BaseProofSig.
Module U64 := Word.
Include U64.
Include UintNotations(U64).
Include Primitives.Make(U64).
Include Words.Make(U64).
End MakeProof.
