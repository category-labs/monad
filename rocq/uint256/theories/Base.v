(** * Shared Lower-Level Assembly

    This file provides a canonical assembly of the 64-bit lower layers
    used throughout the uint256 development.  It is the first step in
    removing duplicate functor instantiations higher up the stack. *)

From Stdlib Require Import List.
From Uint256 Require Import Uint Primitives Words.
Import ListNotations.

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
Definition get_word (ws : words) (i : nat) : U64.t :=
  nth i ws U64.zero.

Fixpoint set_word (ws : words) (i : nat) (v : U64.t) : words :=
  match ws, i with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | w :: rest, S i' => w :: set_word rest i' v
  end.

Definition extend_words (n : nat) : words := repeat U64.zero n.

Definition fit_words (n : nat) (ws : words) : words :=
  firstn n (ws ++ repeat U64.zero n).

Record uint256 : Type := mk_uint256 {
  w0 : U64.t;
  w1 : U64.t;
  w2 : U64.t;
  w3 : U64.t
}.

Definition zero_uint256 : uint256 :=
  mk_uint256 U64.zero U64.zero U64.zero U64.zero.

Definition uint256_to_words (x : uint256) : words :=
  [w0 x; w1 x; w2 x; w3 x].

Definition words_to_uint256 (ws : words) : uint256 :=
  match fit_words 4 ws with
  | [w0; w1; w2; w3] => mk_uint256 w0 w1 w2 w3
  | _ => zero_uint256
  end.
End BaseSig.

Module Type BaseProofSig.
Declare Module U64 : Uint64.

Record result64 : Type := {
  value64 : U64.t;
  carry64 : bool
}.

Parameter addc64 : U64.t -> U64.t -> bool -> result64.
Parameter subb64 : U64.t -> U64.t -> bool -> result64.
Parameter shld64 : U64.t -> U64.t -> nat -> U64.t.
Parameter shrd64 : U64.t -> U64.t -> nat -> U64.t.

Definition words := list U64.t.
Definition get_word (ws : words) (i : nat) : U64.t :=
  nth i ws U64.zero.

Fixpoint set_word (ws : words) (i : nat) (v : U64.t) : words :=
  match ws, i with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | w :: rest, S i' => w :: set_word rest i' v
  end.

Definition extend_words (n : nat) : words := repeat U64.zero n.

Definition fit_words (n : nat) (ws : words) : words :=
  firstn n (ws ++ repeat U64.zero n).

Record uint256 : Type := mk_uint256 {
  w0 : U64.t;
  w1 : U64.t;
  w2 : U64.t;
  w3 : U64.t
}.

Definition zero_uint256 : uint256 :=
  mk_uint256 U64.zero U64.zero U64.zero U64.zero.

Definition uint256_to_words (x : uint256) : words :=
  [w0 x; w1 x; w2 x; w3 x].

Definition words_to_uint256 (ws : words) : uint256 :=
  match fit_words 4 ws with
  | [w0; w1; w2; w3] => mk_uint256 w0 w1 w2 w3
  | _ => zero_uint256
  end.
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
