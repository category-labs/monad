(** * Word-List Representation for Multi-Word Arithmetic

    The [Make] functor (parameterized by [Uint64Ops]) defines the
    [words] type and basic accessors for multi-word unsigned
    integers in little-endian order:

    - [words]: list of [t] (least significant word first)
    - [get_word] / [set_word]: indexed access and update
    - [extend_words]: zero-padded word list of a given length

    This is a shared foundation used by RuntimeMul.v, Division.v,
    and their proof files. *)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Uint Primitives.
Import ListNotations.

Module Make (Import U64 : Uint64Ops).
Include UintNotations(U64).
Open Scope uint_scope.

(** ** Word List Type *)

(** A word list represents a multi-word unsigned integer in
    little-endian order.  The first element is the least significant
    word. *)
Definition words := list t.

(** ** Word Access and Update Helpers *)

(** Get word at index i (0 if out of bounds) *)
Definition get_word (ws : words) (i : nat) : t :=
  nth i ws 0.

(** Set word at index i *)
Fixpoint set_word (ws : words) (i : nat) (v : t) : words :=
  match ws, i with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | w :: rest, S i' => w :: set_word rest i' v
  end.

(** Extend word list to length n (padding with zeros) *)
Definition extend_words (n : nat) : words := repeat 0 n.

End Make.

(* TODO: Marked for removal once dependencies on uint256 have been
   revised. *)
(*
(** ** Conversion Between uint256 and Words *)

(** Convert uint256 record to 4-element word list *)
Definition uint256_to_words (x : uint256) : words :=
  [v0 x; v1 x; v2 x; v3 x].

(** Convert 4-element word list to uint256 record *)
Definition words_to_uint256 (ws : words) : uint256 :=
  match ws with
  | [w0; w1; w2; w3] => mk_uint256 w0 w1 w2 w3
  | _ => mk_uint256 0 0 0 0  (* fallback for malformed input *)
  end.

(** ** Word List Validity and Bounds *)

(** All words in list are in valid uint64 range *)
(* TODO: Holds by construction in Uint module *)
Definition words_valid (ws : words) : Prop :=
  Forall (fun w => 0 <= w < modulus64) ws.

(** Normalize a word list value to n words *)
(* TODO: Marked for possible deletion; at most only needed for proofs *)
Definition normalize_words (z : Z) (n : nat) : Z :=
  z mod modulus_words n.
*)
