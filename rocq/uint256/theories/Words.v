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

(** A word list represents a multi-word (64-bit) unsigned integer in
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

(* Ensure ws is exactly n words long *)
Definition fit_words (n : nat) (ws : words) : words :=
  firstn n (ws ++ repeat 0 n).

(** 256-bit as a vector of 4 64-bit unsigned integers *)
(** Little-endian: v0 is the least significant *)
Record uint256 := mk_uint256 {
  w0 : t;
  w1 : t;
  w2 : t;
  w3 : t
}.

Definition zero_uint256 : uint256 :=
  mk_uint256 0 0 0 0.

(** ** Conversion Between uint256 and Words *)

(** Convert uint256 record to 4-element word list *)
Definition uint256_to_words (x : uint256) : words :=
  [w0 x; w1 x; w2 x; w3 x].

(** Convert words list to uint256 record, fail if input longer. *)
Definition words_to_uint256 (ws : words) : uint256 :=
  match fit_words 4 ws with
  | [w0; w1; w2; w3] => mk_uint256 w0 w1 w2 w3
  | _ => zero_uint256 (* unreachable: [fit_words 4] always has length 4 *)
  end.

End Make.

(* TODO: Marked for removal once dependencies on uint256 have been
   revised. *)
(*

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
