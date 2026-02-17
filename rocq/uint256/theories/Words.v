(** * Word-List Representation for Multi-Word Arithmetic

    This file defines the word-list representation used by multi-word
    operations (multiplication, division). A word list represents a
    multi-word unsigned integer in little-endian order.

    This is a shared foundation used by both constexpr and runtime
    multiplication models, as well as division.
*)

From Stdlib Require Import ZArith Lia List.
From Uint256 Require Import Primitives.
Import ListNotations.
Open Scope Z_scope.

(** ** Word List Type *)

(** A word list represents a multi-word unsigned integer in little-endian order.
    The first element is the least significant word. *)
Definition words := list uint64.

(** Convert a word list to its mathematical value (little-endian) *)
Fixpoint to_Z_words (ws : words) : Z :=
  match ws with
  | [] => 0
  | w :: rest => to_Z64 w + 2^64 * to_Z_words rest
  end.

(** The number of bits needed to represent an n-word number *)
Definition words_bits (n : nat) : Z := Z.of_nat n * 64.

(** Modulus for an n-word number *)
Definition modulus_words (n : nat) : Z := 2 ^ (words_bits n).

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
Definition words_valid (ws : words) : Prop :=
  Forall (fun w => 0 <= w < modulus64) ws.

(** Normalize a word list value to n words *)
Definition normalize_words (z : Z) (n : nat) : Z :=
  z mod modulus_words n.

(** ** Word Access and Update Helpers *)

(** Get word at index i (0 if out of bounds) *)
Definition get_word (ws : words) (i : nat) : uint64 :=
  nth i ws 0.

(** Set word at index i *)
Fixpoint set_word (ws : words) (i : nat) (v : uint64) : words :=
  match ws, i with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | w :: rest, S i' => w :: set_word rest i' v
  end.

(** Extend word list to length n (padding with zeros) *)
Definition extend_words (n : nat) : words := repeat 0 n.
