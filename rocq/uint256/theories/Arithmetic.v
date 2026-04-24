(** * Composite Arithmetic Models

    High-level arithmetic functions from [uint256.hpp] built by
    composing the lower-level models from [Primitives.v],
    [RuntimeMul.v], and [Division.v].

    This file covers the arithmetic surface not already modeled in
    those files:

    - 256-bit add/sub with carry/borrow
    - [addmod] and [mulmod]
    - exponentiation by squaring [exp]
    - signed less-than [slt]


    - unsigned comparison on word lists
    - quotient/remainder wrappers for unsigned and signed division

    The internal generic [exp_generic] helper below uses the squaring
    loop for all bases.  The public 256-bit [exp] definition later in
    the file models the dedicated C++ [base == 2] fast path as well. *)

From Stdlib Require Import PArith List Bool.
From Uint256 Require Import Uint Base Primitives Words RuntimeMul Division.
Import ListNotations.

Module Make (B : Base.BaseSig) (U128 : Uint128Ops)
  (Bridge : UintWidenOps B.U64 U128)
  (Div : Division.DivisionSig(B)(U128)(Bridge))
  (RM : RuntimeMul.RuntimeMulSig with Module U64 := B.U64).
Include Div.
Import B.U64.
Include UintNotations(U64).

Open Scope uint_scope.

Definition one_words_generic (n : nat) : words :=
  set_word (extend_words n) 0 1.

Definition word_width : nat := Pos.to_nat U64.width.

Record result256 := {
  value256 : uint256;
  carry256 : bool
}.

Definition addc (xs ys : uint256) : result256 :=
  let r0 := addc64 (w0 xs) (w0 ys) false in
  let r1 := addc64 (w1 xs) (w1 ys) (carry64 r0) in
  let r2 := addc64 (w2 xs) (w2 ys) (carry64 r1) in
  let r3 := addc64 (w3 xs) (w3 ys) (carry64 r2) in
  {| value256 :=
       mk_uint256 (value64 r0) (value64 r1) (value64 r2) (value64 r3);
     carry256 := carry64 r3 |}.

Definition subb (xs ys : uint256) : result256 :=
  let r0 := subb64 (w0 xs) (w0 ys) false in
  let r1 := subb64 (w1 xs) (w1 ys) (carry64 r0) in
  let r2 := subb64 (w2 xs) (w2 ys) (carry64 r1) in
  let r3 := subb64 (w3 xs) (w3 ys) (carry64 r2) in
  {| value256 :=
       mk_uint256 (value64 r0) (value64 r1) (value64 r2) (value64 r3);
     carry256 := carry64 r3 |}.

Definition ltb_uint256 (x y : uint256) : bool :=
  carry256 (subb x y).

Definition add_words_full_uint256 (x y : uint256) : words :=
  let sum := addc x y in
  uint256_to_words (value256 sum) ++ [of_bool (carry256 sum)].

(** ** Modular arithmetic *)

Definition addmod (x y modulus : uint256) : option uint256 :=
  if ((negb (w3 modulus =? 0)) &&
      (w3 x <=? w3 modulus) &&
      (w3 y <=? w3 modulus))%bool
  then
    let x_sub := subb x modulus in
    let x_norm := if carry256 x_sub then x else value256 x_sub in
    let y_sub := subb y modulus in
    let y_norm := if carry256 y_sub then y else value256 y_sub in
    let xy_sum := addc x_norm y_norm in
    let rem := subb (value256 xy_sum) modulus in
    if (carry256 xy_sum || negb (carry256 rem))%bool
    then Some (value256 rem)
    else Some (value256 xy_sum)
  else
    match udivrem 5 4 (add_words_full_uint256 x y)
            (uint256_to_words modulus) with
    | Some r => Some (words_to_uint256 (ud_rem r))
    | None => None
    end.

Definition mulmod (u v modulus : uint256) : option uint256 :=
  let u := uint256_to_words u in
  let v := uint256_to_words v in
  let modulus := uint256_to_words modulus in
  let prod := RM.truncating_mul_runtime u v 8 in
  match udivrem 8 4 prod modulus with
  | Some r => Some (words_to_uint256 (ud_rem r))
  | None => None
  end.

(** ** Signed Division *)

Definition negate_uint256 (x : uint256) : uint256 :=
  value256 (subb zero_uint256 x).

Definition negate_words (ws : words) : words :=
  uint256_to_words (negate_uint256 (words_to_uint256 ws)).

(** Test whether the sign bit (MSB of the top word) is set.
    This models the zero/non-zero information used by
    [x[3] & sign_bit] in the C++ [sdivrem] implementation. *)
Definition sign_bit : t :=
  shl 1 (word_width - 1).

Definition is_negative (x : uint256) : bool :=
  negb (w3 x <? sign_bit).

(** Signed division of [n]-word two's complement integers.
    Converts operands to absolute values, performs unsigned division,
    then adjusts the signs of quotient and remainder.
    C++ ref: uint256.hpp lines 1299-1316. *)
Definition sdivrem (u v : uint256) : option udivrem_result :=
  let u_neg := is_negative u in
  let v_neg := is_negative v in
  let u_abs := if u_neg then negate_uint256 u else u in
  let v_abs := if v_neg then negate_uint256 v else v in
  match udivrem 4 4
          (uint256_to_words u_abs) (uint256_to_words v_abs) with
  | None => None
  | Some result =>
      let quot_neg := xorb u_neg v_neg in
      Some (mk_udivrem_result
        (if quot_neg then negate_words (ud_quot result) else ud_quot result)
        (if u_neg then negate_words (ud_rem result) else ud_rem result))
  end.

(** ** Signed comparison *)

Definition slt (x y : uint256) : bool :=
  let x_neg := negb (shr (w3 x) 63 =? 0) in
  let y_neg := negb (shr (w3 y) 63 =? 0) in
  let diff := xorb x_neg y_neg in
  ((negb diff && ltb_uint256 x y) || (x_neg && negb y_neg))%bool.

(** ** Exponentiation *)

Definition odd_word (x : t) : bool :=
  negb (x =? shl (shr x 1) 1).

Definition two_words_generic (n : nat) : words :=
  set_word (extend_words n) 0 (1 + 1).

Definition one_uint256 : uint256 :=
  mk_uint256 1 0 0 0.

Definition two_uint256 : uint256 :=
  mk_uint256 (1 + 1) 0 0 0.

Definition is_two_uint256 (x : uint256) : bool :=
  ((w0 x =? (1 + 1)) &&
   (w1 x =? 0) &&
   (w2 x =? 0) &&
   (w3 x =? 0))%bool.

Fixpoint exp_sigbit_loop (n bits : nat) (word_exp : t)
    (base result : words) : words * words :=
  match bits with
  | O => (base, result)
  | S bits' =>
      let result' :=
        if odd_word word_exp
        then RM.truncating_mul_runtime result base n
        else result in
      let base' := RM.truncating_mul_runtime base base n in
      exp_sigbit_loop n bits' (shr word_exp 1) base' result'
  end.

Fixpoint exp_words_loop (n : nat) (exponent : words)
    (base result : words) : words :=
  match exponent with
  | [] => result
  | word_exp :: rest =>
      let bits :=
        match rest with
        | [] => (word_width - countl_zero word_exp)%nat
        | _ => word_width
        end in
      let '(base', result') :=
        exp_sigbit_loop n bits word_exp base result in
      exp_words_loop n rest base' result'
  end.

Fixpoint bounded_shift_nat (fuel : nat) (shift : t) : nat :=
  match fuel with
  | O => O
  | S fuel' =>
      if (shift =? 0) then O
      else S (bounded_shift_nat fuel' (shift - 1))
  end.

(* Models C++ operator<<(uint256_t, T). *)
Definition shift_left_uint256_aux (x : uint256) (shift : t) : uint256 :=
  if negb (shift <? shl 1 8) then zero_uint256
  else if shift <? shl 1 7 then
    if shift <? shl 1 6 then
      let s := bounded_shift_nat word_width shift in
      mk_uint256
        (shl (w0 x) s)
        (shld64 (w1 x) (w0 x) s)
        (shld64 (w2 x) (w1 x) s)
        (shld64 (w3 x) (w2 x) s)
    else
      let shift' := shift - shl 1 6 in
      let s := bounded_shift_nat word_width shift' in
      mk_uint256
        0
        (shl (w0 x) s)
        (shld64 (w1 x) (w0 x) s)
        (shld64 (w2 x) (w1 x) s)
  else if shift <? shl (1 + 1 + 1) 6 then
    let shift' := shift - shl 1 7 in
    let s := bounded_shift_nat word_width shift' in
    mk_uint256
      0
      0
      (shl (w0 x) s)
      (shld64 (w1 x) (w0 x) s)
  else
    let shift' := shift - shl (1 + 1 + 1) 6 in
    let s := bounded_shift_nat word_width shift' in
    mk_uint256 0 0 0 (shl (w0 x) s).

(* Models C++ operator<<(uint256_t, uint256_t) wrapper. *)
Definition shift_left_uint256 (x shift : uint256) : uint256 :=
  if ((w1 shift =? 0) &&
      (w2 shift =? 0) &&
      (w3 shift =? 0))%bool
  then shift_left_uint256_aux x (w0 shift)
  else zero_uint256.

Definition filled_uint256 (fill : t) : uint256 :=
  mk_uint256 fill fill fill fill.

Inductive right_shift_kind :=
| RightShiftLogical
| RightShiftArithmetic.

Definition shift_right_uint256_aux (kind : right_shift_kind) (fill : t)
    (x : uint256) (shift : t) : uint256 :=
  let tail_shift := bounded_shift_nat word_width (land shift (shl 1 6 - 1)) in
  let tail :=
    match kind with
    | RightShiftLogical => shr (w3 x) tail_shift
    | RightShiftArithmetic => shrd64 fill (w3 x) tail_shift
    end in
  if shift <? shl 1 7 then
    if shift <? shl 1 6 then
      let s := bounded_shift_nat word_width shift in
      mk_uint256
        (shrd64 (w1 x) (w0 x) s)
        (shrd64 (w2 x) (w1 x) s)
        (shrd64 (w3 x) (w2 x) s)
        tail
    else
      let s := bounded_shift_nat word_width (land shift (shl 1 6 - 1)) in
      mk_uint256
        (shrd64 (w2 x) (w1 x) s)
        (shrd64 (w3 x) (w2 x) s)
        tail
        fill
  else if shift <? shl (1 + 1 + 1) 6 then
    let s := bounded_shift_nat word_width (land shift (shl 1 7 - 1)) in
    mk_uint256
      (shrd64 (w3 x) (w2 x) s)
      tail
      fill
      fill
  else
    mk_uint256 tail fill fill fill.

Definition shift_right_uint256 (x shift : uint256) : uint256 :=
  if ((w1 shift =? 0) &&
      (w2 shift =? 0) &&
      (w3 shift =? 0) &&
      (w0 shift <? shl 1 8))%bool
  then shift_right_uint256_aux RightShiftLogical 0 x (w0 shift)
  else zero_uint256.

Definition sar (shift x : uint256) : uint256 :=
  let fill := if is_negative x then u64_max_val else 0 in
  if ((w1 shift =? 0) &&
      (w2 shift =? 0) &&
      (w3 shift =? 0) &&
      (w0 shift <? shl 1 8))%bool
  then shift_right_uint256_aux RightShiftArithmetic fill x (w0 shift)
  else filled_uint256 fill.

(* Models the suffix fill loop in the C++ signextend implementation:
   for (j = start; j < 4; ++j) ret[j] = v. *)
Fixpoint fill_words_from (ws : words) (start : nat) (v : t) : words :=
  match ws, start with
  | [], _ => []
  | _ :: rest, O => v :: fill_words_from rest O v
  | w :: rest, S start' => w :: fill_words_from rest start' v
  end.

Definition signextend_word_index_nat (word_index : t) : nat :=
  if word_index =? 0 then 0%nat
  else if word_index =? 1 then 1%nat
  else if word_index =? (1 + 1) then 2%nat
  else 3%nat.

Definition signextend_current_word (word : t) (s : nat) : t * t :=
  let shifted := shr word s in
  let signed_byte := asr (shl shifted 56) 56 in
  let upper := shl signed_byte s in
  let lower_mask := shl 1 s - 1 in
  let lower := land word lower_mask in
  let sign_bits := asr signed_byte 63 in
  (or upper lower, sign_bits).

Definition signextend (byte_index_256 x : uint256) : uint256 :=
  if negb (ltb_uint256 byte_index_256
             (mk_uint256 (shl 1 5 - 1) 0 0 0))
  then x
  else
    let byte_index := w0 byte_index_256 in
    let word_index := shr byte_index 3 in
    let word_index_n := signextend_word_index_nat word_index in
    let ws := uint256_to_words x in
    let word := get_word ws word_index_n in
    let bit_index := shl (land byte_index (shl 1 3 - 1)) 3 in
    let s := bounded_shift_nat word_width bit_index in
    let '(current, sign_bits) := signextend_current_word word s in
    let ret := set_word ws word_index_n current in
    words_to_uint256 (fill_words_from ret (S word_index_n) sign_bits).

Definition exp (base exponent : uint256) : uint256 :=
  if is_two_uint256 base
  then shift_left_uint256 one_uint256 exponent
  else
    let sig_words := count_significant_words
                       (uint256_to_words exponent) in
    words_to_uint256
      (exp_words_loop 4
         (firstn sig_words (uint256_to_words exponent))
         (uint256_to_words base)
         (one_words_generic 4)).

End Make.

Module Type ArithmeticSig (B : Base.BaseSig) (U128 : Uint128Ops)
  (Bridge : UintWidenOps B.U64 U128)
  (Div : Division.DivisionSig(B)(U128)(Bridge))
  (RM : RuntimeMul.RuntimeMulSig with Module U64 := B.U64).
Include Make(B)(U128)(Bridge)(Div)(RM).
End ArithmeticSig.

Module MakeLegacy (Import Word64 : Uint64Ops) (U128 : Uint128Ops)
  (Import Bridge : UintWidenOps Word64 U128).
Module B := Base.Make(Word64).
Module Div := Division.Make(B)(U128)(Bridge).
Module RM := RuntimeMul.Make(B).
Include Make(B)(U128)(Bridge)(Div)(RM).
End MakeLegacy.

Module MakeOn := Make.
