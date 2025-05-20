Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import monad.proofs.misc.
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.tutorials.demo2.
Require Import monad.tutorials.demomisc.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import stdpp.list.
Import stdpp.decidable.
Import cQp_compat.
Open Scope cQp_scope.
Open Scope Z_scope.
Import linearity.
Import Verbose.
Ltac slauto := misc.slauto1.
Disable Notation take.
Disable Notation drop.
Disable Notation "`div`" (all).
Disable Notation intR.
Disable Notation uintR.
Import linearity.
Disable Notation atomic_name'.
Disable Notation atomic_name.
Open Scope pstring_scope.
Set Printing FullyQualifiedNames.


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.
  Coercion cQpc : Qp >-> cQp.t.

  Open Scope Z_scope.

(*
Write a Rep predicate for the following C++ class and a spec for the add method.

```c++
class uint256 {
public:
  using limb_t = unsigned long long;          // assumes 64-bit limbs
  limb_t data[4];                             // little-endian: data[0] is least-significant

  uint256() : data{0, 0, 0, 0} {}

  void add(const uint256& other);
};
```

+++ FILES
../../fmai/prompts/sep.md
../../fmai/prompts/specs.md

+++ QUERIES
Check "unsigned long long"%cpp_type.

 *)
(* ---------------------------------------------------------------------- *)
(** Pure Gallina helpers to compute 256‐bit addition on four 64‐bit limbs *)

Definition two64 : Z := (2 ^ 64)%Z.

Definition add_limbs (a b carry: Z) : Z * Z :=
  let s := a + b + carry in
  (Z.rem s two64, Z.quot s two64).

Definition add_uint256 (a0 a1 a2 a3 b0 b1 b2 b3: Z) : Z * Z * Z * Z :=
  let '(s0, c0) := add_limbs a0 b0 0  in
  let '(s1, c1) := add_limbs a1 b1 c0 in
  let '(s2, c2) := add_limbs a2 b2 c1 in
  let '(s3, c3) := add_limbs a3 b3 c2 in
  (s0, s1, s2, s3).

(* ---------------------------------------------------------------------- *)
(** The [Rep] predicate for [class uint256], parameterized by a fraction
    [q] and the four Z‐valued limbs [v0..v3] (little‐endian).             *)

Definition uint256R (q: cQp.t) (v0 v1 v2 v3: Z) : Rep :=
  _field "uint256::data"
    |-> bluerock.lang.cpp.logic.arr.arrayR
           ("unsigned long long"%cpp_type)
           (primR ("unsigned long long"%cpp_type) q)
           [Vint v0; Vint v1; Vint v2; Vint v3]
  ** structR "uint256" q.

(* ---------------------------------------------------------------------- *)
(** Spec of the member function
     void uint256::add(const uint256& other);
    which does  this := this + other  modulo 2^256.                   *)

cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun this =>
  (* the [other] parameter is passed by reference *)
  \arg{oth} "other" (Vptr oth)
  (* pre: full ownership of both 256‐bit values *)
  \pre{(a0:Z) (a1:Z) (a2:Z) (a3:Z)
        (b0:Z) (b1:Z) (b2:Z) (b3:Z)}
    this |-> uint256R (cQp.mut 1) a0 a1 a2 a3
    ** oth  |-> uint256R (cQp.mut 1) b0 b1 b2 b3
  (* post: full ownership of [this], now equal to the sum *)
  \post{(r0:Z) (r1:Z) (r2:Z) (r3:Z)}
    this |-> uint256R (cQp.mut 1) r0 r1 r2 r3
    ** [| (r0, r1, r2, r3) = add_uint256 a0 a1 a2 a3 b0 b1 b2 b3 |]
).




