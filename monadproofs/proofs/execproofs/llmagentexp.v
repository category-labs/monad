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
Ensure that the Rep predicate only takes 1 Gallina Z as the "mathematical model" argument, not 4 Zs.

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
(* shorthand for the 64-bit limb type *)
Notation ull := "unsigned long long"%cpp_type.

(* split a 256-bit integer into four 64-bit limbs, little-endian *)
Definition limbs_of_uint256 (n: Z) : list Z :=
  let tw := (2 ^ 64)%Z in
  [ Z.modulo n tw;
    Z.modulo (Z.div n tw) tw;
    Z.modulo (Z.div n (tw * tw)%Z) tw;
    Z.modulo (Z.div n (tw * tw * tw)%Z) tw ].

(* the Rep for uint256 *)
Definition uint256R (q: cQp.t) (n: Z) : Rep :=
  arrayR ull (fun i => primR ull q (Vint i)) (limbs_of_uint256 n).

(* spec for: void uint256::add(const uint256&) *)
cpp.spec "uint256::add(uint256 const &)" as uint256_add_spec with (fun (this: ptr) =>
  (* incoming operand *)
  \arg{otherPtr} "other" (Vptr otherPtr)
  (* preserve whatever fraction q_other of “other” the client passed in *)
  \prepost{n_other q_other} otherPtr |-> uint256R (cQp.mut q_other) n_other
  (* full ownership of *this, old value n_self *)
  \pre{n_self} this |-> uint256R (cQp.mut 1) n_self
  (* result: *this holds the sum modulo 2^256, other unchanged *)
  \post this |-> uint256R (cQp.mut 1) ((n_self + n_other) mod (2 ^ 256))%Z
).


