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
(* Rep‐predicate for uint256: just one Z-model, not four separate limbs. *)
Definition uint256R (q: cQp.t) (x: Z) : Rep :=
  let mask := (2^64)%Z in
  let l0 := (x mod mask)%Z in
  let l1 := (Z.div x mask mod mask)%Z in
  let l2 := (Z.div x (mask*mask) mod mask)%Z in
  let l3 := (Z.div x (mask*mask*mask) mod mask)%Z in
  (* the four‐element little‐endian array in data[], plus the struct tag *)
  _field "::uint256::data" |-> bluerock.lang.cpp.logic.arr.arrayR
     "unsigned long long"%cpp_type
     (fun limb => primR "unsigned long long"%cpp_type q (Vint limb))
     [l0; l1; l2; l3]
  ** structR "uint256" q.

(* Separation‐logic spec for uint256::add(const uint256&). *)
  cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (thisp: ptr) =>
     (* bind the actual C++ reference argument plus its model Z and fraction *)
     \arg{(othersp:ptr) (xother:Z) (q:Qp)} "other" (Vptr othersp)
     (* model for 'this' only Z, full ownership so we use \prepost *)
     \prepost{(xv:Z)} thisp |-> uint256R (cQp.mut 1) xv
     (* precondition also needs fractional read‐only ownership of 'other' *)
     \pre othersp |-> uint256R (cQp.mut q) xother
     (* postcondition: 'this' has been updated to xv+xother mod 2^256 *)
     \post thisp |-> uint256R (cQp.mut 1) ((xv + xother) mod (2^256)%Z)
   ).


