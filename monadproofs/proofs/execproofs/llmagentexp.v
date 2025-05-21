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
Notation ull := "unsigned long long"%cpp_type.

Definition limbs256 (n: Z) : list Z :=
  let base := (2 ^ 64)%Z in
  let l0 := Z.modulo n base in
  let n1 := Z.div n base in
  let l1 := Z.modulo n1 base in
  let n2 := Z.div n1 base in
  let l2 := Z.modulo n2 base in
  let n3 := Z.div n2 base in
  let l3 := Z.modulo n3 base in
  [l0; l1; l2; l3].

Definition uint256R (q: cQp.t) (n: Z) : Rep :=
  _field "uint256::data" |-> arrayR ull (fun v => primR ull q (Vint v)) (limbs256 n)
  ** structR "uint256" q.

(* Spec of the in‐place adder *)
cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (this: ptr) =>
  \arg{otherPtr: ptr} "other" (Vptr otherPtr)
  \pre{(n1: Z) (n2: Z) (q2: Qp)}
    this    |-> uint256R (cQp.mut 1)    n1
  ** otherPtr |-> uint256R (cQp.mut q2) n2
  \post
    this    |-> uint256R (cQp.mut 1) (Z.modulo (n1 + n2) (2 ^ 256)%Z)
  ** otherPtr |-> uint256R (cQp.mut q2) n2
).


