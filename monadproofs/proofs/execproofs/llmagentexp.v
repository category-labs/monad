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

