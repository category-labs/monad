Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import monad.proofs.misc.
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.tutorials.demo.
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



Definition foo1: nat :=1.
  Axiom foo: nat.
  Inductive bar :=
    |foot.


```gallina
  Definition foo1: nat :=1.
  Axiom foo: nat.
  Inductive bar :=
    |foot.

  ```
    messages buffer:
axioms: (foo)
    


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Coercion cQpc : Qp >-> cQp.t.

  Open Scope Z_scope.
  Set Nested Proofs Allowed.
  Axiom foo: nat.
  Definition foo1: nat :=1.
  Inductive bar :=
    |foot.


(*
Write a spec in Coq for the following C++ function (using cpp.spec):
```c++
void swap(int* p, int* q) {
  auto t = *p;
  *p = *q;
  *q = t;
}
```

+++ FILES
../../fmai/prompts/sep.md
../../fmai/prompts/specs.md

*)
cpp.spec "swap(int*, int*)" as swap_spec with (
  \arg{(p1:ptr) (q1:ptr)} "p" (Vptr p1)
  \arg           "q" (Vptr q1)
  \pre{(x:Z) (y:Z)}
    p1 |-> primR "int" (cQp.mut 1) (Vint x)
  ** q1 |-> primR "int" (cQp.mut 1) (Vint y)
  \post
    p1 |-> primR "int" (cQp.mut 1) (Vint y)
  ** q1 |-> primR "int" (cQp.mut 1) (Vint x)
).
 End LLMSOLN.















Print val.

Print WpSpec.


