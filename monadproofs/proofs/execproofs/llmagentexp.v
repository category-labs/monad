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


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Coercion cQpc : Qp >-> cQp.t.

  Open Scope Z_scope.

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
  \arg{ploc:ptr} "p" (Vptr ploc)
  \arg{qloc:ptr} "q" (Vptr qloc)
  \pre{pval:Z} ploc |-> primR "int"%cpp_type (cQp.mut 1) pval
  \pre{qval:Z} qloc |-> primR "int"%cpp_type (cQp.mut 1) qval
  \post ploc |-> primR "int"%cpp_type (cQp.mut 1) qval
        ** qloc |-> primR "int"%cpp_type (cQp.mut 1) pval
).
Search (bluerock.auto.cpp.database.spec.SpecFor.C "swap(int*, int* )").

(* cpp.spec declares the following instance, which can be used for search
Print swap_spec_spec_instance.
Search (bluerock.auto.cpp.database.spec.SpecFor.C "swap(int*, int* )").
*)













