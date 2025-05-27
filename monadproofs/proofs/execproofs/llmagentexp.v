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

 *)
(* uint256R q n  describes a 256‐bit little‐endian
   uint256 whose mathematical value is n mod 2^256,
   stored as data[0..3] of 64‐bit unsigned limbs. *)
Definition uint256R (q: cQp.t) (n: Z) : Rep :=
  _field "uint256::data"%cpp_name
    |-> arrayR "unsigned long long"%cpp_type
         (fun d => primR "unsigned long long"%cpp_type q (Vint d))
         [ Z.modulo n                (Z.pow 2 64);
           Z.modulo (Z.div n  (Z.pow 2 64))  (Z.pow 2 64);
           Z.modulo (Z.div n  (Z.pow 2 128)) (Z.pow 2 64);
           Z.modulo (Z.div n  (Z.pow 2 192)) (Z.pow 2 64) ].

(* Spec for void uint256::add(const uint256& other); *)
cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (this: ptr) =>
  (* argument ‘other’ passed as a pointer *)
  \arg{otherLoc: ptr} "other" (Vptr otherLoc)

  (* full ownership of [this], modelling old value n1 *)
  \pre{(n1: Z)} this  |-> uint256R (cQp.mut 1) n1

  (* read‐only fractional ownership of ‘other’, unchanged by the call *)
  \prepost{(n2: Z) (q: Qp)} otherLoc |-> uint256R (cQp.mut q) n2

  (* after return, [this] = (n1+n2) mod 2^256, with full ownership again *)
  \post this  |-> uint256R (cQp.mut 1) (Z.modulo (n1 + n2) (Z.pow 2 256))
).



