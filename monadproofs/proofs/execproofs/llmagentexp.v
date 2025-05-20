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
(** 256‐bit unsigned integers as four little‐endian 64‐bit limbs *)
Definition uint256R (q: cQp.t) (v: Z) : Rep :=
  (* require that the mathematical value is in range 0 .. 2^256-1 *)
  [| 0 ≤ v < (2 ^ (64 * 4))%Z |]
  ** arrayR "unsigned long long"%cpp_type
       (fun l => primR "unsigned long long"%cpp_type q (Vint l))
       [ Z.land    v                ((2 ^ 64 - 1)%Z)
       ; Z.land (Z.shiftr v 64)     ((2 ^ 64 - 1)%Z)
       ; Z.land (Z.shiftr v 128)    ((2 ^ 64 - 1)%Z)
       ; Z.land (Z.shiftr v 192)    ((2 ^ 64 - 1)%Z)
       ].

(** spec of uint256::add in place:  this->v := (this->v + other.v) mod 2^256 *)
cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (this:ptr) =>
  \arg{otherPtr:ptr} "other" (Vptr otherPtr)
  \pre{(v1:Z) (v2:Z)}
     this     |-> uint256R (cQp.mut 1) v1
  ** otherPtr |-> uint256R (cQp.mut 1) v2
  \post
     this     |-> uint256R (cQp.mut 1) (Z.modulo (v1 + v2) (2 ^ (64*4))%Z)
  ** otherPtr |-> uint256R (cQp.mut 1) v2
).

Search (bluerock.auto.cpp.database.spec.SpecFor.C "uint256::add(const uint256&)").


