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
Definition uint256R (q: cQp.t) (x: Z) : Rep :=
  let two64   := Z.pow 2 64 in
  let two128  := Z.pow 2 128 in
  let two192  := Z.pow 2 192 in
  let l0 := (x mod two64)%Z in
  let l1 := (x / two64   mod two64)%Z in
  let l2 := (x / two128  mod two64)%Z in
  let l3 := (x / two192  mod two64)%Z in
  arrayR "unsigned long long"%cpp_type
         (fun v:Z => primR "unsigned long long"%cpp_type q (Vint v))
         [l0; l1; l2; l3].

(* spec of uint256::add(const uint256&) *)
cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (this:ptr) =>
  (* the single reference parameter *)
  \arg{otherp} "other" (Vptr otherp)

  (* we need full ownership of [this] to write, but only any positive
     fraction of [other] since we only read it *)
  \prepost{(x xother:Z) (q:Qp)}
    this   |-> uint256R (cQp.mut 1) x
    ** otherp |-> uint256R (cQp.mut q) xother

  (* post: [this] now contains the sum mod 2^256, other is returned unchanged *)
  \post
    this |-> uint256R (cQp.mut 1) (Z.modulo (x + xother) (Z.pow 2 256))
).

(* lets look a the o4-mini conversation history that resulted in the above soln *)

