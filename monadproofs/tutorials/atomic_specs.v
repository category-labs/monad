Require Import monad.tutorials.demo2.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.proofs.misc.
Require Import monad.tutorials.demomisc.
Require Import monad.tutorials.demoprf.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Import Verbose.
Import linearity.

Notation memory_order_seq_cst := 5.

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.

(*
Hint Resolve learn_atomic_val : br_opacity.
*)  
  Open Scope Z_scope.
  Set Nested Proofs Allowed.


    #[ignore_errors]
    cpp.spec "std::__atomic_base<int>::exchange(int, enum std::memory_order)"  as int_exchange_spec with
            (λ this : ptr,
       \arg{(x : Z)} "v" (Vint x)
       \arg "order" (Vint memory_order_seq_cst)
       \let pd := this ,, o_derived CU "std::__atomic_base<int>" "std::atomic<int>"  
       \pre{Q : Z → mpred}
         AC1 << ∀ y : Z, pd |-> atomicR "int" (cQp.mut 1) (Vint y)>> @ ⊤, ∅
            << pd |-> atomicR "int" (cQp.mut 1) (Vint x), COMM Q y >> 
       \post{y : Z}[Vint y]
       Q y).

    #[ignore_errors]
    cpp.spec "std::__atomic_base<int>::load(enum std::memory_order) const"  as int_load_spec with
            (λ this : ptr,
       \let pd := this ,, o_derived CU "std::__atomic_base<int>" "std::atomic<int>"  
       \arg "order" (Vint memory_order_seq_cst)
       \pre{ (q:Qp) (InvOut : Z → mpred)}
         AC1 << ∀ y : Z, pd |-> atomicR "int" q (Vint y)>> @ ⊤, ∅
                      << pd |-> atomicR "int" q (Vint y), COMM InvOut y >> 
       \post{y : Z}[Vint y]
       InvOut y).
    
    #[ignore_errors]
    cpp.spec "std::__atomic_base<unsigned int>::load(enum std::memory_order) const"  as uint_load_spec with
            (λ this : ptr,
       \let pd := this ,, o_derived CU "std::__atomic_base<unsigned int>" "std::atomic<unsigned int>"  
       \arg "order" (Vint memory_order_seq_cst)
       \pre{ (q:Qp) (InvOut : Z → mpred)}
         AC1 << ∀ y : Z, pd |-> atomicR "unsigned int" q (Vint y)>> @ ⊤, ∅
                      << pd |-> atomicR "unsigned int" q (Vint y), COMM InvOut y >> 
       \post{y : Z}[Vint y]
       InvOut y).
    
    #[ignore_errors]
    cpp.spec "std::atomic<bool>::exchange(bool, enum std::memory_order)"  as exchange_spec with
            (λ this : ptr,
       \arg{(x : bool)} "v" (Vbool x)
       \arg "order" (Vint memory_order_seq_cst)
       \pre{Q : bool → mpred}
         AC1 << ∀ y : bool, this |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
            << this |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q y >> 
       \post{y : bool}[Vbool y]
       Q y).
    
    #[ignore_errors]
    cpp.spec "std::atomic<bool>::store(bool, enum std::memory_order)"  as store_spec with
        (λ this : ptr,
       \arg{(Q : mpred) (x : bool)} "v" (Vbool x)
       \arg "memorder" (Vint 5)
       \pre
         AC1 << ∀ y : bool, this |-> atomicR Tbool (cQp.mut 1) (Vbool y)>> @ ⊤, ∅
            << this |-> atomicR Tbool (cQp.mut 1) (Vbool x), COMM Q >> 
       \post    Q).

    #[ignore_errors]
    cpp.spec "std::__atomic_base<int>::store(int, enum std::memory_order)"  as int_store_spec with
        (λ this : ptr,
       \arg{(Q : mpred) (x : Z)} "v" (Vint x)
       \let pd := this ,, o_derived CU "std::__atomic_base<int>" "std::atomic<int>"  
       \arg "memorder" (Vint 5)
       \pre
         AC1 << ∀ y : Z, pd |-> atomicR "int" 1 (Vint y)>> @ ⊤, ∅
            << pd |-> atomicR "int" 1 (Vint x), COMM Q >> 
       \post Q).

    #[ignore_errors]
    cpp.spec "std::__atomic_base<unsigned int>::store(unsigned int, enum std::memory_order)"  as uint_store_spec with
        (λ this : ptr,
       \arg{(Q : mpred) (x : Z)} "v" (Vint x)
       \let pd := this ,, o_derived CU "std::__atomic_base<unsigned int>" "std::atomic<unsigned int>"  
       \arg "memorder" (Vint 5)
       \pre
         AC1 << ∀ y : Z, pd |-> atomicR "unsigned int" 1 (Vint y)>> @ ⊤, ∅
            << pd |-> atomicR "unsigned int" 1 (Vint x), COMM Q >> 
       \post Q).
End with_Sigma.
