Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.block_state_cpp.
Require Import monad.proofs.exec_specs.
Disable Notation atomic_name'.
Require Import Lens.Elpi.Elpi.
#[local] Open Scope lens_scope.
Set Printing FullyQualifiedNames.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : ext.module ⊧ CU}.

  
  
  (**
Monad is a new L1 blockchain that can execute EVM-compative transactions much faster.
The C++ class `monad::AccountState` stores the state of an account while a transaction is being executed.
We need to write `AccountStateR`, its Rep predicate.
First, we need to find an appropriate Gallina model for `monad::AccountState`.
A possibility is to use `monad.EVMOpSem.block.block_account`, which is a type that comes from Yoichi's EVM semantics defined in Coq (via Lem) in 2018. However, this type just represents an account state before the execution of a block.
The C++ class has more fields, which may be only relevant during the execution transaction.
Some of them maybe in the `EVMOpSem.evm.variable_ctx` Record in the Gallina EVM semantics.
This Record is used in the step function of EVM in the semantics in Gallina.

Monad executes transactions of a block with optimisic concurrency.
The validate_exact_balance_ field denotes whethere the transaction has done some action (e.g. BALANCE opcode) that requires the pre-tx balance to be an exact value instead of just being >= min_balance for the speculative execution to not be invalidated by previous concurrent transactions. Use `AssumptionExactness` as a model of those fields: min_balance only makes sense if validate_exact_balance_ is false.

`AccountStateR` should take arguments of type cQp.t, block.block_account, AssumptionExactness,  and perhaps also evm.variable_ctx.
AccountState has a baseclass and includes monad::Account. you will need to define Rep predicates for these as well.
block.block_account and/or evm.variable_ctx may serve as appropriate model types for those as well. The logical information from block.block_account and/or evm.variable_ctx seems to be split across the fields of those 3 classes.
TRY VERY VERY HARD TO FIND THE MODELS OF THE C++ FIELDS IN block.block_account and evm.variable_ctx. YOU MUST NOT ADD A SEPARATE MODEL ARGUMENT FOR ANY FIELD WHICH ALREADY HAS A MODEL IN THOSE GALLINA RECORDS.

Below are some existing Rep predicates that you can use (in addition to the ones mentioned in the general spec background above):
- IncarnationR is the existing Rep predicate for the c++ class `monad::Incarnation`.
- bytes32R for `bytes32_t` (alias for `evmc::bytes32`).
- u256t for `uint256_t` (alias for `intx::uint<256>`)
- addressR is the Rep predicate for Address (alias for `evmc::address`)

Many of these Rep predicates are currently admitted. You dont need to define them. But their type will tell you the Gallina models of these types.
Unfortunately, there is currently no way to search the Coq context for Rep predicate definitions/axioms for a given C++ type.
So, if a Rep predicate for a class has not been mentioned in this first prompt, you can assume it doesnt exist and you need to define it.
You can admit a `MapR` for the storage_ field: but you still need to figure out an appropriate type for MapR. Do not bother to define it generically for the templated Map type: just focus on the concrete instantiation.

+++ FILES
../../fmai/prompts/sep.md
../../fmai/prompts/specs.md

+++ QUERIES

Print evm.account_state.
Print block.block_account.
Print evm.variable_ctx
Print evm.instruction_sem.
Print block.step.
Print IncarnationR.
Print addressR.
Print bytes32R.
Print u256R.
Check Zdigits.binary_value.
Check Zdigits.Z_to_binary.
 *)
 Set Printing FullyQualifiedNames.
(*----------------------------------------------------------------*)
(* A local Rep‐level optionR to shadow iris.cmra.OptionR         *)
(*----------------------------------------------------------------*)
Definition optionR {T:Type}
           (somety: bluerock.lang.cpp.syntax.core.type)
           (r: T -> Rep)
           (q: stdpp.numbers.Qp)
           (o: option T)
         : Rep.
Admitted. (* TOFIXLATER: implement Rep for std::optional<T> *)

(*----------------------------------------------------------------*)
(* Model for the C++ AccountSubstate fields                      *)
(*----------------------------------------------------------------*)
Record AccountSubstateModel : Type := MkASM {
  asm_destructed       : bool;
  asm_touched          : bool;
  asm_accessed         : bool;
  asm_accessed_storage : list monad.EVMOpSem.keccak.w256
}.
Arguments MkASM _ _ _ _.
Arguments asm_destructed _.
Arguments asm_touched _.
Arguments asm_accessed _.
Arguments asm_accessed_storage _.

(*----------------------------------------------------------------*)
(* Admit an extractor from runtime data to our model             *)
(*----------------------------------------------------------------*)
Definition AccountSubstateModel_of
           (oa: option monad.EVMOpSem.block.block_account)
           (vctx: monad.EVMOpSem.evm.variable_ctx)
         : AccountSubstateModel.
Admitted. (* TOFIXLATER: derive destructed_/touched_/accessed_/… from oa/vctx *)

(*----------------------------------------------------------------*)
(* Admit program→bytes32 hash                                     *)
(*----------------------------------------------------------------*)
Definition programHashN
           (p: monad.EVMOpSem.evm.program)
         : Corelib.Numbers.BinNums.N.
Admitted. (* TOFIXLATER: compute keccak256‐hash of the program *)

(*----------------------------------------------------------------*)
(* Extract the Indices needed for IncarnationR                   *)
(*----------------------------------------------------------------*)
Definition Indices_of
           (orig: monad.EVMOpSem.block.block_account)
         : monad.proofs.exec_specs.Indices.
Admitted. (* TOFIXLATER: extract Indices from block_account *)

(*----------------------------------------------------------------*)
(* Map‐table representations for the two unordered_dense tables.  *)
(*----------------------------------------------------------------*)
Definition Table32to32R
           (q: stdpp.numbers.Qp)
           (m: monad.EVMOpSem.evm.storage)
         : Rep.
Admitted. (* TOFIXLATER: flesh out the memory layout for table<bytes32,bytes32> *)

Definition Table32toVoidR
           (q: stdpp.numbers.Qp)
           (ks: list monad.EVMOpSem.keccak.w256)
         : Rep.
Admitted. (* TOFIXLATER: flesh out the memory layout for table<bytes32,void> *)

(*----------------------------------------------------------------*)
(* C++ class monad::AccountSubstate                              *)
(*----------------------------------------------------------------*)
Definition AccountSubstateR
           (q: stdpp.numbers.Qp)
           (mdl: AccountSubstateModel)
           (_vctx: monad.EVMOpSem.evm.variable_ctx)
         : Rep :=
  bluerock.lang.cpp.logic.rep_defs.as_Rep
    (fun this =>
       let rep: Rep :=
         _field "monad::AccountSubstate::destructed_"%cpp_name
           |-> boolR (cQp.mut q) (asm_destructed mdl)
       ** _field "monad::AccountSubstate::touched_"%cpp_name
           |-> boolR (cQp.mut q) (asm_touched mdl)
       ** _field "monad::AccountSubstate::accessed_"%cpp_name
           |-> boolR (cQp.mut q) (asm_accessed mdl)
       ** _field "monad::AccountSubstate::accessed_storage_"%cpp_name
           |-> Table32toVoidR q (asm_accessed_storage mdl)
       ** structR "monad::AccountSubstate"%cpp_name (cQp.mut q)
       in rep this).

(*----------------------------------------------------------------*)
(* C++ class monad::Account                                      *)
(*----------------------------------------------------------------*)
Definition AccountR
           (q: stdpp.numbers.Qp)
           (orig: monad.EVMOpSem.block.block_account)
           (im: monad.proofs.exec_specs.Indices) 
         : Rep :=
  bluerock.lang.cpp.logic.rep_defs.as_Rep
    (fun this =>
       (* extract balance *)
       let bal_z    := Zdigits.binary_value 256 (monad.EVMOpSem.block.block_account_balance orig) in
       let bal_n    := Z.to_N bal_z in
       (* extract nonce *)
       let nonce_z  := Zdigits.binary_value 256 (monad.EVMOpSem.block.block_account_nonce orig) in
       let nn_nonce := Z.to_N nonce_z in
       let rep :=
         _field "monad::Account::balance"%cpp_name
           |-> u256R q bal_n
       ** _field "monad::Account::code_hash"%cpp_name
           |-> bytes32R q (programHashN (monad.EVMOpSem.block.block_account_code orig))
       ** _field "monad::Account::nonce"%cpp_name
           |-> primR "unsigned long"%cpp_type (cQp.mut q) nn_nonce
       ** _field "monad::Account::incarnation"%cpp_name
           |-> IncarnationR q im
       ** structR "monad::Account"%cpp_name (cQp.mut q)
       in rep this).

(*----------------------------------------------------------------*)
(* C++ class monad::AccountState                                 *)
(*----------------------------------------------------------------*)
Definition AccountStateR
           (q: stdpp.numbers.Qp)
           (oa: option monad.EVMOpSem.block.block_account)
           (ax: AssumptionExactness)
           (vctx: monad.EVMOpSem.evm.variable_ctx)
         : Rep :=
  bluerock.lang.cpp.logic.rep_defs.as_Rep
    (fun this =>
       let rep :=
         (_base "monad::AccountState"%cpp_name
                "monad::AccountSubstate"%cpp_name
           |-> AccountSubstateR q
                                (AccountSubstateModel_of oa vctx)
                                vctx)
       ** _field "account_"%cpp_name
           |-> optionR "std::optional<monad::Account>"%cpp_type
                     (fun b => AccountR q b (Indices_of b))
                     q
                     oa
       ** _field "storage_"%cpp_name
           |-> Table32to32R q (monad.EVMOpSem.evm.vctx_storage vctx)
       ** _field "transient_storage_"%cpp_name
           |-> Table32to32R q (monad.EVMOpSem.evm.vctx_storage_at_call vctx)
       ** _field "validate_exact_nonce_"%cpp_name
           |-> boolR (cQp.mut q)
                      (match ax with _ => (* TOFIXLATER: proj flag *) false end)
       ** _field "validate_exact_balance_"%cpp_name
           |-> boolR (cQp.mut q)
                      (match ax with _ => (* TOFIXLATER: proj flag *) false end)
       ** _field "min_balance_"%cpp_name
           |-> u256R q
                      (match ax with _ => (* TOFIXLATER: proj min_balance *) 0%N end)
       ** structR "monad::AccountState"%cpp_name (cQp.mut q)
       in rep this).




  
  Definition AccountStateR (q:Qp) (s: evm.account_state) : Rep. Proof. Admitted.
  Print addressR.
  cpp.spec "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const" as fix_spec with (fun this:ptr =>
   \prepost{preBlockState g au actualPreTxState} (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
   \pre [| blockStatePtr au = this |]
   \arg{statep: ptr} "state" (Vref statep)
   \pre{au}  statep |-> StateR au
   \arg{addrp: ptr} "address" (Vref addrp)
   \prepost{qa fixee} addrp |-> addressR qa fixee
   \arg{origp: ptr} "original" (Vref origp)
   \pre{assumedFixeeState} origp |-> AccountStateR 1 assumedFixeeState
   \arg{actualp: ptr} "actual" (Vref actualp)
   \pre actualp |-> libspecs.optionR "monad::AccountState" (AccountStateR 1) 1 (actualPreTxState !! fixee)
   \post{satisfiesAssumptionsb:bool} [Vbool satisfiesAssumptionsb]
      [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **
      if (negb satisfiesAssumptionsb)
      then statep |-> StateR au ** origp |-> AccountStateR 1 assumedFixeeState
      else
        Exists auf exactFixeeAssumption, statep |-> StateR auf
          ** origp |-> AccountStateR 1 exactFixeeAssumption
          ** [| relaxedValidation auf = false |]
          ** [| applyUpdates auf actualPreTxState = applyUpdates au actualPreTxState |]).

  Set Nested Proofs Allowed.
  Lemma observeState (state_addr:ptr) q t:
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> AccountStateR q t).
  Proof using. Admitted.

  Definition observeStateF r q t := @observe_fwd _ _ _ (observeState r q t).
  Hint Resolve observeStateF : br_opacity.
Ltac slauto := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id; try solveRefereceTo)); try iPureIntro.

Lemma prf: denoteModule module |-- fix_spec.
Proof using.
  verify_spec'.
  slauto.
Abort.
(*
  Locate RepFor.
  Print rep.RepFor.C.
  go.
  slauto2
  iAssert (origp |-> structR "monad::AccountState" 1) as "?"%string. admit.
  admitRef
  go.

    go.
*)
End with_Sigma.

