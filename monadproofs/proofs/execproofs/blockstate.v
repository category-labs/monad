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
Some of them maybe in the EVMOpSem.evm.variable_ctx struct in the Gallina EVM semantics.
This Record is used in the step function of EVM in the semantics in Gallina.

Monad executes transactions of a block with optimisic concurrency.
The validate_exact_balance_ field denotes whethere the transaction has done some action (e.g. BALANCE opcode) that requires the pre-tx balance to be an exact value instead of just being >= min_balance for the speculative execution to not be invalidated by previous concurrent transactions.

`AccountStateR` should take arguments of type cQp.t, block.block_account, and perhaps also evm.variable_ctx and other possibly new Gallina Record types to represent fields like validate_exact_balance_.
AccountState has a baseclass and includes monad::Account. you will need to define Rep predicates for these as well.
block.block_account and/or evm.variable_ctx may serve as appropriate model types for those as well.

Below are some existing Rep predicates that you can use (in addition to the ones mentioned in the general spec background above):
- IncarnationR is the existing Rep predicate for the c++ class `monad::Incarnation`.
- bytes32R for `bytes32_t` (alias for `evmc::bytes32`).
- u256t for `uint256_t` (alias for `intx::uint<256>`)
- addressR is the Rep predicate for Address (alias for `evmc::address`)

Many of these Rep predicates are currently admitted. You dont need to define them. But their type will tell you the Gallina models of these types.
Unfortunately, there is currently no way to search the Coq context for Rep predicate definitions/axioms for a given C++ type.
So, if a Rep predicate for a class has not been mentioned in this first prompt, you can assume it doesnt exist and you need to define it.

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
Local Open Scope pstring_scope.
Local Open Scope lens_scope.
Local Open Scope Qp_scope.
Local Open Scope cpp_name_scope.
Local Open Scope cpp_type_scope.

(** 1) AccountR for monad::Account **)
Definition AccountR (q: Qp) (i: monad.proofs.exec_specs.Indices) (ba: block.block_account) : Rep :=
  structR "monad::Account"%cpp_name (cQp.mut q)
  ** _field "balance"%cpp_name   |-> (
       u256R q
         (Z.to_N
            (monad.EVMOpSem.Zdigits.binary_value
               256 (monad.EVMOpSem.block.block_account_balance ba))))
  ** _field "code_hash"%cpp_name |-> (bytes32R q 0%N)
  ** _field "nonce"%cpp_name     |-> (
       u256R q
         (Z.to_N
            (monad.EVMOpSem.Zdigits.binary_value
               256 (monad.EVMOpSem.block.block_account_nonce ba))))
  ** _field "incarnation"%cpp_name |-> (IncarnationR q i).

(** 2) AccountSubstateR for monad::AccountSubstate **)
Definition AccountSubstateR (q: Qp)
           (destr touched accessed: bool) : Rep :=
  structR "monad::AccountSubstate"%cpp_name (cQp.mut q)
  ** _field "destructed_"%cpp_name       |-> (boolR (cQp.mut q) destr)
  ** _field "touched_"%cpp_name          |-> (boolR (cQp.mut q) touched)
  ** _field "accessed_"%cpp_name         |-> (boolR (cQp.mut q) accessed)
  ** _field "accessed_storage_"%cpp_name |-> 
       anyR
         "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, void, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<evmc::bytes32>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 0b>"%cpp_type
         (cQp.mut q).

(** 3) AccountStateR for monad::AccountState **)
Definition AccountStateR (q: Qp)
           (i: monad.proofs.exec_specs.Indices)
           (accOpt: option block.block_account)
           (destr touched accessed: bool)
           (validate_nonce validate_balance: bool)
           (minBal: Z) : Rep :=
  structR "monad::AccountState"%cpp_name (cQp.mut q)
  ** (_base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name |-> 
       AccountSubstateR q destr touched accessed)
  ** _field "account_"%cpp_name      |-> 
       monad.proofs.libspecs.optionR
         "monad::Account"%cpp_type
         (AccountR q i)
         q
         accOpt
  ** _field "storage_"%cpp_name     |-> 
       anyR
         "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, evmc::bytes32, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, evmc::bytes32>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"%cpp_type
         (cQp.mut q)
  ** _field "transient_storage_"%cpp_name |-> 
       anyR
         "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, evmc::bytes32, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, evmc::bytes32>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"%cpp_type
         (cQp.mut q)
  ** _field "validate_exact_nonce_"%cpp_name   |-> (boolR (cQp.mut q) validate_nonce)
  ** _field "validate_exact_balance_"%cpp_name |-> (boolR (cQp.mut q) validate_balance)
  ** _field "min_balance_"%cpp_name  |-> (u256R q (Z.to_N minBal)).

About exect. 
Search AssumptionsAndUpdates.
StateR.





  

  
  Print EVMOpSem.evm.account_state.
  Search EVMOpSem.evm.account_killed.
  Print block.block_account.
  Search evm.variable_ctx EVMOpSem.evm.account_state.
Record account_state : Type := Build_account_state
  { account_address : EVMOpSem.evm.address;
    account_storage : evm.storage;
    account_code : evm.program;
    account_balance : keccak.w256;
    account_ongoing_calls : list (evm.variable_ctx * Z * Z);
    account_killed : bool }.




  
  Definition AccountStateR (q:Qp) (s: evm.account_state) : Rep. Proof. Admitted.

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
