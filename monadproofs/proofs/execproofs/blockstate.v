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
Open Scope N_scope.
Open Scope Z_scope.
Open Scope Qp_scope.
Open Scope cpp_type_scope.
Open Scope cpp_name_scope.

(** We represent each ankerl::unordered_dense::table merely by its structR,
    deferring any real map‐or set‐contents rep to future work. *)
Definition StorageSetR (q : cQp.t) (_keys : list Corelib.Numbers.BinNums.N) : Rep :=
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, void, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<evmc::bytes32>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 0b>"%cpp_name
    q.

Definition MapR (q : cQp.t) (_m : list (Corelib.Numbers.BinNums.N * Corelib.Numbers.BinNums.N)) : Rep :=
  structR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, evmc::bytes32, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, evmc::bytes32>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"%cpp_name
    q.

(** Rep predicate for the base class monad::AccountSubstate *)
Definition AccountSubstateR (q : cQp.t)
           (destructed touched accessed : bool)
           (accessed_keys : list Corelib.Numbers.BinNums.N) : Rep :=
  _field "monad::AccountSubstate::destructed_"      |-> primR "bool" q (Vbool destructed)   **
  _field "monad::AccountSubstate::touched_"         |-> primR "bool" q (Vbool touched)      **
  _field "monad::AccountSubstate::accessed_"        |-> primR "bool" q (Vbool accessed)     **
  _field "monad::AccountSubstate::accessed_storage_"|-> StorageSetR q accessed_keys        **
  structR "monad::AccountSubstate"%cpp_name q.

(** A packed Gallina‐model for monad::Account fields: 
    (balance,code_hash) × (nonce,incarnation) *)
Definition AccountSomeModel : Type :=
  ((Corelib.Numbers.BinNums.N * Corelib.Numbers.BinNums.N)%type
     * (Corelib.Numbers.BinNums.N * monad.proofs.exec_specs.Indices)%type)%type.

(** How we lay out that packed model in memory *)
Definition AccountSomeRep (q : cQp.t) (m : AccountSomeModel) : Rep :=
  let '(bc, ni) := m in
  let '(bal, codeh) := bc in
  let '(nonce, inc) := ni in
  _field "monad::Account::balance"     |-> u256R    q bal       **
  _field "monad::Account::code_hash"   |-> bytes32R q codeh     **
  _field "monad::Account::nonce"       |-> primR "unsigned long" q (Vint (Z.of_N nonce)) **
  _field "monad::Account::incarnation" |-> IncarnationR q inc    **
  structR "monad::Account"%cpp_name q.

(** The full Rep predicate for AccountState *)
Definition AccountStateR (q : cQp.t)
           (destructed touched accessed : bool)
           (accessed_keys : list Corelib.Numbers.BinNums.N)
           (account_opt : option AccountSomeModel)
           (storage_map transient_map : list (Corelib.Numbers.BinNums.N * Corelib.Numbers.BinNums.N))
           (validate_exact_nonce validate_exact_balance : bool)
           (min_balance : Corelib.Numbers.BinNums.N) : Rep :=
  (* base‐class subobject *)
  _base "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
    |-> AccountSubstateR q destructed touched accessed accessed_keys          **
  (* optional embedded Account *)
  _field "monad::AccountState::account_"  
    |-> monad.proofs.libspecs.optionR
          "monad::Account"%cpp_type (AccountSomeRep q) q account_opt        **
  (* main storage tables *)
  _field "monad::AccountState::storage_" 
    |-> MapR q storage_map                                             **
  _field "monad::AccountState::transient_storage_"
    |-> MapR q transient_map                                          **
  (* validation flags *)
  _field "monad::AccountState::validate_exact_nonce_" 
    |-> primR "bool" q (Vbool validate_exact_nonce)                   **
  _field "monad::AccountState::validate_exact_balance_"
    |-> primR "bool" q (Vbool validate_exact_balance)                 **
  (* minimum balance field *)
  _field "monad::AccountState::min_balance_"
    |-> u256R q min_balance                                           **
  structR "monad::AccountState"%cpp_name q.


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

