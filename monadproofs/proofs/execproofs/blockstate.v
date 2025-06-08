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


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : ext.module ⊧ CU}.

  (**
Monad is a new L1 blockchain that can execute EVM-compative transactions much faster.
The C++ class `monad::AccountState` stores the state of an account while a transaction is being executed.
`monad::State` defines the state of the whole blockchain during the (possibly speculative) execution of a transaction.
The Gallina model type for `model::State` is `AssumptionsAndUpdates`.
The field C++ `original_` records the accounts that have been read during the execution.
Monad executes transactions of a block with optimisic concurrency.
In original_ in, monad::AccountState,  the validate_exact_balance_ field denotes whethere the transaction has done some action (e.g. BALANCE opcode) that requires the pre-tx balance to be an exact value instead of just being >= min_balance (e.g. CALL) for the speculative execution to not be invalidated by previous concurrent transactions.
In `monad::State`, relaxed_validation is false if the execution is not speculative and all previous transactions are known to have finished, in which case, the underlying BlockState is guaranted to have the preTx state, and not be lagging bahind.

You need to redefine StateR, the Rep predicate for `monad::State`
StateR is already a stub Rep predicate for `monad::State`. It has been defined in another file.
Redefine it here properly.


Below are some existing Rep predicates that you can use (in addition to the ones mentioned in the general spec background above):
- IncarnationR is the existing Rep predicate for the c++ class `monad::Incarnation`.
- bytes32R for `bytes32_t` (alias for `evmc::bytes32`).
- u256t for `uint256_t` (alias for `intx::uint<256>`)
- addressR is the Rep predicate for Address (alias for `evmc::address`)
- AccountR is the Rep predicate for monad::Account
- AccountSubstateR is the Rep predicate for monad::AccountSubState
- AccountStateR is the Rep predicate for monad::AccountState


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
Print AssumptionExactness.
Print AccountStateR.
Print AccountSubstateR.
Print AccountR.
Print StateR.
Print AssumptionsAndUpdates.
Search AssumptionsAndUpdates.
   *)

  #[only(lens)] derive AssumptionExactness. (* TODO: move to decl *)

  cpp.spec "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const" as fix_spec with (fun this:ptr =>
   \prepost{preBlockState g au actualPreTxState} (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
   \pre [| blockStatePtr au = this |]
   \arg{statep: ptr} "state" (Vref statep)
   \pre{au}  statep |-> StateR au
   \arg{addrp: ptr} "address" (Vref addrp)
   \prepost{qa fixee} addrp |-> addressR qa fixee
   \arg{origp: ptr} "original" (Vref origp)
   \pre{assumedFixeeState ae inds} origp |-> AccountStateR 1 assumedFixeeState ae inds
   \arg{actualp: ptr} "actual" (Vref actualp)
   \pre actualp |-> libspecs.optionR "monad::AccountState" (fun acs => AccountStateR 1 acs ae inds) 1 (actualPreTxState !! fixee)
   \post{satisfiesAssumptionsb:bool} [Vbool satisfiesAssumptionsb]
      [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **
      if (negb satisfiesAssumptionsb)
      then statep |-> StateR au ** origp |-> AccountStateR 1 assumedFixeeState ae inds
      else
        Exists auf exactFixeeAssumption, statep |-> StateR auf
          ** origp |-> AccountStateR 1 exactFixeeAssumption (ae &: _min_balance .= None) inds
          ** [| relaxedValidation auf = false |]
          ** [| applyUpdates auf actualPreTxState = applyUpdates au actualPreTxState |]).

  Set Nested Proofs Allowed.
  Lemma observeState (state_addr:ptr) q t ae inds:
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> AccountStateR q t ae inds).
  Proof using. Admitted.

  Definition observeStateF r q t a b:= @observe_fwd _ _ _ (observeState r q t a b).
  Hint Resolve observeStateF : br_opacity.
  
Ltac slauto := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id; try solveRefereceTo)); try iPureIntro.

Lemma prf: verify[module] fix_spec.
Abort.

  (*
"ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator!=<0b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>&) const"%cpp_name


"ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::end()"%cpp_name


"monad::AccountState::min_balance() const"%cpp_name


"monad::VersionStack<monad::AccountState>::recent()"%cpp_name


"monad::State::relaxed_validation() const"%cpp_name


"monad::VersionStack<monad::AccountState>::size() const"%cpp_name


"monad::AccountState::validate_exact_balance() const"%cpp_name


"monad::AccountState::validate_exact_nonce() const"%cpp_name


"monad::is_dead(const std::optional<monad::Account>&)"%cpp_name


"ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::find(const evmc::address&)"%cpp_name


"monad::Incarnation::Incarnation(const monad::Incarnation&)"%cpp_name


"intx::uint<256u>::~uint()"%cpp_name


"ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::~iter_t()"%cpp_name


"std::optional<monad::Account>::operator->()"%cpp_name


"std::optional<monad::Account>::operator->() const"%cpp_name


"ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator->() const"%cpp_name


"intx::uint<256u>::operator=(const intx::uint<256u>&)"%cpp_name


"intx::uint<256u>::operator+=(const intx::uint<256u>&)"%cpp_name


"intx::uint<256u>::operator-=(const intx::uint<256u>&)"%cpp_name


"intx::operator-(const intx::uint<256u>&, const intx::uint<256u>&)"%cpp_name


"intx::operator==(const intx::uint<256u>&, const intx::uint<256u>&)"%cpp_name


"intx::operator<(const intx::uint<256u>&, const intx::uint<256u>&)"%cpp_name


"intx::operator>(const intx::uint<256u>&, const intx::uint<256u>&)"%cpp_name


"intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&)"%cpp_name


"evmc::operator!=(const evmc::bytes32&, const evmc::bytes32&)"%cpp_name


"monad::operator==(monad::Incarnation, monad::Incarnation)"%cpp_name


"std::optional<monad::Account>::operator bool() const"%cpp_name
- : unit = ()

   *)
  

  (*
Error: This expression has type Init.constr but an expression was expected of type
Init.preterm
*)
  
  bluerock.auto.cpp.cpp_proof.

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



(*
Class RepFor `{Σ : cpp_logic} {σ : genv} (ty : type) {RepType : Type} (R: RepType) : Prop := {}.
*)
