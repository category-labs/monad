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
TRY VERY VERY HARD TO FIND THE MODELS OF THE C++ FIELDS IN block.block_account and evm.variable_ctx. YOU MUST NOT ADD A SEPARATE MODEL ARGUMENT FOR ANY FIELD WHICH ALREADY HAS A MODEL IN THOSE GALLINA RECORDS. block.block_account has the balance/nonce info to serve as the model for those fields in `monad::Account` class.

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
Print AssumptionExactness.
   *)
(* ------------------------------------------------------------------------- *)
(* Helpers for AccountState rep predicates                                    *)
(* ------------------------------------------------------------------------- *)

#[only(lens)] derive AssumptionExactness.

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
From Ltac2 Require Import Ltac2 String.
  Ltac2 newlines () : string := String.concat (string.String.newline ()) [string.String.newline (); string.String.newline ()].

Lemma prf: verify[module] fix_spec.
  Require Import bluerock.auto.cpp.
  Locate "verify[".
  Print cpp_proof.verify_in.

Require Import bluerock.ltac2.extra.extra.
Require Ltac2.Ltac2.

(** ** <<verify>>

    The <<verify[ tu ] spec>> provides a convenient way to write
    theorem statements for proofs that automatically computes the
    dependencies.

    When dependencies might be missing, you can use
    <<verify?[ tu ] spec>>.
 *)

  Import Ltac2.Ltac2.
  Import Ltac2.Printf.
  
  Ltac2 missingSpecs tu s := 
         match cpp_proof.parse_fn_spec s with
         | (sp_parsed, nm, sp) =>
             let (missing, deps) := cpp_proof.bundle_deps tu nm sp in
             printf "%a"
             (Printf.pp_list_sep (newlines ()) Printf.pp_constr)
               (Constr.ConstrSet.elements missing)
         end.
  Ltac2 Eval (missingSpecs 'module preterm:(fix_spec)).


  (*
"ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator!=<0b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>&) const"%cpp_name


"__builtin_expect"%cpp_name


"monad_assertion_failed"%cpp_name


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

