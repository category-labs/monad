Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.block_state_cpp.
Require Import monad.proofs.exec_specs.

 Require Import monad.proofs.execproofs.exec_transaction. 
Disable Notation atomic_name'.
Require Import Lens.Elpi.Elpi.
#[local] Open Scope lens_scope.

#[only(lazy_unfold)] derive AccountR.
#[only(lazy_unfold)] derive AccountStateR.
#[only(lazy_unfold)] derive OriginalAccountStateR.
#[only(lazy_unfold)] derive StateR.

Open Scope N_scope.
    Lemma balassertion (minBal localBal orignalBal actualBal: N):
    orignalBal - localBal <= minBal (* crucial for the proof *)
   ->  minBal <= actualBal
   ->  actualBal < orignalBal
   -> (orignalBal - actualBal) <= localBal.
    Proof using.
      lia. (* success *)
    Qed.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : ext.module ⊧ CU}.

  #[only(lens)] derive AssumptionExactness. (* TODO: move to decl *)


  Definition update {K V} `{EqDecision K}  (k: K) (newval: ptr*V) (m: MapModel K V): MapModel K V :=
    (k,newval)::(List.filter (fun p => bool_decide (fst p <> k)) m).

  Definition lookupr {K V} `{Countable K} := fun k m =>
     (((list_to_map m):(gmap K (ModelWithPtr V))) !! k).
  
  Global Instance lkk {K V} `{Countable K}:  Lookup K  V (MapModel K V) := fun k m =>
    option_map snd (lookupr k m).

  Typeclasses Transparent MapModel.
  Typeclasses Transparent ModelWithPtr.

Definition StateAccountSliceR (addr: evm.address) (a: AssumptionAndUpdate) (relaxedVal: bool) : Rep :=
  _field "monad::State::original_" |->
     AnkerMapSliceR "evmc::address" "monad::OriginalAccountState" 
           addressToN
           addressR
           (fun q asae => let '(ast, ae) := asae in OriginalAccountStateR q ae ast)
           addr
           (Some (originalLoc a, preTxAcStateAssumptions a))
         
  ** _field "monad::State::current_" |->
        AnkerMapSliceR "evmc::address" "monad::VersionStack<monad::AccountState>" 
           addressToN
           addressR
           (VersionStackR "monad::AccountState" AccountStateR)
           addr
           (match txUpdates a with None => None | Some (loc, upd) => Some (loc, [upd])  end)
  ** _field "monad::State::relaxed_validation_" |-> boolR 1$m relaxedVal
  **  structR "monad::State" (1/2)$m.
  
  cpp.spec "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const" as fix_spec with (fun this:ptr =>
   \prepost{preBlockState g au actualPreTxState} (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
   \pre [| blockStatePtr au = this |]
   \arg{statep: ptr} "state" (Vref statep)
   \pre{fixeeAddr fixeeStateSlice relaxedVal}
      statep |-> StateAccountSliceR fixeeAddr fixeeStateSlice relaxedVal
   \arg{addrp: ptr} "address" (Vref addrp)
   \prepost{qa} addrp |-> addressR qa fixeeAddr
   \arg "original" (Vref (originalLoc fixeeStateSlice))
   (* \pre{assumedFixeeState ae} origp |-> OriginalAccountStateR 1 ae assumedFixeeState *)
   \arg{actualp: ptr} "actual" (Vref actualp)
   \prepost actualp |-> libspecs.optionR "monad::Account" (fun acs => AccountR 1 acs) 1 (actualPreTxState !! fixeeAddr)
   \post{satisfiesAssumptionsb:bool} [Vbool satisfiesAssumptionsb]
    (*  [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **  may be provable, and may find performance bugs but wont strengthen the overall exec_block spec. the next line is weaker and suffices *)
     [| if satisfiesAssumptionsb then  satAccountNonStorageAssumptions relaxedVal (Some fixeeStateSlice) (actualPreTxState !! fixeeAddr)
        else Logic.True |] **
      if (negb satisfiesAssumptionsb)
      then statep |-> StateAccountSliceR fixeeAddr fixeeStateSlice relaxedVal
      else
        Exists fixeeStateSliceFinal,
          statep |-> StateAccountSliceR fixeeAddr fixeeStateSliceFinal relaxedVal
          ** [| accountFinalVal false fixeeStateSliceFinal (actualPreTxState !! fixeeAddr)  = accountFinalVal relaxedVal fixeeStateSlice (actualPreTxState !! fixeeAddr) |] ).



(* Model predicates for is_empty and is_dead *)

Definition is_empty_model (oas: option AccountM) : bool :=
  match oas with
  | None => true
  | Some (ba,_) =>
      let ch := monad.proofs.exec_specs.code_hash_of_program
                  (monad.EVMOpSem.block.block_account_code ba) in
      let zn := monad.proofs.exec_specs.w256_to_Z
                  (monad.EVMOpSem.block.block_account_nonce ba) in
      let bn := monad.proofs.exec_specs.w256_to_N
                  (monad.EVMOpSem.block.block_account_balance ba) in
      (N.eqb ch 0%N)
      && (Z.eqb zn 0)
      && (N.eqb bn 0%N)
  end.

Definition is_dead_model (oas: option AccountM) : bool :=
  negb (bool_decide (option.is_Some oas)) || is_empty_model oas.

(* Basic getter specs for AccountState and State *)

cpp.spec "monad::AccountState::min_balance() const"
  as accountstate_min_balance_spec
  with (fun this:ptr =>
    \prepost{orig_state asm} this |-> OriginalAccountStateR 1 asm orig_state
    \post[Vptr (this ,, _field "monad::AccountState::min_balance_")]
          emp).

cpp.spec "monad::AccountState::validate_exact_balance() const"
  as accountstate_validate_exact_balance_spec
  with (fun this:ptr =>
    \prepost{orig_state asm} this |-> OriginalAccountStateR 1  asm orig_state
    \post[Vbool (~~ bool_decide (option.is_Some (min_balance asm)))] emp).

cpp.spec "monad::AccountState::validate_exact_nonce() const"
  as accountstate_validate_exact_nonce_spec
  with (fun this:ptr =>
    \prepost{orig_state asm} this |-> OriginalAccountStateR 1 asm orig_state
    \post[Vbool (nonce_exact asm)] emp).

cpp.spec "monad::State::relaxed_validation() const"
  as state_relaxed_validation_spec inline.

(*
cpp.spec "monad::State::relaxed_validation() const"
  as state_relaxed_validation_spec
  with (fun this:ptr =>
    \prepost{au} this |-> StateR au
    \post[Vbool (relaxedValidation au)] emp).
*)

(* Specs for the free functions is_empty and is_dead *)

cpp.spec "monad::is_empty(const monad::Account&)" as is_empty_spec with (
  \arg{accountp: ptr} "account" (Vref accountp)
  \prepost{(oas: option AccountM) }
      accountp |-> libspecs.optionR
                   "monad::Account"
                   (fun ba => AccountR 1 ba) 1 oas
  \post[Vbool (is_empty_model oas)] emp).

cpp.spec "monad::is_dead(const std::optional<monad::Account>&)" as is_dead_spec with (
  \arg{accountp: ptr} "account" (Vref accountp)
  \prepost{(oas: option AccountM)}
      accountp |-> libspecs.optionR
                   "monad::Account"
                   (fun ba => AccountR 1 ba) 1 oas
  \post[Vbool (is_dead_model oas)] emp
).


(* TODO: generalize *)
cpp.spec "monad::VersionStack<monad::AccountState>::size() const"
  as versionstack_size_spec
  with (fun this:ptr =>
    \prepost{ls q}
        this |-> VersionStackR "monad::AccountState" AccountStateR (cQp.mut q) ls
    \post[Vint (Z.of_nat (length ls))] emp
  ).


(* 1. U256 addition assignment: intx::uint<256u>::operator+=(const intx::uint<256u>&) *)
cpp.spec "intx::uint<256u>::operator+=(const intx::uint<256u>&)" as u256_add_assign_spec with ( fun (this:ptr) =>
  \arg{yp: ptr} "y" (Vref yp)
  \pre{(q qy: Qp) (xv yv: Corelib.Numbers.BinNums.N)}
      this |-> u256R (cQp.mut q) xv
    ** yp   |-> u256R (cQp.mut qy) yv
  \post[Vref this]
      this |-> u256R (cQp.mut q) (N.modulo (xv + yv) (2 ^ 256))%N
    ** yp   |-> u256R (cQp.mut qy) yv
).

(* 2. U256 subtraction assignment: intx::uint<256u>::operator-=(const intx::uint<256u>&) *)
cpp.spec "intx::uint<256u>::operator-=(const intx::uint<256u>&)" as u256_sub_assign_spec with (fun (this:ptr) =>
  \arg{yp: ptr} "y" (Vref yp)
  \pre{(q qy: Qp) (xv yv: Corelib.Numbers.BinNums.N)}
      this |-> u256R (cQp.mut q) xv
    ** yp   |-> u256R (cQp.mut qy) yv
  \post[Vref this]
      this |-> u256R (cQp.mut q) (N.modulo (xv - yv) (2 ^ 256))%N
    ** yp   |-> u256R (cQp.mut qy) yv
).

(* 3. Bytes32 inequality: evmc::operator!=(const evmc::bytes32&, const evmc::bytes32&) *)
cpp.spec "evmc::operator!=(const evmc::bytes32&, const evmc::bytes32&)" as bytes32_neq_spec with(
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \prepost{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> bytes32R (cQp.mut qa) av
    ** bp |-> bytes32R (cQp.mut qb) bv
  \post[Vbool (negb (N.eqb av bv))] emp
).

  #[global] Instance dec (i1 i2: Indices): Decision (i1=i2) := ltac:(solve_decision).

(* 4. Incarnation equality: monad::operator==(monad::Incarnation, monad::Incarnation) *)
cpp.spec "monad::operator==(monad::Incarnation, monad::Incarnation)" as incarnation_eq_spec with (
  \arg{i1p: ptr} "i1" (Vref i1p)
  \arg{i2p: ptr} "i2" (Vref i2p)
  \prepost{(q1 q2: Qp) (idx1 idx2: Indices)}
      i1p |-> IncarnationR (cQp.mut q1) idx1
    ** i2p |-> IncarnationR (cQp.mut q2) idx2
  \post[Vbool (bool_decide (idx1 = idx2))] emp
).

(* 5. std::optional<Account>::operator bool() const *)
cpp.spec "std::optional<monad::Account>::operator bool() const" as optional_bool_spec with ( fun (this:ptr) =>
  \prepost{(q: Qp) oas}
      this |-> libspecs.optionR
                "monad::Account"
                (fun ba => AccountR (cQp.mut q) ba) q oas
  \post[Vbool (bool_decide (stdpp.option.is_Some oas))] emp
).



 (* 6. U256 assignment: intx::uint<256u>::operator=(const intx::uint<256u>&) *)
cpp.spec "intx::uint<256u>::operator=(const intx::uint<256u>&)" as u256_assign_spec with (fun (this:ptr) =>
  \arg{yp: ptr} "y" (Vref yp)
  \pre{(q qy: Qp) (xv yv: Corelib.Numbers.BinNums.N)}
      this |-> u256R (cQp.mut q) xv
    ** yp   |-> u256R (cQp.mut qy) yv
  \post[Vref this]
      this |-> u256R (cQp.mut q) yv
    ** yp   |-> u256R (cQp.mut qy) yv
).

(* 7. U256 less-than: intx::operator<(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator<(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_lt_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
  \post[Vbool (av <? bv)%N]
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
).

cpp.spec "intx::operator==(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_eq_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
  \post[Vbool (bool_decide (av = bv)%N)]
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
).

(* 8. U256 greater-than: intx::operator>(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator>(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_gt_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
  \post[Vbool (bv <? av)%N]
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
).

(* 9. U256 greater-or-equal: intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_ge_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
  \post[Vbool (bv <=? av)%N]
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
).


(* 8. std::optional<Account>::operator->() non‐const *)
cpp.spec "std::optional<monad::Account>::operator->()" as optional_arrow_spec with (fun (this:ptr) =>
  \prepost{(q: Qp) oas}
      this |-> libspecs.optionR
                "monad::Account"
                (fun ba => AccountR (cQp.mut q) ba) q oas
  \post[Vptr (this ,, opt_somety_offset "monad::Account")] emp
).

(* 9. std::optional<Account>::operator->() const *)
cpp.spec "std::optional<monad::Account>::operator->() const" as optional_arrow_const_spec with (fun (this:ptr) =>
  \prepost{(q: Qp) oas}
      this |-> libspecs.optionR
                "monad::Account"
                (fun ba => AccountR (cQp.mut q) ba) q oas
  \post[Vptr (this ,, opt_somety_offset "monad::Account")] emp
).

(* 8. std::optional<Account>::operator->() non‐const *)
cpp.spec "std::optional<monad::Account>::value() &" as optional_val_spec with (fun (this:ptr) =>
  \prepost{(q: Qp) oas}
      this |-> libspecs.optionR
                "monad::Account"
                (fun ba => AccountR (cQp.mut q) ba) q oas
  \post[Vptr (this ,, opt_somety_offset "monad::Account")] emp
).

(* 9. std::optional<Account>::operator->() const *)
cpp.spec "std::optional<monad::Account>::value() const &" as optional_val_const_spec with (fun (this:ptr) =>
  \prepost{(q: Qp) oas}
      this |-> libspecs.optionR
                "monad::Account"
                (fun ba => AccountR (cQp.mut q) ba) q oas
  \post[Vptr (this ,, opt_somety_offset "monad::Account")] emp
).



(**
Monad is a new L1 blockchain that can execute EVM-compative transactions much faster.
The C++ class `monad::AccountState` stores the state of an account while a transaction is being executed.
Monad executes transactions of a block with optimisic concurrency.
`monad::State` defines the state of the whole blockchain during the (possibly speculative) execution of a transaction.
As transactios commit, they update `monad::BlockState`.
`monad::State::read_account` reads from `monad::BlockState` which may not have the changes yet from the last few transactions.

The Gallina model type for `model::State` is `AssumptionsAndUpdates`.
The field C++ `original_` records the accounts that have been read during the execution.
In original_ in, monad::AccountState,  the validate_exact_balance_ field denotes whethere the transaction has done some action (e.g. BALANCE opcode) that requires the pre-tx balance to be an exact value instead of just being >= min_balance (e.g. CALL) for the speculative execution to not be invalidated by previous concurrent transactions.
In `monad::State`, relaxed_validation is false if the execution is not speculative and all previous transactions are known to have finished, in which case, the underlying BlockState is guaranted to have the preTx state, and not be lagging bahind.

I am now proving the spec of monad::State::fix_account_mismatch(...).
This function is executed at the end of the speculative execution of a transaction, after waiting for the previous transaction to commit.
This function is called by monad::BlockState::can_merge, which checks whether the speculative assumptions made are valid for the actual pre-tx state, now that the previous transaction has committed. If monad::BlockState::can_merge returns, true monad::BlockState::merge is called to merge the updates in `monad::State` to `monad::BlockState`.

It is executed only if the assumed value of an account is different from the actual value of an account after the previous tx commits. If so, it tries to see if the mismatch is only in balance or nonce and `validate_exact_balance_` is false  indicates that the speculations of the transaction are valid as long as balance >= min_balance.

The function calls many other functions. To do the proof in Coq, I need the spec of those functions. Your task is to write the specs of those functions:

"ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator!=<0b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>&) const"


"ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::end()"


"ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::find(const evmc::address&)"


Do not write all specs at once. Write only a few and fix all errors and then get to the others. Keep a (* TOFIXLATER *) comment somewhere in your answer so that the chatloop comes back to you to give you a chance to fix dummy definitions



To write specs, you need to know the Rep predicates of the class the method belongs to, and the Rep predicates for the types of the arguments.
Below are some existing Rep predicates that you can use (in addition to the ones mentioned in the general spec background above):
- IncarnationR is the existing Rep predicate for the c++ class `monad::Incarnation`.
- bytes32R for `bytes32_t` (alias for `evmc::bytes32`).
- u256t for `uint256_t` (alias for `intx::uint<256>`)
- addressR is the Rep predicate for Address (alias for `evmc::address`)
- AccountR is the Rep predicate for monad::Account
- AccountSubstateR is the Rep predicate for monad::AccountSubState
- AccountStateR is the Rep predicate for monad::AccountState
- StateR for monad::AccountState.
- BlockState.Rauth for monad::BlockState in this context when the previous transaction has finished and we have exclusive write access the block state, which is the `this` location in the call to monad::BlockState::fix_account_mismatch and also the block_state_ reference in the monad::State argument.

Use mapIterR, defined in this file above, as the Rep predicator for the iterator `iter_t`.

Unfortunately, there is no way to search for the Rep predicate for a class. Assume
the above list (in addition to the content in previous sections and in the current file) is exhaustive.


+++ FILES
../../fmai/prompts/sep.md
../../fmai/prompts/specs.md

+++ QUERIES

Print evm.account_state.
Print block.block_account.
Print IncarnationR.
Print addressR.
Print bytes32R.
Print u256R.
Print AssumptionExactness.
Print AccountStateR.
Print AccountSubstateR.
Print AccountR.
Print StateR.
Print AssumptionsAndUpdates.
CppDefnOf monad::BlockState::fix_account_mismatch.
CppDefnOf monad::BlockState::can_merge.
Print can_merge.
CppDefnOf monad::BlockState::merge.
Print merge.
 *)


(* ------------------------------------------------------------------- *)
(* Specs of State::current_.end() and find() using MapCurrentR        *)
(* with index‐correctness assertions                                  *)
(* ------------------------------------------------------------------- *)


cpp.spec "monad::Incarnation::Incarnation(const monad::Incarnation&)"
  as incarnation_copy_spec with (fun this:ptr =>
  \arg{otherp:ptr} "other" (Vref otherp)
  \prepost{(q:Qp) (idx: Indices)}
      otherp |-> IncarnationR (cQp.mut q) idx
  \post
      this   |-> IncarnationR (cQp.mut 1) idx).


(* 9. U256 greater-or-equal: intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator-(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_minus_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
  \post{ret}[Vptr ret]
      ap |-> u256R (cQp.mut qa) av
    ** bp |-> u256R (cQp.mut qb) bv
    ** ret |-> u256R (cQp.mut qb) ((av -bv) `mod` (2 ^ 256))%N
).


(* TODO : delete: duplicate in exec_Transaction. generalize over 256 *)
cpp.spec "intx::uint<256u>::~uint()" as uint256dtor with (λ this : ptr, \pre{w} this |-> u256R 1 w
                        \post    emp).
#[global] Instance : LearnEq2 u256R := ltac:(solve_learnable).

  Lemma observeOrigState (state_addr:ptr) q t ae:
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> OriginalAccountStateR q t ae).
  Proof using. Admitted.

  Lemma observeState (state_addr:ptr) q t:
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> AccountStateR q t).
  Proof using. Admitted.
  
  Definition observeStateF r q t:= @observe_fwd _ _ _ (observeState r q t).
  Definition observeOrigStateF r q t a:= @observe_fwd _ _ _ (observeOrigState r q t a).
  Hint Resolve observeStateF observeOrigStateF : br_opacity.
  
Require Import monad.proofs.bigauto.

Hint Opaque AccountSubstateR : br_opacity.
Hint Opaque AccountStateR : br_opacity.
Transparent AccountR.
Hint Opaque AccountR: br_opacity.
  Opaque w256_to_Z.
  Transparent libspecs.optionR.
  Opaque w256_to_Z.
  Hint Opaque libspecs.optionR: br_opacity.
  #[global] Instance learnac : LearnEq2 (AccountR) := ltac:(solve_learnable).
  #[global] Instance learnby : LearnEq2 (bytes32R) := ltac:(solve_learnable).
  Arguments libspecs.optionR {_} {_} {_} {_} {_} _ _ _ !o/.

  #[global] Instance optionRSome {SomeTyModel:Type} (somety somety2: bluerock.lang.cpp.syntax.core.type)
    (someTyRep someTyRep2: SomeTyModel -> Rep) (q:Qp) (s: SomeTyModel) (oa: option SomeTyModel) (b:ptr):
    learn_exist_interface.Learnable (b ,, opt_somety_offset somety |-> someTyRep s)
      (b |-> libspecs.optionR somety2 someTyRep2 q oa) [ oa = Some s] := ltac:(solve_learnable).
  
  Ltac optionSome :=
  IPM.perm_right ltac:(fun R _ =>
    match R with
    | ?b |-> @libspecs.optionR _ _ _ _ ?T ?somety ?someTyRep _ ?oa =>
        IPM.perm_left ltac:(fun L _ =>
          match L with
          | b ,, opt_somety_offset somety |-> ?someTyRep2 =>
             let f := fresh "evarn" in
             evar (f:T);
             let tt:= eval unfold f in (someTyRep f) in
               unify tt someTyRep2;
               unify oa (Some f)
              end)
    end).

  cpp.spec (Nscoped ("monad::Incarnation") (Ndtor))
    as inc_dtor with
      (fun (this:ptr) => \pre{r} this |-> IncarnationR 1 r
                          \post emp
      ).
  Ltac optionSomeBig final :=
    wapplyRev AccountR_unfoldable;
    work;
    repeat (iExists _);
    Forward.rwHyps;
    optionSome;
    final.
  Hint Opaque IncarnationR : br_opacity.
    #[global] Instance learning3 : LearnEq2 StorageMapR := ltac:(solve_learnable).
    #[global] Instance learning5 (origp: ptr) o1 o2: Learnable 
      (origp ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR 1 (storageMapOf o1))
      (origp ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR 1 (storageMapOf o2))
      [o1=o2] := ltac:(solve_learnable).
    #[global] Instance learning6 (origp: ptr) o1 o2: learn_exist_interface.Learnable 
      (origp ,, o_field CU "monad::AccountState::validate_exact_nonce_"
  |-> primR "bool" 1$m (Vbool (nonce_exact o1)))
      (origp ,, o_field CU "monad::AccountState::validate_exact_nonce_"
  |-> primR "bool" 1$m (Vbool (nonce_exact o2)))
      [o1=o2] := ltac:(solve_learnable).
    #[global] Instance learning7 (origp: ptr) o1 o2: learn_exist_interface.Learnable 
      (origp ,, o_field CU "monad::AccountState::validate_exact_balance_"
  |-> primR "bool" 1$m  (Vbool (~~ bool_decide (is_Some (min_balance o1)))))
      (origp ,, o_field CU "monad::AccountState::validate_exact_balance_"
  |-> primR "bool" 1$m  (Vbool (~~ bool_decide (is_Some (min_balance o2)))))
      [o1=o2] := ltac:(solve_learnable).
    #[global] Instance ll : LearnEq2 AccountStateR := ltac:(solve_learnable).
    #[global] Instance ll2 : LearnEq3 OriginalAccountStateR := ltac:(solve_learnable).
    
  Ltac unifyOptionR :=
    IPM.perm_right ltac:(fun R _ =>
    match R with
    | ?b |-> @libspecs.optionR _ _ _ _ ?T ?somety ?someTyRep _ _ =>
        IPM.perm_left ltac:(fun L _ =>
          match L with
          | b |-> @libspecs.optionR _ _ _ _ T somety ?someTyRep2 _ _ =>
              unify someTyRep someTyRep2
          end)
    end).
  Ltac instOptionR :=
    repeat (iExists _); unifyOptionR.

  Ltac slauto := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id; try solveRefereceTo; try autounfold with unfold; try Forward.forward_reason; try Forward.rwHyps; (* try optionSomeBig; *) try instOptionR)); try iPureIntro.
  
  Arguments is_Some /_ _.
  #[global] Instance llll: LearnEq2 MapCurrentR := ltac:(solve_learnable).
  #[global] Instance lllll: LearnEq3 AnkerMapIterR := ltac:(solve_learnable).

    #[global] Instance optionRSomeAc 
     q oas (origp:ptr) x:
    learn_exist_interface.Learnable (origp ,, opt_somety_offset
                                                               "monad::Account"
                                                               |-> AccountR 1 x)
                                    
      (origp |->  libspecs.optionR "monad::Account" (fun ba=> AccountR q ba)
         q oas) [ oas = Some x] := ltac:(solve_learnable).

      #[global] Instance foldedLv2Lear (origp:ptr) q qq oas x: learn_exist_interface.Learnable
    (origp ,, opt_somety_offset
    "monad::Account" ,, 
      o_field CU "monad::Account::balance"
      |-> u256R qq (w256_to_N (block.block_account_balance (fst x))))
    (origp |->  libspecs.optionR "monad::Account" (fun ba => AccountR q ba)
       q oas)
    [ oas = Some x;  q=1%Qp] := ltac:(solve_learnable).

    Opaque AnkerMapIterR.
  Existing Instance UNSAFE_read_prim_learn.
  Lemma andSep {T} (P Q : T->mpred) E:
    environments.envs_entails E (Exists t:T, (P t ** (P t -* Q t)))
    -> environments.envs_entails E (Exists t:T, (P t //\\ Q t)).
  Proof using Sigma.
    apply environments.envs_entails_mono.
    - reflexivity.
    -  ego; eagerUnifyU. go. iStopProof. apply lose_resources.
  Qed.
  Lemma trueSepEmp (P: mpred) E:
    environments.envs_entails E P
    -> environments.envs_entails E (True ** P).
  Proof using Sigma.
    apply environments.envs_entails_mono.
    - reflexivity.
    - go.
  Qed.

  Ltac big :=
    repeat(slauto; try (wp_if;slauto;[])). (* only do a case split if one case can be fully solved *)
  
  Definition foldAccountR := [FWD] (fun p a b => @AutoUnlocking.unfold_eq _ _ _ (@AutoUnlocking.Unfoldable_at _ _ _ _ _ p (AccountR_unfoldable _ _ _ _ a b))).
  Hint Resolve foldAccountR : br_opacity.
  Definition costRemB := [BWD<-]wp_const_const_delete.
  Hint Resolve costRemB: br_opacity.
      #[global] Instance foldedLv2Lear2 (origp:ptr) q qq oas x: learn_exist_interface.Learnable
    (origp ,, opt_somety_offset
    "monad::Account" ,, 
      o_field CU "monad::Account::balance"
      |-> u256R qq (w256_to_N (block.block_account_balance (fst x))))
    (origp |->  libspecs.optionR "monad::Account" (fun ba => AccountR q ba)
       q (if block.block_account_exists oas.1 then Some oas else None))
    [ oas = x;  q=1%Qp] := ltac:(solve_learnable).

  Set Nested Proofs Allowed.
  Lemma equationfoo (x assumedFixeeState: AccountM): (if block.block_account_exists assumedFixeeState.1 then Some assumedFixeeState else None) = Some x -> x=assumedFixeeState /\ block.block_account_exists assumedFixeeState.1 = true.
  Proof using. intros Heq.
  destruct assumedFixeeState as [assumedFixeeState inds]. simpl in *.
  remember (block.block_account_exists assumedFixeeState) as rd.
  destruct rd; simpl in *; try discriminate;[].
  destruct x as [assumedFixeeState1 inds1]; try discriminate.
  simplify_eq. auto.
  Qed.
Notation LearnEq7 P :=
  (forall a a' b b' c c' d d' e e' f f' g g',
    learn_exist_interface.Learnable
      (P a b c d e f g)
      (P a' b' c' d' e' f' g')
      [a = a'; b = b'; c = c'; d = d'; e = e'; f = f'; g=g']).
  
#[global] Instance lanker {K V} : LearnEq7 (@AnkerMapR _ _ _ K V) := ltac:(solve_learnable).
(* #[global] Instance lmapiter : LearnEq3 mapIterR := ltac:(solve_learnable). *)
      
  Opaque Zdigits.binary_value Zdigits.Z_to_binary.
Lemma prf: verify[module] fix_spec.
Proof using.
  verify_spec'.
  iAssert (inc_dtor) as "#?". admit.
  unfold StateAccountSliceR.
  go.
  unfold AnkerMapSliceR.
  go.
  destruct fixeeStateSlice.
  simpl in *.
  destruct preTxAcStateAssumptions as [pAssumed ae].
  simpl in *.
  big.
  wp_if.
  2:{ (*nonce match case. it is simpler than and extremely similar to the other case *)  admit. }
  big.

  (* there are 3 vars of type AccountM. 2 of them are same: x and assumedFixeestate.1  the next block unifies them. figure out why we ended up with 3 vars*)
  (*
  destruct x0 as [assumedFixeeState2 inds2]; try discriminate.
  simpl in *.
  subst. 
  orient_rwHyps.
  simplify_eq.*)

  (*
      #[global] Instance foldedLv2Lear3 (origp:ptr) q qq oas x: learn_exist_interface.Learnable
    (origp ,, opt_somety_offset
    "monad::Account" ,, 
      o_field CU "monad::Account::balance"
      |-> u256R qq (w256_to_N (block.block_account_balance (fst x))))
    (origp |->  libspecs.optionR "monad::Account" (fun ba => AccountR q ba)
       q (if block.block_account_exists oas.1 then Some oas else None))
    [ oas = x;  q=1%Qp] := ltac:(solve_learnable).
   *)
  unfold OriginalAccountStateR. go.
  unfold AccountR. go.
  rwHypsP.
  slauto.
  wp_if.
  2:{ (*balance match case. it is simpler than and extremely similar to the other case *)  admit. }

  big.
  repeat (iExists _). (* learning for AnkerMapR does not work. why? *)
  eagerUnifyU.
  slauto.
  repeat (iExists _).
  eagerUnifyU.
  slauto.
  destruct txUpdates as [txUpdates |].
  { (* fixee (address) found in state.current *)
    destruct txUpdates as [updLoc txUpdates].
    simpl in *.
    go.
    unfold pairSndOffset.
    unfold pairOffsets.
    go.
    #[global] Instance kjsfdjs {T} a: LearnEq3 (@VersionStackR _ _ _ T a) := ltac:(solve_learnable).
    #[global] Instance kjfslksfdjs a: LearnEq2 (@VersionStackSpineR _ _ _ a) := ltac:(solve_learnable).
    #[global] Instance fsdkflj {A B} (foo:A*B) ls: Refine1 false false (map fst ls = [foo.1]) [ls=[foo]] :=
      ltac:(constructor; auto).
Arguments pairSndOffset/.
Arguments pairOffsets/.
     unfold VersionStackR.
     slauto.
     destruct txUpdates as [txUpdloc txUpd].
     simpl in *.
     slauto.
     wp_if;[slauto|]. (* return false if the optuonal account in txUpd is None *)
     slauto. (* above, we admitted the nonce match case, so we directly go the nonce mismatch case *)
     rename x into assumed.
     rename x0 into actual.
     assert (w256_to_Z (block.block_account_nonce assumed.1) <= w256_to_Z (block.block_account_nonce actual.1)) as Hle by admit. (*TODO: add this as a precond. eventually, will need to strenghthen the BlockState::read_account Rfrag spec. *)
     slauto.
     wp_if.
     { (* assumed balance > actual balance *)
     
    Remove Hints foldedLv2Lear : typeclass_instances.
    Remove Hints foldedLv2Lear2 : typeclass_instances.
    Remove Hints prim.primR_aggressiveC: br_opacity.
    Set Printing Depth 999999999.

    (* assumedBal ~ original.balance
       updatedBal ~ local.balance

original.balance:

     *)

       (*
1 focused goal (shelved: 1) (ID 5909603)
  
  thread_info : biIndex
  _Σ : gFunctors
  Sigma : cpp_logic thread_info _Σ
  CU : genv
  MODd : ext.module ⊧ CU
  f := fix_spec : mpredI
  _H_ : module ⊧ CU
  _x_ : ptr -> mpred
  state_addr, address_addr, original_state_addr, oactual_addr : ptr
  preBlockState : StateOfAccounts
  g : BlockState.glocs
  au : StateM
  actualPreTxState : StateOfAccounts
  statep : ptr
  fixeeAddr : evm.address
  pAssumed : PartialAccountState
  ae : AssumptionExactness
  originalLoc, txUpdloc : ptr
  txUpd : PartialAccountState
  addrp : ptr
  qa : Qp
  actualp, ooriginal_addr : ptr
  assumed : AccountM
  original_addr, actual_addr : ptr
  actual : AccountM
  nonce_mismatch_addr, balance_mismatch_addr, local_state_addr, olocal_addr, local_addr : ptr
  x2 : AccountM
  GUARDS : GWs.GUARDS
  _H_0 : valid<"monad::State&"> (Vptr statep)
  _H_1 : valid<"evmc::address&"> (Vptr addrp)
  _H_2 : valid<"monad::AccountState&"> (Vptr originalLoc)
  _H_3 : valid<"std::optional<monad::Account>&"> (Vptr actualp)
  _H_4 : valid<"bool"> (Vbool true)
  _H_5 : valid<"std::optional<monad::Account>&"> (Vptr (originalLoc ,, o_field CU "monad::AccountState::account_"))
  _transient_map_ : list (N * N)
  _H_6 : valid<"bool"> (Vbool (~~ bool_decide (exists x : N, min_balance ae = Some x)))
  _H_7 : valid<"bool"> (Vbool (nonce_exact ae))
  H0 : coreState pAssumed = Some assumed
  b : is_empty_model (coreState pAssumed) = false
  _H_8 : valid<"bool"> (Vbool true)
  _H_9 : valid<"unsigned long"> (w256_to_Z (block.block_account_nonce assumed.1))
  H1 : actualPreTxState !! fixeeAddr = Some actual
  b0 : is_empty_model (actualPreTxState !! fixeeAddr) = false
  _H_10 :
    valid<"monad::Account&"> (Vptr
                                (originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset
                                                                                                "monad::Account"))
  _H_11 : valid<"monad::Account&"> (Vptr (actualp ,, opt_somety_offset "monad::Account"))
  _H_12 : valid<"unsigned long"> (w256_to_Z (block.block_account_nonce actual.1))
  _q_ :
    (code_hash_of_program (block.block_account_code assumed.1) =? code_hash_of_program (block.block_account_code actual.1))%N =
    true
  _q1_ : assumed.2 = actual.2
  _H_13 :
    valid<"bool"> (Vbool
                     (bool_decide
                        (w256_to_Z (block.block_account_nonce assumed.1) ≠ w256_to_Z (block.block_account_nonce actual.1))))
  _p_ : w256_to_Z (block.block_account_nonce assumed.1) ≠ w256_to_Z (block.block_account_nonce actual.1)
  _q2_ : nonce_exact ae = false
  _transient_map_0 : list (N * N)
  _H_14 : valid<"bool"> (Vbool false)
  _H_15 :
    valid<"bool"> (Vbool
                     (~~
                      bool_decide
                        (w256_to_N (block.block_account_balance assumed.1) = w256_to_N (block.block_account_balance actual.1))))
  _p1_ : w256_to_N (block.block_account_balance assumed.1) ≠ w256_to_N (block.block_account_balance actual.1)
  x1 : N
  H2 : min_balance ae = Some x1
  _transient_map_1 : list (N * N)
  _q3_ : (w256_to_N (block.block_account_balance actual.1) <? x1)%N = false
  it_addr : ptr
  i : N
  _x_1, _x_0 : ptr
  _H_16 :
    _x_1 ,, pairFstOffset "evmc::address" "monad::VersionStack<monad::AccountState>" =
    _x_0 ,, pairFstOffset "evmc::address" "monad::VersionStack<monad::AccountState>"
  _H_17 :
    _x_1 ,, o_field CU "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>::second" =
    _x_0 ,, o_field CU "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>::second"
  _H_18 : valid<"monad::AccountState&"> (Vptr txUpdloc)
  _H_19 : valid<"std::optional<monad::Account>&"> (Vptr (txUpdloc ,, o_field CU "monad::AccountState::account_"))
  transient_map : list (N * N)
  H3 : coreState txUpd = Some x2
  _H_20 :
    valid<"monad::Account&"> (Vptr
                                (txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account"))
  _H_21 : valid<"unsigned long"> (w256_to_Z (block.block_account_nonce x2.1))
  Hle : w256_to_Z (block.block_account_nonce assumed.1) ≤ w256_to_Z (block.block_account_nonce actual.1)
  _H_22 :
    valid<"unsigned long"> (w256_to_Z (block.block_account_nonce actual.1) - w256_to_Z (block.block_account_nonce assumed.1))
  _H_23 :
    valid<"unsigned long"> (trim 64
                              (w256_to_Z (block.block_account_nonce x2.1) +
                               (w256_to_Z (block.block_account_nonce actual.1) -
                                w256_to_Z (block.block_account_nonce assumed.1))))
  _p2_ : (w256_to_N (block.block_account_balance actual.1) <? w256_to_N (block.block_account_balance assumed.1))%N = true
  diff_addr : ptr
  ============================
  _ : denoteModule module
  _ : type_ptr "monad::State&" state_addr
  _ : type_ptr "evmc::address&" address_addr
  _ : type_ptr "monad::AccountState&" original_state_addr
  _ : type_ptr "std::optional<monad::Account>&" oactual_addr
  _ : type_ptr "monad::State" statep
  _ : type_ptr "std::optional<monad::Account>" actualp
  _ : versionstack_size_spec
  _ : uint256dtor
  _ : u256_sub_assign_spec
  _ : u256_minus_spec
  _ : u256_lt_spec
  _ : u256_gt_spec
  _ : u256_ge_spec
  _ : u256_eq_spec
  _ : u256_assign_spec
  _ : u256_add_assign_spec
  _ : optional_val_spec
  _ : optional_val_const_spec
  _ : optional_bool_spec
  _ : is_dead_spec
  _ : incarnation_eq_spec
  _ : incarnation_copy_spec
  _ : bytes32_neq_spec
  _ : accountstate_validate_exact_nonce_spec
  _ : accountstate_validate_exact_balance_spec
  _ : accountstate_min_balance_spec
  _ : version_stack_recent_spec
  _ : iterd
  _ : iter_neq_spec
  _ : iter_arrow_spec
  _ : current_find_spec
  _ : current_end_spec
  _ : inc_dtor
  _ : reference_to "monad::AccountState" originalLoc
  _ : type_ptr "monad::AccountState" originalLoc
  _ : type_ptr "std::optional<monad::Account>&" ooriginal_addr
  _ : type_ptr "monad::AccountSubstate" (originalLoc ,, o_base CU "monad::AccountState" "monad::AccountSubstate")
  _ : type_ptr "bool" (originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_engaged_offset "monad::Account")
  _ : type_ptr "monad::Account"
        (originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account")
  _ : type_ptr "monad::Account&" original_addr
  _ : type_ptr "monad::Account&" actual_addr
  _ : type_ptr "bool" (actualp ,, opt_engaged_offset "monad::Account")
  _ : type_ptr "monad::Account" (actualp ,, opt_somety_offset "monad::Account")
  _ : type_ptr "bool" nonce_mismatch_addr
  _ : type_ptr "bool" balance_mismatch_addr
  _ : validP<"bool"> (Vbool false)
  _ : reference_to
        "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>"
        it_addr
  _ : validP<"std::pair<evmc::address, monad::VersionStack<monad::AccountState>>*"> (Vptr _x_1)
  _ : reference_to "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>" _x_1
  _ : reference_to "monad::VersionStack<monad::AccountState>"
        (_x_0 ,, o_field CU "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>::second")
  _ : validP<"std::pair<evmc::address, monad::VersionStack<monad::AccountState>>*"> (Vptr _x_0)
  _ : reference_to "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>" _x_0
  _ : type_ptr "monad::AccountState&" local_state_addr
  _ : reference_to "std::optional<monad::Account>" (txUpdloc ,, o_field CU "monad::AccountState::account_")
  _ : type_ptr "std::optional<monad::Account>&" olocal_addr
  _ : reference_to "monad::AccountState" txUpdloc
  _ : type_ptr "monad::AccountState" txUpdloc
  _ : type_ptr "monad::AccountSubstate" (txUpdloc ,, o_base CU "monad::AccountState" "monad::AccountSubstate")
  _ : type_ptr "monad::Account&" local_addr
  _ : type_ptr "bool" (txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_engaged_offset "monad::Account")
  _ : type_ptr "monad::Account" (txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account")
  _ : validP<"bool"> (Vbool true)
  _ : reference_to "intx::uint<256u>" diff_addr
  _ : validP<"bool"> (Vbool
                        ((w256_to_N (block.block_account_balance assumed.1) - w256_to_N (block.block_account_balance actual.1))
                         `mod` 2 ^ 256 <=? w256_to_N (block.block_account_balance x2.1))%N)
  --------------------------------------□
  _ : blockStatePtr au |-> BlockState.Rauth preBlockState g actualPreTxState
  _ : HiddenPostCondition
  _ : state_addr |-> primR "monad::State&" 1$m (Vptr statep)
  _ : address_addr |-> primR "evmc::address&" 1$m (Vptr addrp)
  _ : original_state_addr |-> primR "monad::AccountState&" 1$m (Vptr originalLoc)
  _ : oactual_addr |-> primR "std::optional<monad::Account>&" 1$m (Vptr actualp)
  _ : statep |-> structR "monad::State" (1 / 2)$m
  _ : statep ,, o_field CU "monad::State::relaxed_validation_" |-> primR "bool" 1$m (Vbool true)
  _ : statep ,, o_field CU "monad::State::original_"
      |-> AnkerMapSliceSpineR "evmc::address" "monad::OriginalAccountState" addressToN addressR
            (fun (q : Qp) '(ast, ae0) =>
             o_base CU "monad::AccountState" "monad::AccountSubstate"
             |-> AccountSubstateR q
                   {| asm_destructed := false; asm_touched := false; asm_accessed := false; asm_accessed_keys := [] |} **
             o_field CU "monad::AccountState::account_"
             |-> libspecs.optionR "monad::Account"
                   (fun ba : AccountM =>
                    o_field CU "monad::Account::balance" |-> u256R q (w256_to_N (block.block_account_balance ba.1)) **
                    o_field CU "monad::Account::code_hash"
                    |-> bytes32R q (code_hash_of_program (block.block_account_code ba.1)) **
                    o_field CU "monad::Account::nonce" |-> ulongR q$m (w256_to_Z (block.block_account_nonce ba.1)) **
                    o_field CU "monad::Account::incarnation" |-> IncarnationR q ba.2 ** structR "monad::Account" q$m)
                   q (coreState ast) **
             o_field CU "monad::AccountState::storage_" |-> StorageMapR q (storageMapOf ast) **
             (Exists transient_map0 : list (N * N),
              o_field CU "monad::AccountState::transient_storage_" |-> StorageMapR q transient_map0) **
             structR "monad::AccountState" q$m **
             o_field CU "monad::AccountState::validate_exact_nonce_" |-> primR "bool" q$m (Vbool (nonce_exact ae0)) **
             o_field CU "monad::AccountState::validate_exact_balance_"
             |-> primR "bool" q$m (Vbool (~~ bool_decide (exists x : N, min_balance ae0 = Some x))) **
             o_field CU "monad::AccountState::min_balance_"
             |-> match min_balance ae0 with
                 | Some n => u256R q n
                 | None => Exists nb : N, u256R q nb
                 end)
            fixeeAddr (Some originalLoc)
  _ : ooriginal_addr
      |-> primR "std::optional<monad::Account>&" 1$m (Vptr (originalLoc ,, o_field CU "monad::AccountState::account_"))
  _ : original_addr
      |-> primR "monad::Account&" 1$m
            (Vptr (originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account"))
  _ : actual_addr |-> primR "monad::Account&" 1$m (Vptr (actualp ,, opt_somety_offset "monad::Account"))
  _ : actualp |-> structR "std::optional<monad::Account>" 1$m
  _ : actualp ,, opt_engaged_offset "monad::Account" |-> primR "bool" 1$m (Vbool true)
  _ : actualp ,, opt_somety_offset "monad::Account" |-> structR "monad::Account" 1$m
  _ : actualp ,, opt_somety_offset "monad::Account" ,, o_field CU "monad::Account::nonce"
      |-> ulongR 1$m (w256_to_Z (block.block_account_nonce actual.1))
  _ : actualp ,, opt_somety_offset "monad::Account" ,, o_field CU "monad::Account::code_hash"
      |-> bytes32R 1 (code_hash_of_program (block.block_account_code actual.1))
  _ : actualp ,, opt_somety_offset "monad::Account" ,, o_field CU "monad::Account::incarnation" |-> IncarnationR 1 actual.2
  _ : nonce_mismatch_addr |-> primR "bool" 1$c (Vbool true)
  _ : balance_mismatch_addr |-> primR "bool" 1$c (Vbool true)
  _ : originalLoc |-> structR "monad::AccountState" 1$m
  _ : originalLoc ,, o_field CU "monad::AccountState::validate_exact_balance_" |-> primR "bool" 1$m (Vbool false)
  _ : originalLoc ,, o_field CU "monad::AccountState::validate_exact_nonce_" |-> primR "bool" 1$m (Vbool false)
  _ : originalLoc ,, o_field CU "monad::AccountState::storage_" |-> StorageMapR 1 (storageMapOf pAssumed)
  _ : originalLoc ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
      |-> AccountSubstateR 1
            {| asm_destructed := false; asm_touched := false; asm_accessed := false; asm_accessed_keys := [] |}
  _ : originalLoc ,, o_field CU "monad::AccountState::transient_storage_" |-> StorageMapR 1 _transient_map_1
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" |-> structR "std::optional<monad::Account>" 1$m
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_engaged_offset "monad::Account"
      |-> primR "bool" 1$m (Vbool true)
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account"
      |-> structR "monad::Account" 1$m
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::incarnation" |-> IncarnationR 1 actual.2
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::nonce" |-> ulongR 1$m (w256_to_Z (block.block_account_nonce assumed.1))
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::code_hash" |-> bytes32R 1 (code_hash_of_program (block.block_account_code assumed.1))
  _ : originalLoc ,, o_field CU "monad::AccountState::min_balance_" |-> u256R 1 x1
  _ : addrp |-> addressR qa fixeeAddr
  _ : statep ,, o_field CU "monad::State::current_"
      |-> AnkerMapSliceSpineR "evmc::address" "monad::VersionStack<monad::AccountState>" addressToN addressR
            (fun (q : Qp) (lt : list (ptr * PartialAccountState)) =>
             VersionStackSpineR "monad::AccountState" q (map fst lt) **
             pureR ([∗ list] '(loc, val0) ∈ lt, loc |-> AccountStateR q val0))
            fixeeAddr (Some (_x_0 ,, o_field CU "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>::second"))
  _ : it_addr
      |-> AnkerMapIterR (Some i) (_x_0 ,, pairFstOffset "evmc::address" "monad::VersionStack<monad::AccountState>")
            (_x_0 ,, o_field CU "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>::second")
  _ : _x_0 ,, o_field CU "std::pair<evmc::address, monad::VersionStack<monad::AccountState>>::second"
      |-> VersionStackSpineR "monad::AccountState" 1 [txUpdloc]
  _ : local_state_addr |-> primR "monad::AccountState&" 1$m (Vptr txUpdloc)
  _ : olocal_addr
      |-> primR "std::optional<monad::Account>&" 1$m (Vptr (txUpdloc ,, o_field CU "monad::AccountState::account_"))
  _ : txUpdloc |-> structR "monad::AccountState" 1$m
  _ : txUpdloc ,, o_field CU "monad::AccountState::storage_" |-> StorageMapR 1 (storageMapOf txUpd)
  _ : txUpdloc ,, o_base CU "monad::AccountState" "monad::AccountSubstate"
      |-> AccountSubstateR 1
            {| asm_destructed := false; asm_touched := false; asm_accessed := false; asm_accessed_keys := [] |}
  _ : txUpdloc ,, o_field CU "monad::AccountState::transient_storage_" |-> StorageMapR 1 transient_map
  _ : local_addr
      |-> primR "monad::Account&" 1$m
            (Vptr (txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account"))
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" |-> structR "std::optional<monad::Account>" 1$m
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::incarnation" |-> IncarnationR 1 x2.2
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::code_hash" |-> bytes32R 1 (code_hash_of_program (block.block_account_code x2.1))
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_engaged_offset "monad::Account"
      |-> primR "bool" 1$m (Vbool true)
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account"
      |-> structR "monad::Account" 1$m
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::nonce"
      |-> ulongR 1$m
            (trim 64
               (w256_to_Z (block.block_account_nonce x2.1) +
                (w256_to_Z (block.block_account_nonce actual.1) - w256_to_Z (block.block_account_nonce assumed.1))))
  _ : originalLoc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::balance" |-> u256R 1 (w256_to_N (block.block_account_balance assumed.1))
  _ : actualp ,, opt_somety_offset "monad::Account" ,, o_field CU "monad::Account::balance"
      |-> u256R 1 (w256_to_N (block.block_account_balance actual.1))
  _ : txUpdloc ,, o_field CU "monad::AccountState::account_" ,, opt_somety_offset "monad::Account" ,, 
      o_field CU "monad::Account::balance" |-> u256R 1 (w256_to_N (block.block_account_balance x2.1))
  _ : diff_addr
      |-> u256R 1
            ((w256_to_N (block.block_account_balance assumed.1) - w256_to_N (block.block_account_balance actual.1))
             `mod` 2 ^ 256)
  --------------------------------------∗
  branch.stmt module
    [region:
      "diff" @ diff_addr; "local" @ local_addr; "olocal" @ olocal_addr; "local_state" @ local_state_addr; 
      "it" @ it_addr; "balance_mismatch" @ balance_mismatch_addr; "nonce_mismatch" @ nonce_mismatch_addr;
      "actual" @ actual_addr; "original" @ original_addr; "ooriginal" @ ooriginal_addr; "oactual" @ oactual_addr;
      "original_state" @ original_state_addr; "address" @ address_addr; "state" @ state_addr; [this := blockStatePtr au];
      return {?: "bool"}]
    (~~
     ~~
     ((w256_to_N (block.block_account_balance assumed.1) - w256_to_N (block.block_account_balance actual.1)) `mod` 2 ^ 256 <=?
      w256_to_N (block.block_account_balance x2.1))%N)
    (Sseq [])
    (Sseq
       [Sexpr
          (Ecall
             (Ecast Cfun2ptr
                (Eglobal "monad_assertion_failed" "void(const char*, const char*, const char*, long, const char*)"))
             [Ecast Carray2ptr
                (Estring {| literal_string.bytes := "local.balance >= diff"; literal_string.bytes_per_char := 1 |} "char");
              Ecast Carray2ptr
                (Estring
                   {|
                     literal_string.bytes :=
                       "bool monad::BlockState::fix_account_mismatch(State &, const Address &, AccountState &, const std::optional<Account> &) const";
                     literal_string.bytes_per_char := 1
                   |} "char");
              Ecast Carray2ptr
                (Estring
                   {|
                     literal_string.bytes :=
                       "/home/abhishek/fv-workspace/monad/libs/execution/src/monad/state2/block_state.cpp";
                     literal_string.bytes_per_char := 1
                   |} "char");
              Ecast (Cintegral "long") (Eint 293 "int"); Ecast (Cnull2ptr "const char*") Enull])])
    (Kseq
       (wp_block module
          [region:
            "diff" @ diff_addr; "local" @ local_addr; "olocal" @ olocal_addr; "local_state" @ local_state_addr;
            "it" @ it_addr; "balance_mismatch" @ balance_mismatch_addr; "nonce_mismatch" @ nonce_mismatch_addr;
            "actual" @ actual_addr; "original" @ original_addr; "ooriginal" @ ooriginal_addr; "oactual" @ oactual_addr;
            "original_state" @ original_state_addr; "address" @ address_addr; "state" @ state_addr;
            [this := blockStatePtr au]; return {?: "bool"}]
          [Sseq [];
           Sexpr
             (Eoperator_call OOMinusEqual
                (operator_impl.MFunc "intx::uint<256u>::operator-=(const intx::uint<256u>&)"%cpp_name Direct
                   "intx::uint<256u>&(const intx::uint<256u>&)"%cpp_type)
                [Emember false (Evar "local" "monad::Account&") (Nid "balance") false "intx::uint<256u>";
                 Evar "diff" "const intx::uint<256u>"])])
       (Kfree module (1 >*> FreeTemps.delete "const intx::uint<256u>" diff_addr)
          (Kseq
             (wp_block module
                [region:
                  "local" @ local_addr; "olocal" @ olocal_addr; "local_state" @ local_state_addr; 
                  "it" @ it_addr; "balance_mismatch" @ balance_mismatch_addr; "nonce_mismatch" @ nonce_mismatch_addr;
                  "actual" @ actual_addr; "original" @ original_addr; "ooriginal" @ ooriginal_addr; 
                  "oactual" @ oactual_addr; "original_state" @ original_state_addr; "address" @ address_addr;
                  "state" @ state_addr; [this := blockStatePtr au]; return {?: "bool"}]
                [])
             (Kseq
                (wp_block module
                   [region:
                     "local" @ local_addr; "olocal" @ olocal_addr; "local_state" @ local_state_addr; 
                     "it" @ it_addr; "balance_mismatch" @ balance_mismatch_addr; "nonce_mismatch" @ nonce_mismatch_addr;
                     "actual" @ actual_addr; "original" @ original_addr; "ooriginal" @ ooriginal_addr;
                     "oactual" @ oactual_addr; "original_state" @ original_state_addr; "address" @ address_addr;
                     "state" @ state_addr; [this := blockStatePtr au]; return {?: "bool"}]
                   [])
                (Kfree module (1 >*> FreeTemps.delete "monad::Account&" local_addr)
                   (Kfree module (1 >*> FreeTemps.delete "std::optional<monad::Account>&" olocal_addr)
                      (Kfree module (1 >*> FreeTemps.delete "monad::AccountState&" local_state_addr)
                         (Kseq
                            (wp_block module
                               [region:
                                 "it" @ it_addr; "balance_mismatch" @ balance_mismatch_addr;
                                 "nonce_mismatch" @ nonce_mismatch_addr; "actual" @ actual_addr; "original" @ original_addr;
                                 "ooriginal" @ ooriginal_addr; "oactual" @ oactual_addr;
                                 "original_state" @ original_state_addr; "address" @ address_addr; 
                                 "state" @ state_addr; [this := blockStatePtr au]; return {?: "bool"}]
                               [Sif None (Ecast Cl2r (Evar "nonce_mismatch" "const bool"))
                                  (Sseq
                                     [Sexpr
                                        (Eassign
                                           (Emember false (Evar "original" "monad::Account&") (Nid "nonce") false
                                              "unsigned long")
                                           (Ecast Cl2r
                                              (Emember false (Evar "actual" "const monad::Account&") 
                                                 (Nid "nonce") false "unsigned long"))
                                           "unsigned long")])
                                  (Sseq []);
                                Sif None (Ecast Cl2r (Evar "balance_mismatch" "const bool"))
                                  (Sseq
                                     [Sexpr
                                        (Eoperator_call OOEqual
                                           (operator_impl.MFunc
                                              "intx::uint<256u>::operator=(const intx::uint<256u>&)"%cpp_name Direct
                                              "intx::uint<256u>&(const intx::uint<256u>&)"%cpp_type)
                                           [Emember false (Evar "original" "monad::Account&") (Nid "balance") false
                                              "intx::uint<256u>";
                                            Emember false (Evar "actual" "const monad::Account&") 
                                              (Nid "balance") false "intx::uint<256u>"])])
                                  (Sseq []);
                                Sreturn (Some (Ebool true))])
                            (Kfree module
                               (1 >*>
                                FreeTemps.delete
                                  "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>"
                                  it_addr)
                               (Kfree module (1 >*> FreeTemps.delete "const bool" balance_mismatch_addr)
                                  (Kfree module (1 >*> FreeTemps.delete "const bool" nonce_mismatch_addr)
                                     (Kfree module (1 >*> FreeTemps.delete "const monad::Account&" actual_addr)
                                        (Kfree module (1 >*> FreeTemps.delete "monad::Account&" original_addr)
                                           (Kfree module
                                              (1 >*> FreeTemps.delete "std::optional<monad::Account>&" ooriginal_addr)
                                              (Kcleanup module [] (Kreturn (fun v : ptr => ▷ _x_ v)))))))))))))))))
*)       
     go.
    unfold Vers
  iAssert (version_stack_recent_spec) as "#?". admit.
  unfold VersionStackR.
  slauto.
    go.
    slauto.
    iExists txUpdates, [].
    slauto.
    
    constructor.
    solve_refine.
  rwHypsP.
  Search txUpdates.

  
                             
    iExists _,_.
    slauto.
    Print atomic_name_.
    Compute .
  }
  { (* fixee (address) NOT found in state.current *)
    Remove Hints foldedLv2Lear : typeclass_instances.
    go.
    iExists _. (* 1%Qp *)
    iExists (Some x0).
    slauto.
    rename x into assumedFixeeState.
    iExists _.
    iExists (Some assumedFixeeState).
    go.
    iExists _.
    iExists (Some x0).
    go.
    
    iExists (1%Qp).
    iExists (Some (assumedFixeeState &: lens._fst .@ _block_account_nonce .= block.block_account_nonce (fst x0))).
    set (fixedAssumedFixeeState := ((assumedFixeeState &: lens._fst .@ _block_account_nonce .= block.block_account_nonce (fst x0) &: lens._fst .@ _block_account_balance .= block.block_account_balance (fst x0)))).
    destruct assumedFixeeState as [assumedFixeeState inds].
    simpl in *. subst.
    destruct assumedFixeeState.
    simpl.
    Remove Hints foldedLv2Lear2 optionRSomeAc: typeclass_instances.
    Remove Hints prim.primR_aggressiveC: br_opacity.
    go.
  #[only(lens)] derive PartialAccountState. (* TODO: move to decl *)
    iExists
      {| preTxAcStateAssumptions := (pAssumed &: _coreState .= Some fixedAssumedFixeeState, ae) ; exec_specs.originalLoc := originalLoc; txUpdates := None |}.
    slauto.
    split.
    - unfold min_balanceN. rwHypsP.
      destruct x0.
      simpl in *.
      Search x1.
      destruct b1.
      simpl in *.
      Search x1.
      unfold w256_to_N in *.
      Search x1.
      Transparent w256_to_Z.
      unfold w256_to_Z in *.
      Search x1.
      Search N.ltb false.
      applyToSomeHyp N.ltb_ge.
      Search x1.
      revert autogenhyp.
      (*
(x1 ≤ Z.to_N (Zdigits.binary_value 256 block_account_balance0))%N -> x1 ≤ Zdigits.binary_value 256 block_account_balance0 *)
      Set Printing Coercions.
      admit.
    - 
  }
  
      lia.
      
      lia.
      Check b1.
    subst.
    simpl in *.
    subst.
    simpl in *.
    go.
    (*
  --------------------------------------□
  origp ,, o_field CU "monad::AccountState::account_"
  |-> libspecs.optionR "monad::Account" (fun ba : AccountM => AccountR 1 ba) 1
        (if block_account_exists then Some fixedAssumedFixeeState else None) **
  origp ,, o_field CU "monad::AccountState::validate_exact_balance_" |-> primR "bool" 1$m (Vbool true) **
  statep ,, o_field CU "monad::State::current_"
  |-> MapCurrentR 1
        (update fixee
           (fixeeNewStateLoc,
            [accountFinalVal true
               (Some
                  ({|
                     block.block_account_address := block_account_address;
                     block.block_account_storage := block_account_storage;
                     block.block_account_code := block_account_code;
                     block.block_account_balance := block_account_balance;
                     block.block_account_nonce := block_account_nonce;
                     block.block_account_exists := block_account_exists;
                     block.block_account_hascode := block_account_hascode
                   |}, x0.2, ae))
               x0 (fixeeNewStateLoc, fixeeNewState)])
           (newStates au)) **
  [| satisfiesAssumptions au actualPreTxState |]
     *)
    
(*    
    Lemma falseTemp (origp: ptr):
      origp ,, o_field CU "monad::AccountState::validate_exact_balance_"
  |-> primR "bool" 1$m (Vbool false)
    |-- origp ,, o_field CU "monad::AccountState::validate_exact_balance_"
    |-> primR "bool" 1$m (Vbool true).
    Proof using. Admitted.
    Definition falseTempF := [FWD] falseTemp.
    Lemma falseTemp2 (origp: ptr):
      origp ,, o_field CU "monad::AccountState::relaxed_validation_"
  |-> primR "bool" 1$m (Vbool true)
    |-- origp ,, o_field CU "monad::AccountState::relaxed_validation_"
    |-> primR "bool" 1$m (Vbool false).
    Proof using. Admitted.
    Definition falseTempF2 := [FWD] falseTemp2.
    work using falseTempF, falseTempF2.
 *)


Abort.
  



End with_Sigma.


(** agent improvment:
- have a separate conversation just to check each spec, before sending to coqtop. do fixes on the fly with the agent. once the agent is done, run the checker on each spec, let it fix. the prompts can be customized for specialized types of specs, e.g. copy constructor, ==
- check specs for unused vars
- for every rep predicate, ask to add hints: learnable, unfoldable.


common gpt mistakes in specs
- ownership duplicated in \post even when using \prepost
- unused vars
- copy constructors
  - this |-> structR as \pre
  - \post [Vref this]
- consider the error case of functions, e.g. iterator not found case spec was wrong.
*)
