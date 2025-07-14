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
#[only(lazy_unfold)] derive StateR.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : ext.module ⊧ CU}.

  #[only(lens)] derive AssumptionExactness. (* TODO: move to decl *)

  
  cpp.spec "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const" as fix_spec with (fun this:ptr =>
   \prepost{preBlockState g au actualPreTxState} (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
   \pre [| blockStatePtr au = this |]
   \arg{statep: ptr} "state" (Vref statep)
   \pre{au: AssumptionsAndUpdates}  statep |-> StateR au
   \arg{addrp: ptr} "address" (Vref addrp)
   \prepost{qa fixee} addrp |-> addressR qa fixee
   \arg{origp: ptr} "original" (Vref origp)
   \pre{assumedFixeeState ae inds} origp |-> AccountStateR 1 assumedFixeeState ae inds
   \arg{actualp: ptr} "actual" (Vref actualp)
   \prepost actualp |-> libspecs.optionR "monad::Account" (fun acs => AccountR 1 acs inds) 1 (actualPreTxState !! fixee)
   \post{satisfiesAssumptionsb:bool} [Vbool satisfiesAssumptionsb]
    (*  [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **  may be provable, and may find performance bugs but wont strengthen the overall exec_block spec. the next line is weaker and suffices *)
     [| if satisfiesAssumptionsb then satisfiesAssumptions au actualPreTxState else Logic.True |] **
      if (negb satisfiesAssumptionsb)
      then statep |-> StateR au ** origp |-> AccountStateR 1 assumedFixeeState ae inds
      else
        Exists auf exactFixeeAssumption, statep |-> StateR auf
          ** origp |-> AccountStateR 1 exactFixeeAssumption (ae &: _min_balance .= None) inds
          ** [| relaxedValidation auf = false |]
          ** [| applyUpdates auf actualPreTxState = applyUpdates au actualPreTxState |]).



(* Rep predicate for VersionStack<monad::AccountState> *)
Definition VersionStackR (q: cQp.t) (ls: list monad.EVMOpSem.evm.account_state) : Rep :=
  bluerock.lang.cpp.logic.heap_pred.aggregate.structR
    "monad::VersionStack<monad::AccountState>" q.

(* Model predicates for is_empty and is_dead *)

Definition is_empty_model (oas: option monad.EVMOpSem.block.block_account) : bool :=
  match oas with
  | None => true
  | Some ba =>
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

Definition is_dead_model (oas: option monad.EVMOpSem.block.block_account) : bool :=
  negb (bool_decide (option.is_Some oas)) || is_empty_model oas.

(* Basic getter specs for AccountState and State *)

cpp.spec "monad::AccountState::min_balance() const"
  as accountstate_min_balance_spec
  with (fun this:ptr =>
    \pre{orig_state asm idx} this |-> AccountStateR 1 orig_state asm idx
    \post[Vptr (this ,, _field "monad::AccountState::min_balance_")]
          this |-> AccountStateR 1 orig_state asm idx).

cpp.spec "monad::AccountState::validate_exact_balance() const"
  as accountstate_validate_exact_balance_spec
  with (fun this:ptr =>
    \pre{orig_state asm idx} this |-> AccountStateR 1 orig_state asm idx
    \post[Vbool (~~ bool_decide (option.is_Some (min_balance asm)))]
          this |-> AccountStateR 1 orig_state asm idx).

cpp.spec "monad::AccountState::validate_exact_nonce() const"
  as accountstate_validate_exact_nonce_spec
  with (fun this:ptr =>
    \pre{orig_state asm idx} this |-> AccountStateR 1 orig_state asm idx
    \post[Vbool (nonce_exact asm)]
          this |-> AccountStateR 1 orig_state asm idx).

cpp.spec "monad::State::relaxed_validation() const"
  as state_relaxed_validation_spec
  with (fun this:ptr =>
    \pre{au} this |-> StateR au
    \post[Vbool (relaxedValidation au)]
          this |-> StateR au).

(* Specs for the free functions is_empty and is_dead *)

cpp.spec "monad::is_empty(const monad::Account&)" as is_empty_spec with (
  \arg{accountp: ptr} "account" (Vref accountp)
  \pre{(oas: option monad.EVMOpSem.block.block_account) (idx: monad.proofs.exec_specs.Indices)}
      accountp |-> monad.proofs.libspecs.optionR
                   "monad::Account"
                   (fun ba => monad.proofs.exec_specs.AccountR 1 ba idx) 1 oas
  \post[Vbool (is_empty_model oas)]
      accountp |-> monad.proofs.libspecs.optionR
                   "monad::Account"
                   (fun ba => monad.proofs.exec_specs.AccountR 1 ba idx) 1 oas
).

cpp.spec "monad::is_dead(const std::optional<monad::Account>&)" as is_dead_spec with (
  \arg{accountp: ptr} "account" (Vref accountp)
  \pre{(oas: option monad.EVMOpSem.block.block_account) (idx: monad.proofs.exec_specs.Indices)}
      accountp |-> monad.proofs.libspecs.optionR
                   "monad::Account"
                   (fun ba => monad.proofs.exec_specs.AccountR 1 ba idx) 1 oas
  \post[Vbool (is_dead_model oas)]
      accountp |-> monad.proofs.libspecs.optionR
                   "monad::Account"
                   (fun ba => monad.proofs.exec_specs.AccountR 1 ba idx) 1 oas
).

(* Spec of VersionStack::size(), a method, so we use fun this:ptr => … *)

cpp.spec "monad::VersionStack<monad::AccountState>::size() const"
  as versionstack_size_spec
  with (fun this:ptr =>
    \pre{(ls: list monad.EVMOpSem.evm.account_state) (q:Qp)}
        this |-> VersionStackR (cQp.mut q) ls
    \post[Vint (Z.of_nat (length ls))]
        this |-> VersionStackR (cQp.mut q) ls
  ).


(* 1. U256 addition assignment: intx::uint<256u>::operator+=(const intx::uint<256u>&) *)
cpp.spec "intx::uint<256u>::operator+=(const intx::uint<256u>&)" as u256_add_assign_spec with ( fun (this:ptr) =>
  \arg{yp: ptr} "y" (Vref yp)
  \prepost{(q qy: Qp) (xv yv: Corelib.Numbers.BinNums.N)}
      this |-> monad.proofs.exec_specs.u256R (cQp.mut q) xv
    ** yp   |-> monad.proofs.exec_specs.u256R (cQp.mut qy) yv
  \post[Vref this]
      this |-> monad.proofs.exec_specs.u256R (cQp.mut q) (N.modulo (xv + yv) (2 ^ 256))%N
    ** yp   |-> monad.proofs.exec_specs.u256R (cQp.mut qy) yv
).

(* 2. U256 subtraction assignment: intx::uint<256u>::operator-=(const intx::uint<256u>&) *)
cpp.spec "intx::uint<256u>::operator-=(const intx::uint<256u>&)" as u256_sub_assign_spec with (fun (this:ptr) =>
  \arg{yp: ptr} "y" (Vref yp)
  \prepost{(q qy: Qp) (xv yv: Corelib.Numbers.BinNums.N)}
      this |-> monad.proofs.exec_specs.u256R (cQp.mut q) xv
    ** yp   |-> monad.proofs.exec_specs.u256R (cQp.mut qy) yv
  \post[Vref this]
      this |-> monad.proofs.exec_specs.u256R (cQp.mut q) (N.modulo (xv - yv) (2 ^ 256))%N
    ** yp   |-> monad.proofs.exec_specs.u256R (cQp.mut qy) yv
).

(* 3. Bytes32 inequality: evmc::operator!=(const evmc::bytes32&, const evmc::bytes32&) *)
cpp.spec "evmc::operator!=(const evmc::bytes32&, const evmc::bytes32&)" as bytes32_neq_spec with(
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \prepost{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> monad.proofs.exec_specs.bytes32R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.bytes32R (cQp.mut qb) bv
  \post[Vbool (negb (N.eqb av bv))] emp
).

  #[global] Instance dec (i1 i2: Indices): Decision (i1=i2) := ltac:(solve_decision).

(* 4. Incarnation equality: monad::operator==(monad::Incarnation, monad::Incarnation) *)
cpp.spec "monad::operator==(monad::Incarnation, monad::Incarnation)" as incarnation_eq_spec with (
  \arg{i1p: ptr} "i1" (Vref i1p)
  \arg{i2p: ptr} "i2" (Vref i2p)
  \prepost{(q1 q2: Qp) (idx1 idx2: monad.proofs.exec_specs.Indices)}
      i1p |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q1) idx1
    ** i2p |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q2) idx2
  \post[Vbool (bool_decide (idx1 = idx2))] emp
).

(* 5. std::optional<Account>::operator bool() const *)
cpp.spec "std::optional<monad::Account>::operator bool() const" as optional_bool_spec with ( fun (this:ptr) =>
  \prepost{(q: Qp) (oas: option monad.EVMOpSem.block.block_account) (idx: monad.proofs.exec_specs.Indices)}
      this |-> monad.proofs.libspecs.optionR
                "monad::Account"
                (fun ba => monad.proofs.exec_specs.AccountR (cQp.mut q) ba idx) q oas
  \post[Vbool (bool_decide (stdpp.option.is_Some oas))]
      this |-> monad.proofs.libspecs.optionR
                "monad::Account"
                (fun ba => monad.proofs.exec_specs.AccountR (cQp.mut q) ba idx) q oas
).



 (* 6. U256 assignment: intx::uint<256u>::operator=(const intx::uint<256u>&) *)
cpp.spec "intx::uint<256u>::operator=(const intx::uint<256u>&)" as u256_assign_spec with (fun (this:ptr) =>
  \arg{yp: ptr} "y" (Vref yp)
  \pre{(q qy: Qp) (xv yv: Corelib.Numbers.BinNums.N)}
      this |-> monad.proofs.exec_specs.u256R (cQp.mut q) xv
    ** yp   |-> monad.proofs.exec_specs.u256R (cQp.mut qy) yv
  \post[Vref this]
      this |-> monad.proofs.exec_specs.u256R (cQp.mut q) yv
    ** yp   |-> monad.proofs.exec_specs.u256R (cQp.mut qy) yv
).

(* 7. U256 less-than: intx::operator<(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator<(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_lt_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
  \post[Vbool (av <? bv)%N]
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
).

cpp.spec "intx::operator==(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_eq_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
  \post[Vbool (bool_decide (av = bv)%N)]
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
).

(* 8. U256 greater-than: intx::operator>(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator>(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_gt_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
  \post[Vbool (bv <? av)%N]
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
).

(* 9. U256 greater-or-equal: intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_ge_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
  \post[Vbool (bv <=? av)%N]
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
).


(* 8. std::optional<Account>::operator->() non‐const *)
cpp.spec "std::optional<monad::Account>::operator->()" as optional_arrow_spec with (fun (this:ptr) =>
  \prepost{(q: Qp) (oas: option monad.EVMOpSem.block.block_account) (idx: monad.proofs.exec_specs.Indices)}
      this |-> monad.proofs.libspecs.optionR
                "monad::Account"
                (fun ba => monad.proofs.exec_specs.AccountR (cQp.mut q) ba idx) q oas
  \post[Vptr (this ,, opt_somety_offset "monad::Account")] emp
).

(* 9. std::optional<Account>::operator->() const *)
cpp.spec "std::optional<monad::Account>::operator->() const" as optional_arrow_const_spec with (fun (this:ptr) =>
  \prepost{(q: Qp) (oas: option monad.EVMOpSem.block.block_account) (idx: monad.proofs.exec_specs.Indices)}
      this |-> monad.proofs.libspecs.optionR
                "monad::Account"
                (fun ba => monad.proofs.exec_specs.AccountR (cQp.mut q) ba idx) q oas
  \post[Vptr (this ,, opt_somety_offset "monad::Account")] emp
).





(* Rep predicate for the iterator object *)
 Definition mapIterR (i: N) : Rep :=
  structR
      "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>" 1. (* TODO: add ownership of fields *)



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

  cpp.spec "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::operator!=<0b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>&) const" as iter_neq_spec with
  (fun this: ptr =>
     \arg{otherp: ptr} "other" (Vref otherp)
     \prepost{(i1 i2: Corelib.Numbers.BinNums.N)}
       this  |-> mapIterR i1
     ** otherp |-> mapIterR i2
     \post[Vbool (negb (i1 =? i2)%N)]
       this  |-> mapIterR i1
     ** otherp |-> mapIterR i2).

  (* 16. iterator destructor *)
  cpp.spec "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, 4096ul>::iter_t<0b>::~iter_t()" as iterd with
  (fun this: ptr =>
     \pre{(i: Corelib.Numbers.BinNums.N)} this |-> mapIterR i
     \post emp
  ).

(* ------------------------------------------------------------------- *)
(* Specs of State::current_.end() and find() using MapCurrentR        *)
(* with index‐correctness assertions                                  *)
(* ------------------------------------------------------------------- *)

(* end(): index = length l *)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::end()"
  as current_end_spec
  with (fun (this: ptr) =>
    \pre{(l: list (monad.proofs.evmopsem.evm.address * list monad.proofs.evmopsem.evm.account_state)) (q: Qp)}
      this |-> monad.proofs.exec_specs.MapCurrentR q l
    \post{(ret:ptr) (i:nat)}
      [Vptr ret] this |-> monad.proofs.exec_specs.MapCurrentR q l
     ** ret |-> mapIterR (Stdlib.NArith.BinNat.N.of_nat i)
     ** [| i = length l |]
  ).

(* find(key): index matches position of key in l *)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>::find(const evmc::address&)"
  as current_find_spec
  with (fun (this: ptr) =>
    \arg{keyp: ptr} "key" (Vref keyp)
    \prepost{(l: list (monad.proofs.evmopsem.evm.address * list monad.proofs.evmopsem.evm.account_state)) (qk qm: Qp) (addr: monad.proofs.evmopsem.evm.address)}
      this |-> monad.proofs.exec_specs.MapCurrentR qm l
    \prepost keyp |-> monad.proofs.libspecs.addressR (cQp.mut qk) addr
    \post{(ret:ptr) (oidx: option N) (st:list monad.proofs.evmopsem.evm.account_state)}
      [Vptr ret] ret  |-> mapIterR (ssrfun.Option.default (lengthN l) oidx)
      ** [| match oidx with
            | Some idx  => nth_error l (N.to_nat idx) = Some (addr, st)
            | None => True
            end
            |]
  ).

cpp.spec "monad::Incarnation::Incarnation(const monad::Incarnation&)"
  as incarnation_copy_spec with (fun this:ptr =>
  \arg{otherp:ptr} "other" (Vref otherp)
  \prepost{(q:Qp) (idx: monad.proofs.exec_specs.Indices)}
      otherp |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q) idx
  \post
      this   |-> monad.proofs.exec_specs.IncarnationR (cQp.mut 1) idx).


(* 9. U256 greater-or-equal: intx::operator>=(const intx::uint<256u>&, const intx::uint<256u>&) *)
cpp.spec "intx::operator-(const intx::uint<256u>&, const intx::uint<256u>&)" as u256_minus_spec with (
  \arg{ap: ptr} "a" (Vref ap)
  \arg{bp: ptr} "b" (Vref bp)
  \pre{(qa qb: Qp) (av bv: Corelib.Numbers.BinNums.N)}
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
  \post{ret}[Vptr ret]
      ap |-> monad.proofs.exec_specs.u256R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.u256R (cQp.mut qb) bv
    ** ret |-> monad.proofs.exec_specs.u256R (cQp.mut qb) ((av -bv) `mod` (2 ^ 256))%N
).


(* TODO : delete: duplicate in exec_Transaction. generalize over 256 *)
cpp.spec "intx::uint<256u>::~uint()" as uint256dtor with (λ this : ptr, \pre{w} this |-> u256R 1 w
                        \post    emp).
#[global] Instance : LearnEq2 u256R := ltac:(solve_learnable).

  Lemma observeState (state_addr:ptr) q t ae inds:
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> AccountStateR q t ae inds).
  Proof using. Admitted.

  Definition observeStateF r q t a b:= @observe_fwd _ _ _ (observeState r q t a b).
  Hint Resolve observeStateF : br_opacity.
  
Require Import monad.proofs.bigauto.

Hint Opaque AccountSubstateR : br_opacity.
Hint Opaque AccountStateR : br_opacity.
Transparent AccountR.
Hint Opaque AccountR: br_opacity.
  Opaque w256_to_Z.
  Transparent libspecs.optionR.
  Opaque w256_to_Z.
  Hint Opaque libspecs.optionR: br_opacity.
  #[global] Instance learnac : LearnEq3 (AccountR) := ltac:(solve_learnable).
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
    #[global] Instance learning5 (origp: ptr) o1 o2: learn_exist_interface.Learnable 
      (origp ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR 1 (block.block_account_storage o1))
      (origp ,, o_field CU "monad::AccountState::storage_"
         |-> StorageMapR 1 (block.block_account_storage o2))
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
    #[global] Instance ll : LearnEq4 AccountStateR := ltac:(solve_learnable).
    
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
  #[global] Instance lllll: LearnEq1 mapIterR := ltac:(solve_learnable).

    #[global] Instance optionRSomeAc 
     q oas (origp:ptr) x inds idx:
    learn_exist_interface.Learnable (origp ,, opt_somety_offset
                                                               "monad::Account"
                                                               |-> AccountR 1 x inds)
                                    
      (origp |->  libspecs.optionR "monad::Account" (fun ba : block.block_account => AccountR q ba idx)
         q oas) [ oas = Some x; inds = idx] := ltac:(solve_learnable).

      #[global] Instance foldedLv2Lear (origp:ptr) q qq oas x idx: learn_exist_interface.Learnable
    (origp ,, opt_somety_offset
    "monad::Account" ,, 
      o_field CU "monad::Account::balance"
      |-> u256R qq (w256_to_N (block.block_account_balance x)))
    (origp |->  libspecs.optionR "monad::Account" (fun ba : block.block_account => AccountR q ba idx)
       q oas)
    [ oas = Some x;  q=1%Qp] := ltac:(solve_learnable).

    Opaque mapIterR.
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
  
  Definition foldAccountR := [FWD] (fun p a b c => @AutoUnlocking.unfold_eq _ _ _ (@AutoUnlocking.Unfoldable_at _ _ _ _ _ p (AccountR_unfoldable _ _ _ _ a b c))).
  Hint Resolve foldAccountR : br_opacity.
  Definition costRemB := [BWD<-]wp_const_const_delete.
  Hint Resolve costRemB: br_opacity.
Lemma prf: verify[module] fix_spec.
Proof using.
  work.
  iAssert (inc_dtor) as "#?". admit.
  verify_spec'.
  big.
  wp_if.
  2:{ (*nonce match case. it is simpler than and extremely similar to the other case *)  admit. }
  big.
  wp_if.
  2:{ (*balance match case. it is simpler than and extremely similar to the other case *)  admit. }

  big.
  wp_if.
  { (* more complex case where there is an entry in the current map, which the tx did an operation that can potentially update the state of that account. needs some more detailed specs about iterators to reason about how iter->second works *)
    admit.
  }
  {
    Remove Hints foldedLv2Lear : typeclass_instances.
    go.
    iExists _.
    iExists (Some x0).
    go.
    
    iExists _.
    iExists (Some x).
    go.
    iExists _.
    iExists (Some x0).
    go.
    
    iExists _.
    iExists (Some (x &: _block_account_nonce .= block.block_account_nonce x0)).
    destruct x.
    simpl.
    go.

    
    HERE


    
  #[global] Instance foldedLv2Lear2 (origp:ptr) q qq oas x idx: learn_exist_interface.Learnable
    (origp ,, opt_somety_offset
    "monad::Account" ,, 
      o_field CU "monad::Account::code_hash"
      |->  bytes32R qq (code_hash_of_program (block.block_account_code x)))
    (origp |->  libspecs.optionR "monad::Account" (fun ba : block.block_account => AccountR q ba idx)
       q oas)
    [ oas = Some x;  q=qq%Qp] := ltac:(solve_learnable).
  go.
    go.
    do 8 run1.
    do 4 run1.
    do 4 run1.
    do 4 run1.
    do 4 run1.
    do 4 run1.
    do 4 run1.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.

    Search x0.
    iFrame.
    iFrame.
    iFrame.
    iFrame.
    iFrame.
    work.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    step.
    work.
    run1.
    run1.
    run1.
    do 4 run1.
    do 4 run1.
    do 4 run1.
    
    go.
    big.
    iassert
  
  2:{ }
  2:{  slauto.
  - slauto. admit. fail.
  big.
    rewrite <- .
  go.
  work.
  
  go.
  apply andSep.
  go.
  apply trueSepEmp.
  go.
  
  progress big.

  True **
  (Exists q : cQp.t,
   actualp ,, opt_somety_offset "monad::Account" ,, o_field CU "monad::Account::nonce"
   |-> ulongR q (w256_to_Z (block.block_account_nonce x0)) ** True -∗
   operators.wp_eval_binop.body module Bneq "unsigned long" "unsigned long" "bool"
     (w256_to_Z (block.block_account_nonce x)) (w256_to_Z (block.block_account_nonce x0))
     (fun v' : val =>
      nonce_mismatch_addr |-> primR "bool" 1$c v' -∗
      interp module ((1 >*> 1) |*| (1 >*> 1))
        (wp_decls module  
  go.
  Search True emp.
  Set Nested Proofs Allowed.
  apply andSep.
  go.
  Search learn_exist_interface.Learnable primR.
  work.
    Search environments.envs_entails.
    intros.
  PrimRSep


  work.
  go.
  instOptionR.
  instOptionR. go.
    
  subst.
  ego.
  slauto.
  ego.
  wp_if;[slauto; fail|].
  ego.
  wp_if;[slauto; fail|].
  slauto.
  ego.
  slauto.
  unfold is_Some in *.
  
  slauto.
  miscPure.forward_reason.
  Forward.rwHyps.
  simpl in *.
  go.
  wp_if;[slauto|].
  slauto.
  wapplyRev AccountR_unfoldable.
  eagerUnifyU.
  go.
  iExists _, _, _.
  optionSome.
  
  slauto.
  wapplyRev AccountR_unfoldable.
  go.
  iExists _, _, _.
  optionSome.
  slauto.
  wapplyRev AccountR_unfoldable.
  go.
  iExists _, _, _.
  optionSome.
  slauto.
  iExists _.
  slauto.
  optionSomeBig.
  iExists _.
  slauto.
  wp_if.
  { (* nonce mismatch *)
    slauto.
    wp_if;slauto.

    Set Nested Proofs Allowed.
    go.
    
    slauto.
    wp_if; slauto.
    optionSomeBig; slauto.
    wp_if; slauto.
    go.
    big.
    go.
    unfold AccountStateR.
    big.
    Forward.rwHyps.
    subst.
    unfoldLocalDefs.
    unfold is_Some.
    simpl in *.
    miscPure.forward_reason.
    subst.
    go.
    Forward.rwHyps.
    go.
    wp_if; big.
    Transparent StateR.
    unfold StateR.
    slauto.
    rewrite <- wp_const_const_delete.
    slauto.
    rewrite <- wp_const_const_delete.
    slauto.
    
    mapIterR
Search wp_const.
    go.

    #[global] Instance 
    
Search AccountStateR.   
    Forward.rwHyps.
    go.
    go.
    optionSome;
    go.
    optionSomeBig.
    
  optionSomeBig.
  go.
  ego; fail.
  ego; fail.
  go.
  wapplyR AccountR_unfoldable.
  go.




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
