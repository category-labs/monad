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


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : ext.module ⊧ CU}.

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
  \post[Vbool (negb (N.eqb av bv))]
      ap |-> monad.proofs.exec_specs.bytes32R (cQp.mut qa) av
    ** bp |-> monad.proofs.exec_specs.bytes32R (cQp.mut qb) bv
).

  #[global] Instance dec (i1 i2: Indices): Decision (i1=i2) := ltac:(solve_decision).

(* 4. Incarnation equality: monad::operator==(monad::Incarnation, monad::Incarnation) *)
cpp.spec "monad::operator==(monad::Incarnation, monad::Incarnation)" as incarnation_eq_spec with (
  \arg{i1p: ptr} "i1" (Vref i1p)
  \arg{i2p: ptr} "i2" (Vref i2p)
  \prepost{(q1 q2: Qp) (idx1 idx2: monad.proofs.exec_specs.Indices)}
      i1p |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q1) idx1
    ** i2p |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q2) idx2
  \post[Vbool (bool_decide (idx1 = idx2))]
      i1p |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q1) idx1
    ** i2p |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q2) idx2
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
    \pre{(l: list (monad.proofs.evmopsem.evm.address * list monad.proofs.evmopsem.evm.account_state)) (q: Qp) (addr: monad.proofs.evmopsem.evm.address)}
      this |-> monad.proofs.exec_specs.MapCurrentR q l
      ** keyp |-> monad.proofs.libspecs.addressR (cQp.mut q) addr
    \post{(ret:ptr) (idx:nat) (st:list monad.proofs.evmopsem.evm.account_state)}
      [Vptr ret] this |-> monad.proofs.exec_specs.MapCurrentR q l
     ** keyp |-> monad.proofs.libspecs.addressR (cQp.mut q) addr
     ** ret  |-> mapIterR (Stdlib.NArith.BinNat.N.of_nat idx)
     ** [| Stdlib.Lists.List.nth_error l idx = Some (addr, st) |]
  ).

cpp.spec "monad::Incarnation::Incarnation(const monad::Incarnation&)"
  as incarnation_copy_spec with (fun this:ptr =>
  \arg{otherp:ptr} "other" (Vref otherp)
  \pre{(q:Qp) (idx: monad.proofs.exec_specs.Indices)}
      otherp |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q) idx
    ** this   |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR
                 "monad::Incarnation" (cQp.mut 1)
  \post[Vref this]
      this   |-> monad.proofs.exec_specs.IncarnationR (cQp.mut 1) idx
      ** otherp |-> monad.proofs.exec_specs.IncarnationR (cQp.mut q) idx).
 


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
  
Ltac slauto := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id; try solveRefereceTo)); try iPureIntro.

 Lemma prf: verify[module] fix_spec.
  Ltac2 Eval (missingSpecs constr:(module) preterm:(fix_spec)).
  Proof using.
    verify_spec'.
    slauto.
    unfold AccountStateR.
    slauto.
    ego.
    wp_if.
    {
      go.
    
Abort.







  

  
  (* monad::BlockState::fix_account_mismatch(...)                        *)
  (* -------------------------------------------------------------------- *)
  cpp.spec
    "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const"
    as fix_spec
    with (fun this:ptr =>
      \prepost{preBlockState g au actualPreTxState}
        (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
      \pre [| blockStatePtr au = this |]
      \arg{statep:ptr} "state" (Vref statep)
      \pre{au} statep |-> StateR au
      \arg{addrp:ptr} "address" (Vref addrp)
      \prepost{qa fixee} addrp |-> addressR qa fixee
      \arg{origp:ptr} "original" (Vref origp)
      \pre{assumedFixeeState ae inds}
        origp |-> AccountStateR 1 assumedFixeeState ae inds
      \arg{actualp:ptr} "actual" (Vref actualp)
      \pre actualp |-> libspecs.optionR "monad::AccountState"
                           (fun acs => AccountStateR 1 acs ae inds)
                           1 (actualPreTxState !! fixee)
      \post{satisfiesAssumptionsb:bool}[Vbool satisfiesAssumptionsb]
        [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **
      if negb satisfiesAssumptionsb then
        statep |-> StateR au ** origp |-> AccountStateR 1 assumedFixeeState ae inds
      else
        Exists auf exactFixeeAssumption,
          statep |-> StateR auf
        ** origp |-> AccountStateR 1 exactFixeeAssumption (ae &: _min_balance .= None) inds
        ** [| relaxedValidation auf = false |]
        ** [| applyUpdates auf actualPreTxState = applyUpdates au actualPreTxState |])).

  (* -------------------------------------------------------------------- *)
  (* monad::AccountState::min_balance() const                            *)
  (* -------------------------------------------------------------------- *)
  cpp.spec "monad::AccountState::min_balance() const"
    as min_balance_spec
    with (fun this:ptr =>
      \prepost{(orig: monad.EVMOpSem.block.block_account)
                (ae: monad.proofs.exec_specs.AssumptionExactness)
                (idx: monad.proofs.exec_specs.Indices)}
        this |-> monad.proofs.exec_specs.AccountStateR 1 orig ae idx
      \post[Vref (this ,, _field "monad::AccountState::min_balance_")]
        emp).

  (* -------------------------------------------------------------------- *)
  (* monad::AccountState::validate_exact_balance() const                 *)
  (* -------------------------------------------------------------------- *)
  cpp.spec "monad::AccountState::validate_exact_balance() const"
    as validate_exact_balance_spec
    with (fun this:ptr =>
      \prepost{(orig: monad.EVMOpSem.block.block_account)
                (ae: monad.proofs.exec_specs.AssumptionExactness)
                (idx: monad.proofs.exec_specs.Indices)}
        this |-> monad.proofs.exec_specs.AccountStateR 1 orig ae idx
      \post{b:bool}[Vbool b]
        [| b <-> stdpp.option.is_Some (monad.proofs.exec_specs.min_balance ae) |]).

  (* -------------------------------------------------------------------- *)
  (* monad::AccountState::validate_exact_nonce() const                   *)
  (* -------------------------------------------------------------------- *)
  cpp.spec "monad::AccountState::validate_exact_nonce() const"
    as validate_exact_nonce_spec
    with (fun this:ptr =>
      \prepost{(orig: monad.EVMOpSem.block.block_account)
                (ae: monad.proofs.exec_specs.AssumptionExactness)
                (idx: monad.proofs.exec_specs.Indices)}
        this |-> monad.proofs.exec_specs.AccountStateR 1 orig ae idx
      \post{b:bool}[Vbool b]
        [| b <-> monad.proofs.exec_specs.nonce_exact ae |]).

  (* -------------------------------------------------------------------- *)
  (* monad::State::relaxed_validation() const                            *)
  (* -------------------------------------------------------------------- *)
  cpp.spec "monad::State::relaxed_validation() const"
    as relaxed_validation_spec
    with (fun this:ptr =>
      \prepost{(s: monad.proofs.exec_specs.AssumptionsAndUpdates)}
        this |-> monad.proofs.exec_specs.StateR s
      \post{b:bool}[Vbool b]
        [| b <-> monad.proofs.exec_specs.relaxedValidation s |]).

  (* -------------------------------------------------------------------- *)
  (* monad::is_empty(const monad::Account&)                              *)
  (* -------------------------------------------------------------------- *)
  cpp.spec "monad::is_empty(const monad::Account&)"
    as is_empty_spec
    with (fun this:ptr =>
      \arg{acp:ptr} "account" (Vref acp)
      \prepost{(ba: monad.EVMOpSem.block.block_account)
                (idx: monad.proofs.exec_specs.Indices)}
        acp |-> monad.proofs.exec_specs.AccountR 1 ba idx
      \post{b:bool}[Vbool b]
        [| b <-> (
             negb (monad.EVMOpSem.block.block_account_hascode ba)
          && Z.eqb (monad.proofs.exec_specs.w256_to_Z (monad.EVMOpSem.block.block_account_nonce ba)) 0
          && Z.eqb (monad.proofs.exec_specs.w256_to_Z (monad.EVMOpSem.block.block_account_balance ba)) 0
        )%bool |])).

End with_Sigma.















  

    (*======== free comparison operators on uint<256> ==========================*)
cpp.spec "intx::operator==(const intx::uint<256u>&,const intx::uint<256u>&)" as u256_op_eqval_spec with (
  \arg{a1p} "a" (Vptr a1p)
  \arg{a2p} "b" (Vptr a2p)
  \pre{(n1 n2:Corelib.Numbers.BinNums.N)}
    a1p |-> u256R 1 n1 ** a2p |-> u256R 1 n2
  \post{(b:bool)} [Vbool b] [| b = true <-> n1 = n2 |]
).
  
 Set Printing FullyQualifiedNames.
(*======== Free function: is_dead ===========================================*)
cpp.spec "monad::is_dead(const std::optional<monad::Account>&)" as is_dead_spec with (
  \arg{optp:ptr} "opt" (Vref optp)
  \pre{(opt_model: option monad.EVMOpSem.block.block_account)
       (idx: monad.proofs.exec_specs.Indices)}
    optp |-> monad.proofs.libspecs.optionR
             "monad::Account"
             (fun ba' => AccountR 1 ba' idx)
             1
             opt_model
  \post{(b:bool)} [Vbool b]
    [| b = true <-> opt_model = None |]
).

(*======== Iterator inequality: operator!=<0b> ==============================*)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>,std::allocator<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>>,4096ul>::iter_t<0b>::operator!=<0b>(const ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>,std::allocator<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>>,4096ul>::iter_t<0b>&) const"
  as iter_neq_spec with (fun (this:ptr) =>
    \pre this |-> (* TOFIXLATER: Rep for segmented_vector::iter_t<0b> *) emp
    \arg{other} "other" (Vptr other)
    \pre other |-> (* TOFIXLATER: same Rep *) emp
    \post{(b:bool)} [Vbool b] emp
  ).

(*======== detail::table::end() =============================================*)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address,monad::VersionStack<monad::AccountState>,ankerl::unordered_dense::v4_1_0::hash<evmc::address,void>,std::equal_to<evmc::address>,std::allocator<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>>,ankerl::unordered_dense::v4_1_0::bucket_type::standard,1b>::end()"
  as table_end_spec with (fun (this:ptr) =>
    \pre this |-> structR
       "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
       1$m
    \post{(r:ptr)} [Vptr r] emp
  ).

(*======== AccountState::min_balance() const ================================*)
cpp.spec "monad::AccountState::min_balance() const" as min_balance_spec with (fun (this:ptr) =>
  \prepost{(orig:monad.EVMOpSem.block.block_account)
           (asm:monad.proofs.exec_specs.AssumptionExactness)
           (idx:monad.proofs.exec_specs.Indices)}
    this |-> AccountStateR 1 orig asm idx
  \post{(r:ptr)} [Vptr r] emp
).

(*======== VersionStack<AccountState>::recent() =============================*)
cpp.spec "monad::VersionStack<monad::AccountState>::recent()" as vs_recent_spec with (fun (this:ptr) =>
  \pre this |-> (* TOFIXLATER: Rep for VersionStack<AccountState> *) emp
  \post{(r:ptr)} [Vptr r] emp
).

(*======== State::relaxed_validation() const ================================*)
cpp.spec "monad::State::relaxed_validation() const" as relaxed_validation_spec with (fun (this:ptr) =>
  \prepost{(au:monad.proofs.exec_specs.AssumptionsAndUpdates)}
    this |-> monad.proofs.exec_specs.StateR au
  \post{(b:bool)} [Vbool b] emp
).

(*======== VersionStack<AccountState>::size() const =========================*)
cpp.spec "monad::VersionStack<monad::AccountState>::size() const" as vs_size_spec with (fun (this:ptr) =>
  \pre this |-> (* TOFIXLATER: Rep for VersionStack<AccountState> *) emp
  \post{(n:Z)} [Vint n] emp
).

(*======== AccountState::validate_exact_balance() const =====================*)
cpp.spec "monad::AccountState::validate_exact_balance() const" as validate_exact_balance_spec with (fun (this:ptr) =>
  \prepost{(orig:monad.EVMOpSem.block.block_account)
           (asm:monad.proofs.exec_specs.AssumptionExactness)
           (idx:monad.proofs.exec_specs.Indices)}
    this |-> AccountStateR 1 orig asm idx
  \post{(b:bool)} [Vbool b] emp
).

(*======== AccountState::validate_exact_nonce() const =======================*)
cpp.spec "monad::AccountState::validate_exact_nonce() const" as validate_exact_nonce_spec with (fun (this:ptr) =>
  \prepost{(orig:monad.EVMOpSem.block.block_account)
           (asm:monad.proofs.exec_specs.AssumptionExactness)
           (idx:monad.proofs.exec_specs.Indices)}
    this |-> AccountStateR 1 orig asm idx
  \post{(b:bool)} [Vbool b] emp
).

(*======== detail::table::find(const address&) ==============================*)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address,monad::VersionStack<monad::AccountState>,ankerl::unordered_dense::v4_1_0::hash<evmc::address,void>,std::equal_to<evmc::address>,std::allocator<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>>,ankerl::unordered_dense::v4_1_0::bucket_type::standard,1b>::find(const evmc::address&)"
  as table_find_spec with (fun (this:ptr) =>
    \pre this |-> structR
       "ankerl::unordered_dense::v4_1_0::detail::table<evmc::address, monad::VersionStack<monad::AccountState>, ankerl::unordered_dense::v4_1_0::hash<evmc::address, void>, std::equal_to<evmc::address>, std::allocator<std::pair<evmc::address, monad::VersionStack<monad::AccountState>>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"
       1$m
    \arg{addrp} "key" (Vptr addrp)
    \pre{(key_model: monad.proofs.evmopsem.evm.address)}
      addrp |-> addressR 1 key_model
    \post{(r:ptr)} [Vptr r] emp
  ).

(*======== Incarnation copy‐ctor ============================================*)
cpp.spec "monad::Incarnation::Incarnation(const monad::Incarnation&)" as incarnation_copy_spec with (fun (this:ptr) =>
  \arg{otherp:ptr} "o" (Vptr otherp)
  \pre{(idx:monad.proofs.exec_specs.Indices)}
    otherp |-> IncarnationR 1 idx
  \post this |-> IncarnationR 1 idx
).

(*======== intx::uint<256u> destructor =====================================*)
cpp.spec "intx::uint<256u>::~uint()" as u256_dtor_spec with (fun (this:ptr) =>
  \pre{(n:Corelib.Numbers.BinNums.N)} this |-> u256R 1 n
  \post emp
).

(*======== iterator destructor =============================================*)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>,std::allocator<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>>,4096ul>::iter_t<0b>::~iter_t()"
  as iter_dtor_spec with (fun (this:ptr) =>
    \pre this |-> (* same as iter *) emp
    \post emp
  ).

(*======== iterator operator->() const =====================================*)
cpp.spec
  "ankerl::unordered_dense::v4_1_0::segmented_vector<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>,std::allocator<std::pair<evmc::address,monad::VersionStack<monad::AccountState>>>,4096ul>::iter_t<0b>::operator->() const"
  as iter_op_arrow_spec with (fun (this:ptr) =>
    \pre this |-> (* iter *) emp
    \post{(r:ptr)} [Vptr r] emp
  ).

(*======== intx::uint<256u> operator= ========================================*)
cpp.spec "intx::uint<256u>::operator=(const intx::uint<256u>&)" as u256_op_eq_spec with (fun (this:ptr) =>
  \arg{otherp:ptr} "o" (Vptr otherp)
  \pre{(n m: Corelib.Numbers.BinNums.N)}
    this |-> u256R 1 n ** otherp |-> u256R 1 m
  \post this |-> u256R 1 m
).

(*======== intx::uint<256u> operator+= ======================================*)
cpp.spec "intx::uint<256u>::operator+=(const intx::uint<256u>&)" as u256_op_add_assign_spec with (fun (this:ptr) =>
  \arg{otherp:ptr} "o" (Vptr otherp)
  \pre{(n m: Corelib.Numbers.BinNums.N)}
    this |-> u256R 1 n ** otherp |-> u256R 1 m
  \post emp (* TOFIXLATER: this |-> u256R 1 (n+m mod 2^256) *)
).

(*======== intx::uint<256u> operator-= ======================================*)
cpp.spec "intx::uint<256u>::operator-=(const intx::uint<256u>&)" as u256_op_sub_assign_spec with (fun (this:ptr) =>
  \arg{otherp:ptr} "o" (Vptr otherp)
  \pre{(n m: Corelib.Numbers.BinNums.N)}
    this |-> u256R 1 n ** otherp |-> u256R 1 m
  \post this |-> u256R 1 (n-m mod 2^256)
).

(*======== free intx::operator- on uint<256> =================================*)
cpp.spec "intx::operator-(const intx::uint<256u>&,const intx::uint<256u>&)" as u256_op_sub_spec with (
  \arg{a1p} "a" (Vptr a1p)
  \arg{a2p} "b" (Vptr a2p)
  \pre{(n1 n2:Corelib.Numbers.BinNums.N)}
    a1p |-> u256R 1 n1 ** a2p |-> u256R 1 n2
  \post{(r:ptr)} [Vptr r] r |-> u256R 1 (n1 - n2)
).

(*======== free comparison operators on uint<256> ==========================*)
cpp.spec "intx::operator==(const intx::uint<256u>&,const intx::uint<256u>&)" as u256_op_eqval_spec with (
  \arg{a1p} "a" (Vptr a1p)
  \arg{a2p} "b" (Vptr a2p)
  \pre{(n1 n2:Corelib.Numbers.BinNums.N)}
    a1p |-> u256R 1 n1 ** a2p |-> u256R 1 n2
  \post{(b:bool)} [Vbool b] [| b = true <-> n1 = n2 |]
).




  
  Set Nested Proofs Allowed.


Lemma prf: verify[module] fix_spec.
Abort.

  (*
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




## Assistant 6

I need to discover any existing `Rep`‐predicates or spec‐stubs for these C++ iterator and table types. Let me search our exec_specs library for occurrences of “segmented” and “table” which might reveal how we represent those iterator and container types:

```coqquery
Search segmented in monad.proofs.exec_specs.
Search table in monad.proofs.exec_specs.
```
*)
