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
 Set Printing FullyQualifiedNames.
(* Convert Coq N to Coq Z *)
Definition N_to_Z (n: Corelib.Numbers.BinNums.N)
  : Corelib.Numbers.BinNums.Z :=
  Stdlib.ZArith.BinInt.Z.of_N n.

(* Helpers: convert 256-bit vectors to Z or N *)
Definition w256_to_Z (w: monad.EVMOpSem.keccak.w256)
  : Corelib.Numbers.BinNums.Z :=
  monad.EVMOpSem.Zdigits.binary_value 256 w.

Definition w256_to_N (w: monad.EVMOpSem.keccak.w256)
  : Corelib.Numbers.BinNums.N :=
  Stdlib.ZArith.BinInt.Z.to_N (w256_to_Z w).

(* Dummy placeholder: keys-only for accessed_storage_ *)
Definition AccessedKeysR (q: stdpp.numbers.Qp)
           (keys: list Corelib.Numbers.BinNums.N)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  (* TOFIXLATER: refine to layout each accessed key in the C++ table *)
  anyR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, void, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<evmc::bytes32>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 0b>"%cpp_type
    (cQp.mut q).

(* Dummy placeholder: persistent/transient storage map *)
Definition StorageMapR (q: stdpp.numbers.Qp)
           (m: monad.EVMOpSem.evm.storage)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  (* TOFIXLATER: refine to layout each key→value pair in the C++ map *)
  anyR
    "ankerl::unordered_dense::v4_1_0::detail::table<evmc::bytes32, evmc::bytes32, ankerl::unordered_dense::v4_1_0::hash<evmc::bytes32, void>, std::equal_to<evmc::bytes32>, std::allocator<std::pair<evmc::bytes32, evmc::bytes32>>, ankerl::unordered_dense::v4_1_0::bucket_type::standard, 1b>"%cpp_type
    (cQp.mut q).

(* Realistic placeholder for code_hash_of_program: length mod 2^256, converted to N *)
Definition code_hash_of_program
           (pr: monad.EVMOpSem.evm.program)
  : Corelib.Numbers.BinNums.N :=
  Stdlib.ZArith.BinInt.Z.to_N
    (monad.EVMOpSem.evm.program_length pr mod (2 ^ 256)%Z).

(* Rep predicate for monad::AccountSubstate (base class) *)
Definition AccountSubstateR (q: stdpp.numbers.Qp)
           (destructed touched accessed: bool)
           (accessed_keys: list Corelib.Numbers.BinNums.N)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  _field "AccountSubstate::destructed_"        |-> boolR (cQp.mut q) destructed
  ** _field "AccountSubstate::touched_"          |-> boolR (cQp.mut q) touched
  ** _field "AccountSubstate::accessed_"         |-> boolR (cQp.mut q) accessed
  ** _field "AccountSubstate::accessed_storage_" |-> AccessedKeysR q accessed_keys.

(* Rep predicate for monad::Account using block_account and Indices *)
Definition AccountR (q: stdpp.numbers.Qp)
           (ba: monad.EVMOpSem.block.block_account)
           (idx: monad.proofs.exec_specs.Indices)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  _field "monad::Account::balance"
        |-> u256R q (w256_to_N (ba.(monad.EVMOpSem.block.block_account_balance)))
  ** _field "monad::Account::code_hash"
        |-> bytes32R q (code_hash_of_program ba.(monad.EVMOpSem.block.block_account_code))
  ** _field "monad::Account::nonce"
        |-> primR "unsigned long" (cQp.mut q)
             (w256_to_Z (ba.(monad.EVMOpSem.block.block_account_nonce)))
  ** _field "monad::Account::incarnation"
        |-> monad.proofs.exec_specs.IncarnationR q idx.

(* Rep predicate for full monad::AccountState *)
Definition AccountStateR (q: stdpp.numbers.Qp)
           (orig:        monad.EVMOpSem.block.block_account)
           (asm:         monad.proofs.exec_specs.AssumptionExactness)
           (storage_map:   monad.EVMOpSem.evm.storage)
           (transient_map: monad.EVMOpSem.evm.storage)
           (idx:         monad.proofs.exec_specs.Indices)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  (* base substate *)
  _base "monad::AccountState" "monad::AccountSubstate"
    |-> AccountSubstateR q
         false false false (* destructed_, touched_, accessed_ start false *)
         []               (* accessed_storage_ initially empty *)
  (* account_ is a std::optional; placeholder anyR *)
  ** _field "monad::AccountState::account_"
        |-> anyR "std::optional<monad::Account>"%cpp_type (cQp.mut q) (* TOFIXLATER *)
  (* persistent storage_ *)
  ** _field "monad::AccountState::storage_"
        |-> StorageMapR q storage_map
  (* transient_storage_ *)
  ** _field "monad::AccountState::transient_storage_"
        |-> StorageMapR q transient_map
  (* exact-nonce flag *)
  ** _field "monad::AccountState::validate_exact_nonce_"
        |-> boolR (cQp.mut q) (monad.proofs.exec_specs.nonce_exact asm)
  (* exact-balance flag *)
  ** _field "monad::AccountState::validate_exact_balance_"
        |-> boolR (cQp.mut q)
             (Corelib.Init.Datatypes.negb
                (bool_decide (stdpp.option.is_Some (monad.proofs.exec_specs.min_balance asm))))
  (* min_balance_ bound *)
  ** _field "monad::AccountState::min_balance_"
        |-> u256R q
             (match monad.proofs.exec_specs.min_balance asm with
              | Corelib.Init.Datatypes.Some n => n
              | Corelib.Init.Datatypes.None   => 0%_N
              end).







  
  
 Set Printing FullyQualifiedNames.
Local Open Scope cpp_name.
Local Open Scope cpp_type.

(** * Rep for monad::Account **)
Definition AccountR (q: cQp.t)
  (bal : Corelib.Numbers.BinNums.N)
  (ch  : Corelib.Numbers.BinNums.N)
  (no  : Corelib.Numbers.BinNums.Z)
  (inc : monad.proofs.exec_specs.Indices)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  structR "monad::Account"%cpp_name q
  ** _field "monad::Account::balance"%cpp_name     |-> monad.proofs.exec_specs.u256R q bal
  ** _field "monad::Account::code_hash"%cpp_name   |-> monad.proofs.exec_specs.bytes32R q ch
  ** _field "monad::Account::nonce"%cpp_name       |-> primR "unsigned long"%cpp_type q (Vint no)
  ** _field "monad::Account::incarnation"%cpp_name |-> monad.proofs.exec_specs.IncarnationR q inc.

(** * Rep for the storage_ table **)
Definition StorageTableR (q: cQp.t)
  (_m: monad.EVMOpSem.evm.storage)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  pureR True.

(** * Rep for the transient_storage_ table **)
Definition TransientStorageR (q: cQp.t)
  (_m: monad.EVMOpSem.evm.storage)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  pureR True.

(** * Rep for the accessed_storage_ table **)
Definition AccessedStorageR (q: cQp.t)
  (_keys: list Corelib.Numbers.BinNums.N)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  pureR True.

(** * Rep for monad::AccountSubstate **)
Definition AccountSubstateR (q: cQp.t)
  (destructed touched accessed: bool)
  (acc_keys: list Corelib.Numbers.BinNums.N)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  structR "monad::AccountSubstate"%cpp_name q
  ** _field "monad::AccountSubstate::destructed_"%cpp_name       |-> boolR q destructed
  ** _field "monad::AccountSubstate::touched_"%cpp_name          |-> boolR q touched
  ** _field "monad::AccountSubstate::accessed_"%cpp_name         |-> boolR q accessed
  ** _field "monad::AccountSubstate::accessed_storage_"%cpp_name |-> AccessedStorageR q acc_keys.

(** * Rep for std::optional<monad::Account> **)
Definition OptionAccountR (q: cQp.t)
  (o: option (Corelib.Numbers.BinNums.N
             * Corelib.Numbers.BinNums.N
             * Corelib.Numbers.BinNums.Z
             * monad.proofs.exec_specs.Indices))
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  structR (Ninst "std::optional" [Atype "monad::Account"%cpp_type]) (cQp.mut q)
  ** match o with
     | None =>
        opt_engaged_offset "monad::Account"%cpp_type |-> boolR q false
     | Some (bal,ch,no,inc) =>
        opt_somety_offset     "monad::Account"%cpp_type |-> AccountR q bal ch no inc
        ** opt_engaged_offset "monad::Account"%cpp_type |-> boolR q true
     end.

(** * Rep for monad::AccountState **)
Definition AccountStateR (q: cQp.t)
  (opt_acc: option (Corelib.Numbers.BinNums.N
                   * Corelib.Numbers.BinNums.N
                   * Corelib.Numbers.BinNums.Z
                   * monad.proofs.exec_specs.Indices))
  (storage_m transient_m: monad.EVMOpSem.evm.storage)
  (d t a: bool)
  (acc_keys: list Corelib.Numbers.BinNums.N)
  (ass: monad.proofs.exec_specs.AssumptionExactness)
  : bluerock.lang.cpp.logic.rep_defs.Rep :=
  structR "monad::AccountState"%cpp_name q
  ** _base  "monad::AccountState"%cpp_name "monad::AccountSubstate"%cpp_name
       |-> AccountSubstateR q d t a acc_keys
  ** _field "monad::AccountState::account_"%cpp_name           |-> OptionAccountR q opt_acc
  ** _field "monad::AccountState::storage_"%cpp_name           |-> StorageTableR q storage_m
  ** _field "monad::AccountState::transient_storage_"%cpp_name |-> TransientStorageR q transient_m
  ** _field "monad::AccountState::validate_exact_nonce_"%cpp_name   |-> boolR q (ass.(nonce_exact))
  ** _field "monad::AccountState::validate_exact_balance_"%cpp_name |-> boolR q (isSome (ass.(min_balance)))
  ** _field "monad::AccountState::min_balance_"%cpp_name            |-> 
       monad.proofs.exec_specs.u256R q
         (match ass.(min_balance) with Some n => n | None => 0%N end).




  
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

