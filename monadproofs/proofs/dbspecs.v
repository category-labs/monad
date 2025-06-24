Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bluerock.lang.cpp.cpp.
Require Import stdpp.gmap.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Print block.step.
Print evm.network.
Import linearity.
Require Import monad.asts.exb.
Require Export bluerock.auto.cpp.spec.

Require Import monad.proofs.libspecs.
Import cQp_compat.
#[local] Open Scope lens_scope.

#[local] Open Scope Z_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.
Require Import List.
Require Import bluerock.auto.cpp.
Require Import bluerock.auto.cpp.specs.
Require Import monad.proofs.exec_specs.

Record Proposal :=
  {
    roundNumber: N;
    proposedBlock: Block
  }.

Inductive ActiveBlock :=
| finalized (block_number: N)
| proposalForNextBlock (block_number: N) (round_number:N).


Record DbModel : Type :=
  {
    finalizedBlocks: list (Block * evm.GlobalState); (* dbAuthR asserts that the indices of these blocks must be contiguous. head is the latest finalized block. snd component is the state JUST AFTER executing the block *)
    nextBlockProposals:  list (Proposal * evm.GlobalState);
    activeBlock: ActiveBlock;        (* changed by set_block_and_round *)
    verifiedBlock: option N;         (* latest verified block id, updated by update_verified_block *)
    votedMetadata: option (N * N);   (* (block_num, round) from latest update_voted_metadata *)
    cinvGloc: gname;
  }.

#[only(lens)] derive DbModel.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

  Context  {MODd : exb.module ⊧ CU}.
  Compute (find_struct "monad::Db" module).

  
  Definition bnumber (b: Block) : N := number (header b).
  Open Scope Z_scope.
  Fixpoint contiguousBlocksStartingFrom (oblockIndex: option Z) (l: list (Block * evm.GlobalState)) : Prop :=
    match l with
    | [] => True
    | h::tl => match oblockIndex with
               | Some blockIndex => Z.to_N blockIndex = bnumber (fst h) /\ contiguousBlocksStartingFrom (Some (blockIndex - 1)) tl
               | None => contiguousBlocksStartingFrom (Some (bnumber (fst h) - 1)) tl
               end
                 
    end.

  Definition validActiveBlock  (m: DbModel) : Prop :=
    match activeBlock m with
    | finalized blockNum =>
        match head (finalizedBlocks m), last (finalizedBlocks m) with
        | Some lastFinBlock, Some oldestFinalizedBlockInDb =>
            (bnumber (fst oldestFinalizedBlockInDb) <= blockNum <= bnumber (fst lastFinBlock))%Z
        | _ , _ => False (* this case hits when the [(finalizedBlocks m)] is empty *)
        end
    | proposalForNextBlock blockNum roundNum =>
        match head (finalizedBlocks m) with
        | Some lastFinBlock => (Z.of_N blockNum = 1 + bnumber (fst lastFinBlock))
        | None => True (* no block has been finalized yet. TODO: should blockNum be 0 in this case? *)
        end /\ roundNum < lengthZ (nextBlockProposals m)
    end.

  Definition validModel (m: DbModel) : Prop :=
    contiguousBlocksStartingFrom None (finalizedBlocks m)
    /\ validActiveBlock m. (* needs to also say that the evm.GlobalState parts are obtained by executiing EVM semantics of a block on the state at the end of the previous block *)

  Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
  
  Definition stateAfterActiveBlock (m: DbModel) : evm.GlobalState :=
    match activeBlock m with
    | finalized blockNum =>
        match head (finalizedBlocks m) with
        | Some lastFinBlock =>
            let offset := bnumber (fst lastFinBlock) - blockNum in
            nth (Z.to_nat offset) (map snd (finalizedBlocks m)) dummyEvmState
        | _  => dummyEvmState (* validModel rules this case out *)
        end
    | proposalForNextBlock _ roundNum =>
        nth (Z.to_nat roundNum) (map snd (nextBlockProposals m)) dummyEvmState
    end.
  (** contains the auth ownership of monad::mpt::Db in-memory datastructures AND also the on-disk datastructures. there can be only 1 object owning the on-disk data at any given time. full 1 fraction is needed to update the state. this ownership [dbAuthR 1 _] is disjoint from [dbFragR] below. The latter can be used to read the database even when some other thread owns [dbAuthR 1 _]: the actual ownership of the disk/memory lives in a concurrent invariant *)
  Definition dbAuthR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (* when we fill in the definition of dbAuthR, we must ensure the lemmas below are provable *)
  Lemma dbAuthREntails (q:Qp) (m: DbModel) : dbAuthR q m |--  dbAuthR q m ** [| validModel m|].
  Proof. Admitted.
                                                     
  (** Raw db ownersip (the part that is remaining after dbAuthR above), shared with RODb instances. can use this to construct trie_rodb. RPC and statesync server(s) use fractions of this ownership to read the on-disk data *)
  Definition dbFragR  (q:Qp) : mpred. Proof. Admitted.

  cpp.spec "monad::Db::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{addressp} "address" (Vptr addressp)
      \prepost{q address} addressp |-> addressR q address
      \arg{incp} "incarnation" (Vptr incp)
      \prepost{q blockTxInd} incp |-> IncarnationR q blockTxInd
      \arg{keyp} "key" (Vptr keyp)
      \prepost{key:N} keyp |-> bytes32R q key
      \post{retp:ptr} [Vptr retp]  retp |-> bytes32R 1 (exec_specs.lookupStorage (stateAfterActiveBlock preDb) address key blockTxInd)).

  cpp.spec "monad::Db::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \post this |-> dbAuthR q (preDb &: _activeBlock .= finalized blockNum)).

  cpp.spec "monad::Db::update_verified_block(unsigned long)"
    as update_verified_block_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \post this |-> dbAuthR q (preDb &: _verifiedBlock .= Some blockNum)).

  cpp.spec "monad::Db::update_voted_metadata(unsigned long, unsigned long)"
    as update_voted_metadata_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round"        (Vint roundNum)
      \post this |-> dbAuthR q (preDb &: _votedMetadata .= Some (blockNum, roundNum))).

  Definition stateRoot (b: Block) : N. Proof. Admitted.
  Definition receiptRoot (b: Block) : N. Proof. Admitted.
  Definition transactionsRoot (b: Block) : N. Proof. Admitted.
  Definition withdrawalsRoot (b: Block) : N. Proof. Admitted.

(**
Write the spec of monad::Db::commit

To write specs, you need to know the the Rep predicates for the types of the arguments.
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
- CodeDeltaR is the Rep predcate of (Code =    oneapi::tbb::concurrent_hash_map<bytes32_t, std::shared_ptr<CodeAnalysis>>)
- StateDeltasR is the Rep predicate of StateDeltaR.
- StateDeltaR for StateDelta

Unfortunately, currently there is no query to search for the Rep predicate of a c++ type.
Unfortunately, CppDefnOf queries are currently not available.

+++ FILES
../fmai/prompts/sep.md
../fmai/prompts/specs.md

+++ QUERIES

Compute (lookup_struct module "monad::Db").
Print exec_specs.
 *)
 Set Printing FullyQualifiedNames.
Import exec_specs.
Import bluerock.lang.cpp.logic.rep_defs.

(* ---------------------------------------------------------------------- *)
(* TOFIXLATER: unique_ptr<> rep for state_deltas & code_map *)
Parameter uptr_state_deltas_R
  : Qp
  → monad.proofs.evmopsem.StateOfAccounts * monad.proofs.evmopsem.StateOfAccounts
  → Rep.
Parameter uptr_code_map_R
  : Qp
  → stdpp.gmap.gmap Corelib.Numbers.BinNums.N (list Corelib.Numbers.BinNums.N)
  → Rep.
(* ---------------------------------------------------------------------- *)

(* A generic vector<T> rep predicate *)
Parameter vectorR
  : ∀ {T}, (Qp → T → Rep)
         → Qp → list T → Rep.

(* TOFIXLATER: admit the pure‐model of CallFrame and its memory predicate *)
Parameter CallFrameModel : Type.                                                    (* TOFIXLATER *)
Parameter CallFrameR     : Qp → CallFrameModel → Rep.                               (* TOFIXLATER *)

(* TOFIXLATER: admit WithdrawalR and the C++ vector<Withdrawal> type *)
Parameter WithdrawalR       : Qp → monad.proofs.evmopsem.Withdrawal → Rep.           (* TOFIXLATER *)
Parameter withdrawalVecType : bluerock.lang.cpp.syntax.core.type.                    (* TOFIXLATER *)

(* Named wrapper for option<vector<Withdrawal>> *)
Definition WithdrawalOptionR (po: option (list monad.proofs.evmopsem.Withdrawal)) : Rep :=
  optionR
    withdrawalVecType
    (fun l => vectorR (fun _ w => WithdrawalR w) 1 l)
    1
    po.

(* Vector‐of‐Xs for the spec, as named helpers *)
Parameter ReceiptVecR     : Qp → list monad.proofs.evmopsem.TransactionResult → Rep.  (* TOFIXLATER *)
Parameter CallFrameVecR   : Qp → list CallFrameModel                       → Rep.  (* TOFIXLATER *)
Parameter AddressVecR     : Qp → list evm.address                         → Rep.  (* TOFIXLATER *)
Parameter TransactionVecR : Qp → list monad.proofs.evmopsem.Transaction    → Rep.  (* TOFIXLATER *)
Parameter BlockHeaderVecR : Qp → list monad.proofs.evmopsem.BlockHeader    → Rep.  (* TOFIXLATER *)

(* Model‐level update of DbModel by commit: to be defined later *)
Definition commit_model
  (m    : DbModel)
  (sd   : monad.proofs.evmopsem.StateOfAccounts * monad.proofs.evmopsem.StateOfAccounts)
  (cm   : stdpp.gmap.gmap Corelib.Numbers.BinNums.N (list Corelib.Numbers.BinNums.N))
  (hdr  : monad.proofs.evmopsem.BlockHeader)
  (rs   : list monad.proofs.evmopsem.TransactionResult)
  (cfs  : list (list CallFrameModel))
  (ss   : list evm.address)
  (txs  : list monad.proofs.evmopsem.Transaction)
  (obs  : list monad.proofs.evmopsem.BlockHeader)
  (wo   : option (list monad.proofs.evmopsem.Withdrawal))
  : DbModel.
Admitted. (* TOFIXLATER *)

cpp.spec
  "monad::Db::commit(std::unique_ptr<tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>, std::default_delete<tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>>>&, std::unique_ptr<tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>, std::default_delete<tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
  as commit_spec with (fun (this: ptr) =>
    \prepost{q preDb}    this |-> dbAuthR q preDb

    (* state_deltas unique_ptr *)
    \arg{sdptr}     "state_deltas"     (Vptr sdptr)
    \pre{sdp}       sdptr |-> uptr_state_deltas_R q sdp

    (* code map unique_ptr *)
    \arg{cmptr}     "code"             (Vptr cmptr)
    \pre{cmp}       cmptr |-> uptr_code_map_R q cmp

    (* consensus header *)
    \arg{hdrptr}    "consensus_header" (Vptr hdrptr)
    \pre{hdr}       hdrptr |-> BheaderR 1 hdr

    (* receipts *)
    \arg{receiptsp} "receipts"        (Vptr receiptsp)
    \pre{rs}        receiptsp |-> ReceiptVecR 1 rs

    (* call_frames *)
    \arg{cfsp}      "call_frames"     (Vptr cfsp)
    \pre{cfs}       cfsp   |-> CallFrameVecR 1 cfs

    (* senders *)
    \arg{sendersp}  "senders"         (Vptr sendersp)
    \pre{ss}        sendersp |-> AddressVecR 1 ss

    (* transactions *)
    \arg{txsp}      "transactions"    (Vptr txsp)
    \pre{txs}       txsp   |-> TransactionVecR 1 txs

    (* ommers *)
    \arg{ommersp}   "ommers"          (Vptr ommersp)
    \pre{obs}       ommersp |-> BlockHeaderVecR 1 obs

    (* optional withdrawals *)
    \arg{woptr}     "withdrawals"     (Vptr woptr)
    \pre{wo}        woptr |-> WithdrawalOptionR wo

    (* return updated dbAuthR *)
    \post this |-> dbAuthR q (commit_model preDb sdp cmp hdr rs cfs ss txs obs wo)
  ).




  
End with_Sigma.
