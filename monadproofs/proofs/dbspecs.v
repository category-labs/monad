(* TODO: put most Imports in a prelude *)
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

(* models parts of Block and  MonadConsensusBlockHeader that are relevant for DB specs. *)
Record Proposal :=
  {
    roundNumber: N;
    proposedBlock: Block;
    (* delayed_execution_results is not really relevant because we know that last_verified=last_finalized+3 and we enforce this constraint logicall in these specs *)
  }.

(* models the state changed by Db::set_block_and_round *)
Inductive ActiveBlock :=
(* TODO: add | preGenesis *)
| finalized (block_number: N)
| proposalForNextBlock (block_number: N) (round_number:N).

Record DbModel : Type :=
  {
    finalizedBlocks: list (Block * evm.GlobalState); 
    nextBlockProposals:  list (Proposal * evm.GlobalState);
    activeBlock: ActiveBlock;
    (*^ changed by set_block_and_round *)
    votedMetadata: option (N * N);
    (*^ (block_num, round) from latest update_voted_metadata *)
    lastFinButNotYetVerified: bool;
    (*^ transient state where db.finalize(n+3) has been called but db.verify(n) has not yet been called: will be called soon *)
    cinvGloc: gname;
  }.

#[only(lens)] derive DbModel.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)

  Context  {MODd : exb.module ⊧ CU}.
  Compute (find_struct "monad::Db" module).

  
  Definition bnumber (b: Block) : N := number (header b).
  Open Scope Z_scope.
  Fixpoint contiguousBlocksStartingFrom (oblockIndex: option Z) (l: list Block) : Prop :=
    match l with
    | [] => True
    | h::tl => match oblockIndex with
               | Some blockIndex => Z.to_N blockIndex = bnumber h /\ contiguousBlocksStartingFrom (Some (blockIndex - 1)) tl
               | None => contiguousBlocksStartingFrom (Some (bnumber h - 1)) tl
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

  Definition validProposal (proposal: Proposal) (lastFin: option N) :=
    match lastFin with
    | Some lastFinBlock =>
        (bnumber (proposedBlock proposal) = 1 + lastFinBlock)%N
    | None => bnumber (proposedBlock proposal) = 0%N (* TODO: is this correct? I guess when we start the system, there will always be the finalized genesisd block? *)
    end.
      

  Open Scope N_scope.
  Definition lastVerified (lastFinalized: option N) : option N :=
    match lastFinalized with
    | Some lastFinBlock  =>
        if (bool_decide (lastFinBlock < 3))
        then None
        else Some (lastFinBlock -3)
    | None => None
    end.
    
  Definition lastFinalizedBlockIndex' (finalizedBlocks: list Block) : option N :=
    match head finalizedBlocks with
    | Some lastFinBlock =>
        Some (bnumber lastFinBlock)
    | _  => None
    end.
  
  Definition lastFinalizedBlockIndex (m: DbModel) : option N :=
    lastFinalizedBlockIndex' (map fst (finalizedBlocks m)).

  Definition validModel (m: DbModel) : Prop :=
    contiguousBlocksStartingFrom None (map fst (finalizedBlocks m))
    /\ forall (p:Proposal), p ∈ (map fst (nextBlockProposals m)) -> validProposal p (lastFinalizedBlockIndex m)
   /\ NoDup (map (roundNumber ∘ fst) (nextBlockProposals m)) (* TODO: Fix: Maged says there can be multiple proposals for the same round number. TODO: are proposals expected in the order of roundnumber.  ? *)
    /\ validActiveBlock m. (* needs to also say that the evm.GlobalState parts are obtained by executiing EVM semantics of a block on the state at the end of the previous block, but maybe that is the client's responsibility? the db can be agnostig to the execution mechanism *)

  Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
  

  Definition stateAfterLastFinalized (m: DbModel) : evm.GlobalState :=
    match head (finalizedBlocks m) with
    | Some lastFinBlock =>
        hd dummyEvmState (map snd (finalizedBlocks m))
    | _  => dummyEvmState (* validModel rules this case out *)
    end.
  
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

  Open Scope N_scope.
  cpp.spec "monad::Db::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \pre [| lastFinButNotYetVerified preDb = false |]
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \pre True (* roundNum should have been commited before *) 
      \pre match lastFinalizedBlockIndex preDb with
           | Some lastFinIndex => [| blockNum = 1+ lastFinIndex |]
           | None => True (* TODO *)
           end
      \post this |-> dbAuthR q (preDb &: _activeBlock .= finalized blockNum)).

  cpp.spec "monad::Db::update_verified_block(unsigned long)"
    as update_verified_block_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \pre [| lastFinButNotYetVerified preDb = true |]
      \pre [| Some blockNum = lastVerified (lastFinalizedBlockIndex preDb) |]
      \post this |-> dbAuthR q (preDb &: _lastFinButNotYetVerified .= false)).

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

Compute (lookup_struct module "monad::Db").

Definition commitFn : name:=
  "monad::Db::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)".
Check CodeDeltaR.
(** Compute the post-commit DbModel from pre-commit model and all commit arguments. *)


(** Compute the post-commit DbModel by prepending the new proposal and its state.
    Note: we do not record [rs] in the model (no field to hold transaction results). *)
Definition commit_model2
  (preDb      : DbModel)
  (newBlock   : Proposal)
  (finalState : monad.proofs.evmopsem.StateOfAccounts)
  (rs         : list monad.proofs.evmopsem.TransactionResult)
  : DbModel :=
  preDb
    &: _nextBlockProposals .=
      ((Build_Proposal (roundNumber newBlock) (proposedBlock newBlock), finalState)
         :: nextBlockProposals preDb).
(*
# round numbers are disjoint even across 
lastFinalizes (101, 201)
commit (102, 202)                
commit (103, 203)
commit (103, 203)
commit (103, 204)
finalize(102,202)
*)

cpp.spec
  "monad::Db::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
  as commit_spec with (fun (this:ptr) =>
    \prepost{(preDb:DbModel)} this |-> dbAuthR 1 preDb

    \arg{(deltas_ptr: ptr) (qs: Qp)} "#0" (Vptr deltas_ptr)
    \prepost{(finalState: StateOfAccounts)}
      deltas_ptr |-> StateDeltasR qs (stateAfterLastFinalized preDb, finalState)

    \arg{(code_ptr:ptr) (qcd: Qp)} "#1" (Vptr code_ptr)
    \prepost
      code_ptr |-> CodeDeltaR qcd (stateAfterLastFinalized preDb, finalState)

    \arg{hdr_ptr} "#2" (Vptr hdr_ptr)
    \prepost{(newProposal: Proposal) (qpr: Qp)}
      hdr_ptr |-> BheaderR qpr (header (proposedBlock newProposal))
    \pre [| validProposal newProposal (lastFinalizedBlockIndex preDb) |]
    \pre [| roundNumber newProposal ∉ (map (roundNumber ∘ fst) (nextBlockProposals preDb)) |] (* delete *)

    \arg{receipts_ptr} "#3" (Vptr receipts_ptr)
    \prepost{(rs: list monad.proofs.evmopsem.TransactionResult) (qtrs: Qp)}
      receipts_ptr |->
        monad.proofs.libspecs.VectorR
          "monad::Receipt"%cpp_type
          (fun r => monad.proofs.exec_specs.ReceiptR r)
          qtrs rs

   \arg{cfs_ptr} "#4" (Vptr cfs_ptr)
   (*       
    \prepost
      cfs_ptr |->
        monad.proofs.libspecs.VectorR
          "std::vector<monad::CallFrame>"%cpp_type
          (fun inner => emp)
          q []
          *)
    \arg{(senders_ptr: ptr) (qsn: Qp)} "#5" (Vptr senders_ptr)
    \prepost
      senders_ptr |->
        monad.proofs.libspecs.VectorR
          "evmc::address"%cpp_type
          (fun a => addressR qsn a)
          qsn (map sender (transactions (proposedBlock newProposal)))

    \arg{txns_ptr qtxn} "#6" (Vptr txns_ptr)
    \prepost
      txns_ptr |->
        monad.proofs.libspecs.VectorR
          "monad::Transaction"%cpp_type
          (fun t => monad.proofs.exec_specs.TransactionR qtxn t)
          qtxn (transactions (proposedBlock newProposal))

    \arg{ommers_ptr qo} "ommers" (Vptr ommers_ptr)
    \prepost
      ommers_ptr |->
        monad.proofs.libspecs.VectorR
          "monad::BlockHeader"%cpp_type
          (fun h => BheaderR qo h)
          qo (ommers (proposedBlock newProposal))

    \arg{wds_ptr} "#8" (Vptr wds_ptr)
    (*      
    \prepost{(ws: option (list monad.proofs.evmopsem.Withdrawal)))}
      wds_ptr |-> monad.proofs.libspecs.optionR
        "std::vector<monad::Withdrawal>"%cpp_type
        (fun ws => monad.proofs.libspecs.VectorR
                     "monad::Withdrawal"%cpp_type
                     (fun _ => pureR True) (* TOFIXLATER: refine to WithdrawalR *)
                     q ws)
        q ws
     *)   
    \post this |-> dbAuthR 1 (commit_model2 preDb newProposal finalState rs)
  ). 
(**
Above in this file, there is a dummy definition commit_model. write commit_model2 which actually fills the body propery. remember, you cannot change the content in this file above.
use the background provided above about the Db setup in monad in the section "Monad DB: Two‑Layer Architecture & Client Patterns".

+++ FILES
../fmai/prompts/sep.md
../fmai/prompts/specs.md
../../dbsummary2.md
+++ QUERIES

Compute (lookup_struct module "monad::Db").
Print exec_specs.
Print libspecs.
 *)
 Set Printing FullyQualifiedNames.

  
End with_Sigma.
