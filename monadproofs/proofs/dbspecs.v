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
  Open Scope N_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.
Require Import List.
Require Import bluerock.auto.cpp.
Require Import bluerock.auto.cpp.specs.
Require Import monad.proofs.exec_specs.

Record ConsensusBlockHeader :=
  {
    roundNum:N;
    (* TODO: add more fields *)
  }.
    
Notation EvmState := evm.GlobalState.

Record ProposalInDb :=
  {
    cheader: ConsensusBlockHeader;
    proposedBlock: Block;
    postBlockState: EvmState;
  }.
    
(* Todo: replace by ConsensusProposal
Record Proposal :=
  {
    roundNumber: N;
    proposedBlock: Block;
    (* delayed_execution_results is not really relevant because we know that last_verified=last_finalized+3 and we enforce this constraint logicall in these specs *)
  }.
 *)

Record BlockIndexState :=
  {
    unfinalizedProposals: list ProposalInDb;
    finalizedProposal : option ProposalInDb
  }.
    
Record ProposalId :=
  {
    idBlockNumber : N;
    idRoundNumber: option N;
  }.
    
Record DbModel : Type :=
  {
    blockIndicesStates: list BlockIndexState;
    
    activeProposal: option ProposalId;
    (*^ changed by set_block_and_round. None means set_block_and_round has never been called on this object yet *)
    
    votedMetadata: option (N * N);
    (*^ (block_num, round) from latest update_voted_metadata *)
    
    lastVerifiedBlockIndex: N;
    
    cinvId: gname;
    (* ^ Coq-specific detail: logical id of the concurrency invariant. there is no C++ analog of this *)
  }.

Definition allProposals (b: BlockIndexState) :=
  match finalizedProposal b with
  | None => (unfinalizedProposals b)
  | Some p => p::(unfinalizedProposals b)
  end.

Definition pblockNumber (p: ProposalInDb):=  number (header (proposedBlock p)).

Definition blockNumber (b: BlockIndexState) : N:=
  match allProposals b with
  | h::_ => pblockNumber h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

Definition proposalsHaveSameBlockNumber (b: BlockIndexState) :=
  forall (p1 p2: ProposalInDb),
    p1 ∈ (allProposals b)
    -> p2 ∈ (allProposals b)
    -> pblockNumber p1 = pblockNumber p2.

Definition hasAtLeastOneProposal (b: BlockIndexState) :=
  exists p: ProposalInDb, p ∈ (allProposals b).

Notation NoDuplicate := NoDup.

Definition validBlockIndexState  (b: BlockIndexState) :=
  hasAtLeastOneProposal b
  /\ proposalsHaveSameBlockNumber b
  /\ NoDuplicate (map (roundNum ∘ cheader) (allProposals b)).

Definition contiguousBlockNumbers (lb: list BlockIndexState) : Prop :=
  exists lowestBlockNumber:N,
    map blockNumber lb = seqN lowestBlockNumber (lengthN lb).

Definition lowestBlockNumber (d: DbModel) : N:=
  match blockIndicesStates d with
  | h::_ => blockNumber h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

(* upstream *)
Definition nthElem {A:Type} (l: list A) (n:N) : option A :=
  nth_error l (N.to_nat n).
    
             
Definition lookupBlockByNumber (bnum: N) (d: DbModel) : option BlockIndexState :=
  if bool_decide (bnum <= lowestBlockNumber d /\ 0 < lengthN (blockIndicesStates d))%N
  then nthElem (blockIndicesStates d) (bnum - lowestBlockNumber d)
  else None.

Definition lookupProposalByRoundNum (b: BlockIndexState) (rnum: N) : option ProposalInDb :=
  match List.filter (fun p => bool_decide (roundNum (cheader p) = rnum)) (allProposals b) with
  | h::tl => Some h (* [validBlockIndexState b] -> tl = [] *)
  | [] => None
  end.
    
Definition lookupProposal (id: ProposalId)  (d: DbModel) : option ProposalInDb :=
  match lookupBlockByNumber (idBlockNumber id) d with
  | None => None
  | Some b =>
      match idRoundNumber id with
      | None => finalizedProposal b
      | Some rnum => lookupProposalByRoundNum b rnum
      end
  end.      

Definition lookupActiveProposal (d: DbModel) : option ProposalInDb :=
  match activeProposal d with
  | None => None
  | Some ap => lookupProposal ap d
  end.
    
Definition validActiveProposal  (m: DbModel) : Prop :=
  match activeProposal m with
  | None => True
  | Some pid => isSome (lookupProposal pid m)
  end.                       

(*
Definition validProposal (proposal: Proposal) (lastFin: option N) :=
    match lastFin with
    | Some lastFinBlock =>
        (bnumber (proposedBlock proposal) = 1 + lastFinBlock)%N
    | None => bnumber (proposedBlock proposal) = 0%N (* TODO: is this correct? I guess when we start the system, there will always be the finalized genesisd block? *)
    end.
*)    

(*
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
 *)

Definition validModel (m: DbModel) : Prop :=
  contiguousBlockNumbers (blockIndicesStates m)
  /\ validActiveProposal m. (* may need to also say that the evm.GlobalState parts are obtained by executiing EVM semantics of a block on the state at the end of the previous block, but maybe that is the client's responsibility? the db can be agnostig to the execution mechanism *)

  Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
  
(*
Definition stateAfterLastFinalized (m: DbModel) : evm.GlobalState :=
match head (finalizedBlocks m) with
| Some lastFinBlock =>
hd dummyEvmState (map snd (finalizedBlocks m))
| _  => dummyEvmState (* validModel rules this case out *)
end.
 *)
  
Definition stateAfterActiveProposal (m: DbModel) : evm.GlobalState :=
  match lookupActiveProposal m with
  | None => dummyEvmState
  | Some p => postBlockState p
  end.
  

(** ignore the next 4 lines: Coq boilerplate *)
Open Scope Z_scope.
#[only(lens)] derive DbModel.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
  Context  {MODd : exb.module ⊧ CU}.
  
  
  (** contains the auth ownership of monad::mpt::Db in-memory datastructures AND also the on-disk datastructures. there can be only 1 object owning the on-disk data at any given time. full 1 fraction is needed to update the state. this ownership [dbAuthR 1 _] is disjoint from [dbFragR] below. The latter can be used to read the database even when some other thread owns [dbAuthR 1 _]: the actual ownership of the disk/memory lives in a concurrent invariant *)
  Definition TrieDBR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (* Knowledge (no resource ownership) *)
  Definition SelectedProposalForBlockNum (blockNumber: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (* cannot use if different proposals can be done for the same round number *)
  Definition ProposedInRoundNum (roundNumber: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (* all reads will read from activeProposal, which is determined at TrieRODB::set_block_and_round *)
  Definition TrieRODBR (q:Qp) (activeProposal: option ProposalInDb) : Rep. Proof. Admitted.

  Notation dbAuthR := TrieDBR. (* TODO: inline *)

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
      \post{retp:ptr} [Vptr retp]  retp |-> bytes32R 1 (lookupStorage (stateAfterActiveProposal preDb) address key blockTxInd)).

  Definition MaxRoots : N. Proof. Admitted.

  
  Open Scope N_scope.
  Search compose.
  cpp.spec "monad::Db::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDBR q preDb
      \pre [| lastFinButNotYetVerified preDb = false |]
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \pre [| roundNum ∈ map (roundNumber ∘ fst) (nextBlockProposals preDb) |]
      \pre [| lengthN (nextBlockProposals preDb) < MaxRoots |]%N
      \pre match lastFinalizedBlockIndex preDb with
           | Some lastFinIndex => [| blockNum = 1+ lastFinIndex |]
           | None => True (* TODO: only allowed when the state was in pre genesis *)
           end
      \post this |-> TrieDBR q (preDb &: _activeBlock .= finalized blockNum)).
  (* no finalize in triedb *)
  

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
write the spec of monad::Db::set_block_and_round.
Unfortunately, CppDefnOf is currrently not working so you can only issue Coq queries not clangd queries.

Start the spec as:

cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)" 


+++ FILES
../../../fmdeps/fmai/prompts/sep.md
../../../fmdeps/fmai/prompts/specs.md
../../dbsummary2.md
+++ QUERIES

Compute (lookup_struct module "monad::Db").
Print exec_specs.
Print libspecs.
 *)
 Set Printing FullyQualifiedNames.
(* ---------- Filled‐in hole: optional std::optional<unsigned long> ---------- *)

(* We use the Rep‐predicate `optionR` from the `libspecs` module. *)
Definition optionalULongR (q: cQp.t) (o: option N) : Rep :=
  @libspecs.optionR _ _ _ CU
    N                                        (* SomeTyModel *)
    ("unsigned long"%cpp_type)               (* C++ type of the payload *)
    (fun n => primR "unsigned long"%cpp_type  (* how to represent each N *)
                   q
                   (Vint (Z.of_N n)))
    (cQp.mut 1)                              (* fraction of ownership *)
    o.

(* ---------- Spec of set_block_and_round ---------- *)

cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as set_block_and_round_spec with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preDb} this |-> dbAuthR q preDb

    (* block_number: unsigned long *)
    \arg{blockNum:N} "block_number" (Vint blockNum)

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
      (roundLoc |-> optionalULongR (cQp.mut 1) roundOpt)

    \pre [| match roundOpt with
           | Some rn => rn ∈ map (roundNumber ∘ fst) (nextBlockProposals preDb)
           | None => blockNum ∈ map (bnumber ∘ fst) (finalizedBlocks preDb) (* what if this has already been garbage collected? return a bool error? *)
           end |]

    (* On return, activeBlock is updated accordingly *)
    \post this |-> dbAuthR q
      (preDb &: _activeBlock .=
        match roundOpt with
        | None    => finalized blockNum
        | Some rn => proposalForNextBlock blockNum rn
        end
      )
  ).


Set Printing FullyQualifiedNames.


  
End with_Sigma.
