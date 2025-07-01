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
    txResults: list TransactionResult;
  }.
    
(* Todo: replace by ConsensusProposal
Record Proposal :=
  {
    roundNum: N;
    proposedBlock: Block;
    (* delayed_execution_results is not really relevant because we know that last_verified=last_finalized+3 and we enforce this constraint logicall in these specs *)
  }.
 *)

Record BlockNumStateInDb :=
  {
    proposals: list ProposalInDb;
    finalizedRoundNum : option N;
  }.
    
Record ProposalId :=
  {
    idBlockNum : N;
    idRoundNum: option N;
  }.
    
Record DbModel : Type :=
  {
    blockNumStates: list BlockNumStateInDb;
    
    activeProposal: option ProposalId;
    (*^ changed by set_block_and_round. None means set_block_and_round has never been called on this object yet *)
    
    votedMetadata: option (N * N);
    (*^ (block_num, round) from latest update_voted_metadata *)
    
    lastVerifiedBlockIndex: N;
    
    cinvId: gname;
    (* ^ Coq-specific detail: logical id of the concurrency invariant. there is no C++ analog of this *)
  }.

Definition pblockNum (p: ProposalInDb):=  number (header (proposedBlock p)).

Definition blockNum (b: BlockNumStateInDb) : N:=
  match proposals b with
  | h::_ => pblockNum h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

Definition proposalsHaveSameBlockNum (b: BlockNumStateInDb) :=
  forall (p1 p2: ProposalInDb),
    p1 ∈ (proposals b)
    -> p2 ∈ (proposals b)
    -> pblockNum p1 = pblockNum p2.

Definition hasAtLeastOneProposal (b: BlockNumStateInDb) :=
  exists p: ProposalInDb, p ∈ (proposals b).

Notation NoDuplicate := NoDup.

Definition validBlockNumStateInDb  (b: BlockNumStateInDb) :=
  hasAtLeastOneProposal b
  /\ proposalsHaveSameBlockNum b
  /\ NoDuplicate (map (roundNum ∘ cheader) (proposals b)).

Open Scope N_scope.
Definition contiguousBlockNums (lb: list BlockNumStateInDb) : Prop :=
  let blockNums := List.map blockNum lb in
  let maxBlockNum := maxL blockNums in 
  let minBlockNum := minL blockNums in
  forall blockNumber:N,  minBlockNum <= blockNumber <= maxBlockNum -> exists b, blockNum b = blockNumber /\ b ∈ lb.
                           

Definition lowestBlockNum (d: DbModel) : N:=
  match blockNumStates d with
  | h::_ => blockNum h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

(* upstream *)
Definition nthElem {A:Type} (l: list A) (n:N) : option A :=
  nth_error l (N.to_nat n).
             
Definition lookupBlockByNum (bnum: N) (d: DbModel) : option BlockNumStateInDb :=
  match List.filter (fun b => bool_decide (blockNum b= bnum)) (blockNumStates d) with
  | h::tl => Some h (* [validBlockNumStateInDb b] -> tl = [] *)
  | [] => None
  end.

Definition lookupProposalByRoundNum (b: BlockNumStateInDb) (rnum: N) : option ProposalInDb :=
  match List.filter (fun p => bool_decide (roundNum (cheader p) = rnum)) (proposals b) with
  | h::tl => Some h (* [validBlockNumStateInDb b] -> tl = [] *)
  | [] => None
  end.


Definition finalizedProposal (b : BlockNumStateInDb): option ProposalInDb :=
  match finalizedRoundNum b with
  | None => None
  | Some rnd => lookupProposalByRoundNum b rnd
  end.
     
Definition lookupProposal (id: ProposalId)  (d: DbModel) : option ProposalInDb :=
  match lookupBlockByNum (idBlockNum id) d with
  | None => None
  | Some b =>
      match idRoundNum id with
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

Definition splitL {A} (n:N) (l: list A) : (list A * (list A)) :=
  (takeN n l, dropN n l).

Definition validDbModel (m: DbModel) : Prop :=
  (forall b, b ∈ (blockNumStates m) -> validBlockNumStateInDb b)
  /\ contiguousBlockNums (blockNumStates m)
  /\ NoDuplicate (map blockNum (blockNumStates m))
  /\ validActiveProposal m
  /\ (exists numFinalized:N, let '(firstn, rest) := splitL numFinalized (blockNumStates m) in
         (forall b, b ∈ firstn -> isSome (finalizedProposal b))
         /\ (forall b, b ∈ rest -> isNone (finalizedProposal b))
     ).
       (* may need to also say that the evm.GlobalState parts are obtained by executiing EVM semantics of a block on the state at the end of the previous block, but maybe that is the client's responsibility? the db can be agnostig to the execution mechanism *)

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
  

Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N :=
  let unfin :=
    List.filter
      (fun b => match finalizedProposal b with
                | None => true | _ => false
                end)
      (blockNumStates d) in
  match unfin with
  | [] => None
  | _  => Some (minL (List.map blockNum unfin))
  end.

  (** updateBlockNum: update exactly the [BlockNumStateInDb] whose [blockNum]
       equals [bnum] by applying [f], leave others unchanged.
  *)
#[only(lens)] derive DbModel.
#[only(lens)] derive ProposalInDb.
#[only(lens)] derive BlockNumStateInDb.

  Definition updateBlockNum
             (d: DbModel)
             (bnum: N)
             (f: BlockNumStateInDb -> BlockNumStateInDb)
    : DbModel :=
    d &: _blockNumStates .= 
         List.map (fun b =>
                     if bool_decide (blockNum b = bnum)
                     then f b else b)
                  (blockNumStates d).

(** ignore the next 4 lines: Coq boilerplate *)
Open Scope Z_scope.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
  Context  {MODd : exb.module ⊧ CU}.
  
  
  (** contains the auth ownership of monad::mpt::Db in-memory datastructures AND also the on-disk datastructures. there can be only 1 object owning the on-disk data at any given time. full 1 fraction is needed to update the state. this ownership [dbAuthR 1 _] is disjoint from [dbFragR] below. The latter can be used to read the database even when some other thread owns [dbAuthR 1 _]: the actual ownership of the disk/memory lives in a concurrent invariant *)
  Definition TrieDBR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (* Knowledge (no resource ownership) *)
  Definition SelectedProposalForBlockNum (blockNum: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (* cannot use if different proposals can be done for the same round number *)
  Definition ProposedInRoundNum (roundNum: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (* all reads will read from activeProposal, which is determined at TrieRODB::set_block_and_round *)
  Definition TrieRODBR (q:Qp) (activeProposal: option ProposalInDb) : Rep. Proof. Admitted.

  Notation dbAuthR := TrieDBR. (* TODO: inline *)

  (* when we fill in the definition of dbAuthR, we must ensure the lemmas below are provable *)
  Lemma dbAuthREntails (q:Qp) (m: DbModel) : dbAuthR q m |--  dbAuthR q m ** [| validDbModel m|].
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
      
      \pre{activeProposal} [| lookupActiveProposal preDb = Some activeProposal |]
      \post{retp:ptr} [Vptr retp]
        retp |-> bytes32R
        1
        (lookupStorage (postBlockState activeProposal) address key blockTxInd)).


  cpp.spec "monad::Db::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDBR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \let pid := {| idBlockNum := blockNum; idRoundNum:= Some roundNum |}
      \pre{prp} [| lookupProposal pid preDb = Some prp|]
      \pre [| lowestUnfinalizedBlockIndex preDb = Some blockNum |]
      \post
         this |-> TrieDBR q (updateBlockNum preDb blockNum (fun d => d &: _finalizedRoundNum .= (Some roundNum)))
         ** SelectedProposalForBlockNum blockNum prp (* this Knowledge assertion can be used to constrain the output of TrieRODB reads *)
                               ).
                               
  (* no finalize in TrieRODB *)

  cpp.spec "monad::Db::update_verified_block(unsigned long)"
    as update_verified_block_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \pre [| match lowestUnfinalizedBlockIndex preDb with
              | Some s =>  blockNum < s
              | None => False (* if no block has been finalized yet, cannot call this method *)
              end |]
      \post this |-> dbAuthR q (preDb &: _lastVerifiedBlockIndex .= blockNum)).

Import libspecs.
cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as set_block_and_round_spec with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preDb} this |-> dbAuthR q preDb

    (* block_number: unsigned long *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" q (Vint v)) (cQp.mut q)
          (idRoundNum pid))

    \pre{prp} [| lookupProposal pid preDb = Some prp|]

    (* On return, activeBlock is updated accordingly *)
    \post this |-> dbAuthR q (preDb &: _activeProposal .= Some pid)
  ).

(* cpp.spec "monad::RODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" *)
cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as rodb_set_block_and_round_spec1 with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preActive} this |-> TrieRODBR q preActive

    (* block_number: unsigned long *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" q (Vint v)) (cQp.mut q)
          (idRoundNum pid))


    (* On return, activeBlock is updated accordingly *)
    \post{ret} [Vbool ret]
       if ret then Exists proposal,  this |-> TrieRODBR q (Some proposal)
                                     ** SelectedProposalForBlockNum (idBlockNum pid) proposal
      else  this |-> TrieRODBR q None
  ).

(* cpp.spec "monad::RODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" *)
cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as rodb_set_block_and_round_spec2 with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preActive} this |-> TrieRODBR q preActive

    (* block_number: unsigned long *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" q (Vint v)) (cQp.mut q)
          (idRoundNum pid))

    \pre{proposal} SelectedProposalForBlockNum (idBlockNum pid) proposal

    (* On return, activeBlock is updated accordingly *)
    \post{ret} [Vbool ret]
       if ret then this |-> TrieRODBR q (Some proposal)
      else  this |-> TrieRODBR q None (* the proposal got garbage collected *)
   ).

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

  Definition commitPostState
             (preDb       : DbModel)
             (newProposal : ProposalInDb)
    : DbModel :=
    let bnum := pblockNum newProposal in
    match lookupBlockByNum bnum preDb with
    | Some _ =>
        (* merge into existing state *)
        updateBlockNum preDb bnum (fun bs => bs &: _proposals .= (newProposal::proposals bs))
    | None =>
        preDb &: _blockNumStates .=
              ({| proposals := [newProposal]; finalizedRoundNum := None |}::(blockNumStates preDb)) 
    end.

  Definition WithdrawalR (q: cQp.t) (w: Withdrawal) : Rep. Proof. Admitted.
(* TODO:
- handle garbage collection
- handle genesis block creation
 *)
Open Scope N_scope.
cpp.spec
  "monad::Db::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
  as commit_spec with (fun (this:ptr) =>
    \prepost{(preDb:DbModel)} this |-> dbAuthR 1 preDb

    \arg{(deltas_ptr: ptr) (qs: Qp)} "#0" (Vptr deltas_ptr)
    \prepost{(newProposal: ProposalInDb)}
      deltas_ptr |-> StateDeltasR qs (stateAfterActiveProposal preDb, (postBlockState newProposal))

    \arg{(code_ptr:ptr) (qcd: Qp)} "#1" (Vptr code_ptr)
    \prepost
      code_ptr |-> CodeDeltaR qcd (stateAfterActiveProposal preDb, (postBlockState newProposal))

    \arg{hdr_ptr} "#2" (Vptr hdr_ptr)
    \prepost{ (qpr: Qp)}
      hdr_ptr |-> BheaderR qpr (header (proposedBlock newProposal))
      \pre [| match activeProposal preDb with
              | Some activeProp =>
                  pblockNum newProposal = 1 + idBlockNum activeProp
              | None => pblockNum newProposal = 0
              end
              |]
   (*  \pre [| roundNum newProposal ∉ (map (roundNum ∘ fst) (nextBlockProposals preDb)) |] can this, depending on whether consensus can really send us 2 blocks for the same round number *)

    \arg{receipts_ptr} "#3" (Vptr receipts_ptr)
    \prepost{ (qtrs: Qp)}
      receipts_ptr |->
        VectorR
          "monad::Receipt"%cpp_type
          (fun r => ReceiptR r)
          qtrs (txResults newProposal)
          
   \arg{cfs_ptr} "#4" (Vptr cfs_ptr)
   \prepost{qcf}
      cfs_ptr |->
        monad.proofs.libspecs.VectorR
          "std::vector<monad::CallFrame>"%cpp_type
          (fun inner:unit => emp)
          qcf []
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
          (fun t => TransactionR qtxn t)
          qtxn (transactions (proposedBlock newProposal))

    \arg{ommers_ptr qo} "ommers" (Vptr ommers_ptr)
    \prepost
      ommers_ptr |->
        monad.proofs.libspecs.VectorR
          "monad::BlockHeader"%cpp_type
          (fun h => BheaderR qo h)
          qo (ommers (proposedBlock newProposal))

   \arg{wds_ptr} "#8" (Vptr wds_ptr)
          
    \prepost{qw: cQp.t}
      wds_ptr |-> optionR
        "std::vector<monad::Withdrawal>"%cpp_type
        (fun ws => monad.proofs.libspecs.VectorR
                     "monad::Withdrawal"%cpp_type
                     (WithdrawalR qw)
                     qw ws)
        qw
        (withdrawals (proposedBlock (newProposal)))
    \post this |-> dbAuthR 1 (commitPostState preDb newProposal)).
End with_Sigma.
(**

```gallina
fill in the following admits above in the file:

Definition maxL (l: list N) : N. Proof. Admitted.
Definition minL (l: list N) : N. Proof. Admitted.

  Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N. Proof. Admitted.

  Definition updateBlockNum (d: DbModel) (bnum: N) (f: BlockNumStateInDb -> BlockNumStateInDb): DbModel. Proof. Admitted.

  Definition finalizeProposal (pid: ProposalId) (d: BlockNumStateInDb) : BlockNumStateInDb. Proof. Admitted. 

Definition commit_model
  (preDb      : DbModel)
  (newProposal   : ProposalInDb)
  : DbModel. Proof. Admitted.
```

Put them in a new module to avoid name clash with the existing admits. I will later copy your definitions up  
Unfortunately, CppDefnOf is currrently not working so you can only issue Coq queries not clangd queries.


+++ FILES
../../../fmdeps/fmai/prompts/sep.md
../../../fmdeps/fmai/prompts/specs.md
../../dbsummary2.md
+++ QUERIES

 *)
