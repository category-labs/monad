Require Import monad.proofs.prelude.
Require Export monad.asts.trie_rodb.
Require Export monad.asts.trie_db.
Open Scope N_scope.

(** The first task for writing specs of a C++ class is typically to define a Coq type that
models the data stored by objects of that class.
This Coq type is also often called the model type.
The model type is ideally at a very high-level and abstracts away the C++ related implementation details.
For example, the model type of bytes32 is just `N` the Coq type of unbounded (mathematical) numbers, even though in C++,
it is laid out as 4 words.
Similarly, the model type of various sequention C++ containers, e.g. linked lists, arrays, vectors are the same: Coq lists.

Method specs typically tie the pre/post states of the object to elements of the Coq model type.
We can then use Coq's logic to write assertions on the model, to capture the pre and post conditions.

The next few definitions lead up to the definition of [DbModel], the model type of `monad::Db::TrieDb`.
*)
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
    blockNumsStates: list BlockNumStateInDb;
    
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
  match blockNumsStates d with
  | h::_ => blockNum h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

(* upstream *)
Definition nthElem {A:Type} (l: list A) (n:N) : option A :=
  nth_error l (N.to_nat n).
             
Definition lookupBlockByNum (bnum: N) (d: DbModel) : option BlockNumStateInDb :=
  match List.filter (fun b => bool_decide (blockNum b= bnum)) (blockNumsStates d) with
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

Definition splitL {A} (n:N) (l: list A) : (list A * (list A)) :=
  (takeN n l, dropN n l).

Definition validDbModel (m: DbModel) : Prop :=
  (forall b, b ∈ (blockNumsStates m) -> validBlockNumStateInDb b)
  /\ contiguousBlockNums (blockNumsStates m)
  /\ NoDuplicate (map blockNum (blockNumsStates m))
  /\ validActiveProposal m
  /\ (exists numFinalized:N, let '(firstn, rest) := splitL numFinalized (blockNumsStates m) in
         (forall b, b ∈ firstn -> isSome (finalizedProposal b))
         /\ (forall b, b ∈ rest -> isNone (finalizedProposal b))
     ).

  Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
  
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
      (blockNumsStates d) in
  match unfin with
  | [] => None
  | _  => Some (minL (List.map blockNum unfin))
  end.

#[only(lens)] derive DbModel.
#[only(lens)] derive ProposalInDb.
#[only(lens)] derive BlockNumStateInDb.

Definition updateBlockNum
  (d: DbModel)
  (bnum: N)
  (f: BlockNumStateInDb -> BlockNumStateInDb) : DbModel :=
  d &: _blockNumsStates .= 
    List.map (fun b =>
                if bool_decide (blockNum b = bnum)
                then f b else b)
    (blockNumsStates d).

(** ignore the next 4 lines: Coq boilerplate *)
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
  Context  {MODd : trie_db.module ⊧ CU}.
  
  
  (** contains the auth ownership of monad::mpt::Db in-memory datastructures AND also the on-disk datastructures. there can be only 1 object owning the on-disk data at any given time. full 1 fraction is needed to update the state. this ownership [dbAuthR 1 _] is disjoint from [dbFragR] below. The latter can be used to read the database even when some other thread owns [dbAuthR 1 _]: the actual ownership of the disk/memory lives in a concurrent invariant *)
  Definition TrieDBR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (** Knowledge assertion (no resource ownership) *)
  Definition SelectedProposalForBlockNum (blockNum: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (** cannot use if different proposals can be done for the same round number *)
  Definition ProposedInRoundNum (roundNum: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (** all reads will read from activeProposal, which is determined at TrieRODB::set_block_and_round *)
  Definition TrieRODBR (q:Qp) (activeProposal: option ProposalInDb) : Rep. Proof. Admitted.


  (** The definition of TrieDBR is a detail of the DB implementation: it defines how a (m: DbModel) is represented in memory and disk. Clients of TrieDB do not need to know this. However, clients need a guarantee that the definition TrieDB satisfies the following properties: *)

  
  Lemma TrieDBREntails (q:Qp) (m: DbModel) : TrieDBR q m |--  TrieDBR q m ** [| validDbModel m|].
  Proof. Admitted.

  Lemma TrieDBRsplit (q1 q2:Qp) (m: DbModel) :
    TrieDBR (q1+q2) m |--  TrieDBR q1 m ** TrieDBR q2 m.
  Proof. Admitted.


  cpp.spec "monad::TrieDb::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDBR q preDb
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

  cpp.spec "monad::TrieDb::finalize(unsigned long, unsigned long)"
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

  cpp.spec "monad::TrieDb::update_verified_block(unsigned long)"
    as update_verified_block_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDBR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \pre [| match lowestUnfinalizedBlockIndex preDb with
              | Some s =>  blockNum < s
              | None => False (* if no block has been finalized yet, cannot call this method *)
              end |]
      \post this |-> TrieDBR q (preDb &: _lastVerifiedBlockIndex .= blockNum)).

  cpp.spec "monad::TrieDb::set_block_and_round(unsigned long, std::optional<unsigned long>)"
    as set_block_and_round_spec with (fun (this:ptr) =>
    \prepost{preDb} this |-> TrieDBR 1 preDb

    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{(qo: Qp) (roundOpt: option N)}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" qo (Vint v)) (cQp.mut qo)
          (idRoundNum pid))

    \pre{prp} [| lookupProposal pid preDb = Some prp|]

    \post this |-> TrieDBR 1 (preDb &: _activeProposal .= Some pid)
  ).

  cpp.spec "monad::TrieRODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" 
    as rodb_set_block_and_round_spec1 from (trie_rodb.module) with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{preActive: option ProposalInDb} this |-> TrieRODBR 1 preActive

    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{(qo: Qp) (roundOpt: option N)}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" qo (Vint v)) (cQp.mut qo)
          (idRoundNum pid))


    \post{ret} [Vbool ret]
       if ret then Exists proposal,  this |-> TrieRODBR 1 (Some proposal)
                                     ** SelectedProposalForBlockNum (idBlockNum pid) proposal
      else  this |-> TrieRODBR 1 None
  ).

  cpp.spec "monad::TrieRODb::set_block_and_round(unsigned long, std::optional<unsigned long>)"
    as rodb_set_block_and_round_spec2  from (trie_rodb.module) with (fun (this:ptr) =>
    \prepost{preActive} this |-> TrieRODBR 1 preActive

    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{(qo: Qp) (roundOpt: option N)}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" qo (Vint v)) (cQp.mut qo)
          (idRoundNum pid))

    \pre{proposal} SelectedProposalForBlockNum (idBlockNum pid) proposal

    \post{ret} [Vbool ret]
       if ret then this |-> TrieRODBR 1 (Some proposal)
      else  this |-> TrieRODBR 1 None (* the proposal got garbage collected *)
   ).

  cpp.spec "monad::TrieDb::update_voted_metadata(unsigned long, unsigned long)"
    as update_voted_metadata_spec with (fun (this:ptr) =>
      \prepost{preDb} this |-> TrieDBR 1 preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round"        (Vint roundNum)
      \post this |-> TrieDBR 1 (preDb &: _votedMetadata .= Some (blockNum, roundNum))).

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
        (* add proposal into existing BlockNumState *)
        updateBlockNum preDb bnum (fun bs => bs &: _proposals .= (newProposal::proposals bs))
    | None =>
        (* add a new BlockNumState *)
        preDb &: _blockNumsStates .=
              ({| proposals := [newProposal]; finalizedRoundNum := None |}::(blockNumsStates preDb)) 
    end.

  Definition allProposalsInDb (d: DbModel) :=
    flat_map proposals (blockNumsStates d).
  
  Definition WithdrawalR (q: cQp.t) (w: Withdrawal) : Rep. Proof. Admitted.
  Definition ConsensusBlockHeaderR (q: cQp.t) (w: ConsensusBlockHeader) : Rep. Proof. Admitted.
(* TODO:
- handle garbage collection
- handle genesis block creation
 *)
cpp.spec
  "monad::TrieDb::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<const monad::vm::interpreter::Intercode>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<const monad::vm::interpreter::Intercode>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
  as commit_spec with (fun (this:ptr) =>
    \prepost{(preDb:DbModel)} this |-> TrieDBR 1 preDb

    \arg{(deltas_ptr: ptr) (qs: Qp)} "#0" (Vptr deltas_ptr)
    \prepost{(newProposal: ProposalInDb)}
      deltas_ptr |-> StateDeltasR qs (stateAfterActiveProposal preDb, (postBlockState newProposal))

    \arg{(code_ptr:ptr) (qcd: Qp)} "#1" (Vptr code_ptr)
    \prepost
      code_ptr |-> CodeDeltaR qcd (stateAfterActiveProposal preDb, (postBlockState newProposal))

    \arg{hdr_ptr} "#2" (Vptr hdr_ptr)
    \prepost{ (qpr: Qp)}
      hdr_ptr |-> ConsensusBlockHeaderR qpr (cheader newProposal)
      \pre [| match activeProposal preDb with
              | Some activeProp =>
                  pblockNum newProposal = 1 + idBlockNum activeProp
              | None => pblockNum newProposal = 0
              end
              |]
   \pre [| (roundNum ∘ cheader) newProposal ∉ (map (roundNum ∘ cheader) (allProposalsInDb preDb)) |] (* delete this, depending on whether consensus can really send us 2 blocks for the same round number *)

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
        VectorR
          "std::vector<monad::CallFrame>"%cpp_type
          (fun inner:unit => emp)
          qcf []
    \arg{(senders_ptr: ptr) (qsn: Qp)} "#5" (Vptr senders_ptr)
    \prepost
      senders_ptr |->
        VectorR
          "evmc::address"%cpp_type
          (fun a => addressR qsn a)
          qsn (map sender (transactions (proposedBlock newProposal)))

    \arg{txns_ptr qtxn} "#6" (Vptr txns_ptr)
    \prepost
      txns_ptr |->
        VectorR
          "monad::Transaction"%cpp_type
          (fun t => TransactionR qtxn t)
          qtxn (transactions (proposedBlock newProposal))

    \arg{ommers_ptr qo} "ommers" (Vptr ommers_ptr)
    \prepost
      ommers_ptr |->
        VectorR
          "monad::BlockHeader"%cpp_type
          (fun h => BheaderR qo h)
          qo (ommers (proposedBlock newProposal))

   \arg{wds_ptr} "#8" (Vptr wds_ptr)
          
    \prepost{qw: cQp.t}
      wds_ptr |-> optionR
        "std::vector<monad::Withdrawal>"%cpp_type
        (fun ws => VectorR
                     "monad::Withdrawal"%cpp_type
                     (WithdrawalR qw)
                     qw ws)
        qw
        (withdrawals (proposedBlock (newProposal)))
    \post this |-> TrieDBR 1 (commitPostState preDb newProposal)).
End with_Sigma.
