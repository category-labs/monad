(** Specificatins of TrieDB and TrieRODb.
Although an attempt has been made to make it understandable to anyone with some familiarity with functional programming (ocaml/haskell),
it is highly recommended to review the first 2 formal verification tutorials to understand this file.
At many places, this file refers to analogous concepts explained in the tutorial.
- tutorial1 (only until 1:17:00): https://www.youtube.com/watch?v=zyyoWnF1QUE
- tutorial2 (only until 1:10:00): https://www.youtube.com/watch?v=9fjR_yQmiOU
 *)

Require Import monad.proofs.prelude.
Require Import monad.asts.trie_rodb.
Require Import  monad.asts.trie_db.
Open Scope N_scope.


(** *Model type for TrieDb/TrieRODb *)
(** The first task for writing specs of a C++ class is typically
to define a Coq type that models the data stored by objects of that class.
This Coq type is also often called the model type.
The model type is ideally at a very high-level and abstracts away the C++-related implementation details.
For example, the model type of bytes32 is just `N` the Coq type of unbounded (mathematical) natural numbers,
even though in C++, it is laid out 32 machine bytes.
Similarly, the model type of various sequention C++ containers, e.g. linked lists, arrays, vectors, sets are the typicall the same: Coq lists.

Method specs typically tie the pre/post states of the object to elements of the Coq model type.
We can then use Coq's logic to write assertions on the model, to capture the pre and post conditions.

The next few definitions lead up to the definition of [DbModel], the model type of `monad::Db::TrieDb`, starting with its subcomponents
 *)

(** [ConsensusBlockHeader] is a model type of the C++ struct `MonadConsensusBlockHeader`.
This struct has many fields and the Db probably stores all of them.
But one struct field: `uint64_t round` is special as the Db uses round numbers to make decisions
For now we just model this field. 
 *)
Record ConsensusBlockHeader :=
  {
    roundNum: N; (* models `uint64_t round` *)
    (* TODO: add more fields, to model the following C++ fields
       uint64_t epoch{0};
       MonadQuorumCertificate qc{};
       byte_string_fixed<33> author{};
       uint64_t seqno{0};
       uint128_t timestamp_ns{0};
       byte_string_fixed<96> round_signature{};
       std::vector<BlockHeader> delayed_execution_results{};
       BlockHeader execution_inputs{};
     *)
  }.
    
(** [EvmState] is persistent state of the entire EVM: state of ALL accounts *)
Notation EvmState := evm.GlobalState.

(** [ProposalInDb] bundles all of the information for a single block proposal
    stored in the trie: the consensus header [cheader], the raw [proposedBlock],
    its [postBlockState] after execution, and the per-transaction [txResults]. *)
Record ProposalInDb :=
  {
    cheader: ConsensusBlockHeader;
    proposedBlock: Block;
    postBlockState: EvmState;
    txResults: list TransactionResult;
  }.

(** [BlockNumStateInDb] groups together all proposals sharing the same block number.
*)
Record BlockNumStateInDb :=
  {
    proposals: list ProposalInDb;
    finalizedRoundNum: option N; (** option T is just like std::optional<T> in C++ *)
    (** ^ for any block number, finalized round number, if any, is set by calling Db::finalize()*)
  }.


(** [ProposalId] identifies a single proposal in the model by its block number
    and an optional round number.  *)
Record ProposalId :=
  {
    idBlockNum: N;
    idRoundNum: option N; (** None signifies the finalized round number for block number [idBlockNum] *)
  }.

(* underlying storage for the Db *)
Inductive DbPath :=
| BlockDev (fullpath: string)
| File (fullpath: string).
  
(** [DbModel] is the complete in-memory trie model for [TrieDb].*)
Record DbModel : Type :=
  {
    blockNumsStates: list BlockNumStateInDb;
    (** ^ each member of this list records all proposals (and finalized round number, if any) for some round number.
       each member of this list represents a unique block number.
     *)
    
    activeProposal: option ProposalId;
    (** ^ records the active proposal from which reads like read_storage read.
        set by [set_block_and_round]; None means set_block_and_round has never been called on this object yet. *)

    votedMetadata: option (N * N);
    (** ^ (block_num, round) from the latest [update_voted_metadata] call *)

    lastVerifiedBlockIndex: N;
    (** ^ highest block index marked verified via [update_verified_block] *)

    dbpath: DbPath;
    (** this path is authoritatively owned by the TrieDB. A client can reason that TrieRODb created with the same underlying path reads the same values that this TrieDb writes *)
    
    cinvId: gname;
    (** ^ ignore this Coq detail: invariant name for the concurrent disk/memory ownership.*)
  }.


(** * class invariants of Db

Not all members of the [DbModel] type correspond to a data stored in a TrieDb object (and associated disk structures).
There some invariants, e.g.:
- the list [blockNumsStates] has a contiguous range of block numbers (no holes)
- proposals in [blockNumsStates] have distinct round numbers.
  even if commit() is called multiple times for the same round number, it atomically replaces the old proposal for the same round number: after commit(), the old block cannot be accessed by TrieDb methods.
  Some TriedRODb methods can still access the old proposal until the next set_block_and_round and we will see how our specs capture that below.

In this section, we have a sequence of definitions leading up to [validDbModel], which captures these invariants.
Class invariants hold before/after every method call.
(For classes whose methods can be called concurrently, many of the class invariants always hold, even in the middle of the execution of a concurrent method. For more details, review concurrent invariants in tutorial2)
 *)


(** extracts the block number from a [ProposalInDb] *)
Definition pblockNum (p: ProposalInDb): N  := number (header (proposedBlock p)).

(** returns the block number of a [BlockNumStateInDb].
    clients must ensure that [b] is valid, as defined below by [validBlockNumStateInDb],
    which asserts that all proposals have the same block number and that there is at least one proposal
 *)
Definition blockNum (b: BlockNumStateInDb) : N :=
  match proposals b with
  | h :: _ => pblockNum h
  | [] => 0 (* dummy: clients must ensure [hasAtLeastOneProposal b] *)
  end.

(** [proposalsHaveSameBlockNum] asserts that all entries in a proposal list
    share the same block number, enforcing the group invariant. *)
Definition proposalsHaveSameBlockNum (b: BlockNumStateInDb) :=
  forall p1 p2,
    p1 ∈  proposals b -> p2  ∈ proposals b -> pblockNum p1 = pblockNum p2.

Definition hasAtLeastOneProposal (b: BlockNumStateInDb) :=
  exists p, p ∈ proposals b.

(* this definition from Coq standard library asserts that a given list has no duplicates *)
Notation NoDuplicate := NoDup.

(** [validBlockNumStateInDb] combines the key invariants on a block-number state:
    non-empty list, uniform block number, and no duplicate rounds within the group. *)
Definition validBlockNumStateInDb (b: BlockNumStateInDb) : Prop :=
  hasAtLeastOneProposal b /\
  proposalsHaveSameBlockNum b /\
  NoDuplicate (map (roundNum ∘ cheader) (proposals b)).

(** [validDbModel] does more than just assert [validBlockNumStateInDb] for every item in the [blockNumsStates] list:
    there are some inter-block number constrants as well, e.g.
    - block numbers in the db are continguous, with no duplicates
    - the active block is currently exists in the Db.
    - there is a maxFinalizedIndex such that every block index below it is finalized and every index above is not finalized.
 *)

(** asserts that block numbers in lb are continguous: has no holes. assumes lb is nonempty *)
Definition contiguousBlockNums (lb: list BlockNumStateInDb) : Prop :=
  let blockNums := List.map blockNum lb in
  let maxBlockNum := maxL blockNums in
  let minBlockNum := minL blockNums in
  forall blockNumber,
    minBlockNum <= blockNumber <= maxBlockNum ->
    exists b, blockNum b = blockNumber /\ b ∈ lb.

(** smallest block number in the model. assumes non-empty [blockNumsStates] *)
Definition lowestBlockNum (d: DbModel) : N :=
  match blockNumsStates d with
  | h :: _ => blockNum h
  | [] => 0 (* dummy *)
  end.
             
(** looks up a block number in the Db. *)
Definition lookupBlockByNum (bnum: N) (d: DbModel) : option BlockNumStateInDb :=
  match List.filter (fun b => bool_decide (blockNum b = bnum)) (blockNumsStates d) with
  | h :: _ => Some h 
  | [] => None
  end.

(** lookup a proposal by a given roundnumber in BlockNumStateInDb *)
Definition lookupProposalByRoundNum (b: BlockNumStateInDb) (rnum: N) : option ProposalInDb :=
  match List.filter (fun p => bool_decide (roundNum (cheader p) = rnum)) (proposals b) with
  | h :: _ => Some h (* unique under validBlockNumStateInDb *)
  | [] => None
  end.

(** finalized proposal for a round number, if any *)
Definition finalizedProposal (b : BlockNumStateInDb) : option ProposalInDb :=
  match finalizedRoundNum b with
  | None => None
  | Some rnd => lookupProposalByRoundNum b rnd
  end.

(** lookup a ProposalId (block number, optional round number) in the Db *)
Definition lookupProposal (id: ProposalId) (d: DbModel) : option ProposalInDb :=
  match lookupBlockByNum (idBlockNum id) d with
  | None => None
  | Some b =>
    match idRoundNum id with
    | None => finalizedProposal b
    | Some rnum => lookupProposalByRoundNum b rnum
    end
  end.

(** lookup the active proposal *)
Definition lookupActiveProposal (d: DbModel) : option ProposalInDb :=
  match activeProposal d with
  | None => None
  | Some ap => lookupProposal ap d
  end.
    
(** [validActiveProposal m] asserts that if [activeProposal] is set,
    it must correspond to an existing proposal in [m]. *)
Definition validActiveProposal (m: DbModel) : Prop :=
  match activeProposal m with
  | None => True
  | Some pid => isSome (lookupProposal pid m)
  end.

(** all the proposals in the Db, across all block numbers*)
Definition allProposalsInDb (d: DbModel) :=
  flat_map proposals (blockNumsStates d).

(** [validDbModel m] combines all invariants on the top-level DB model:
    - block numbers in the db are continguous, with no duplicates
    - no duplicate round number across all block numbers
    - the active block is currently exists in the Db.
    - there is a maxFinalizedIndex such that every block index below it is finalized and every index above is not finalized.*)
Definition validDbModel (m: DbModel) : Prop :=
  (forall b, b ∈ blockNumsStates m -> validBlockNumStateInDb b)
  /\ contiguousBlockNums (blockNumsStates m)
  /\ NoDuplicate (map blockNum (blockNumsStates m))
  /\ NoDuplicate (map (roundNum ∘ cheader) (allProposalsInDb m))
  /\ validActiveProposal m
  /\ (exists maxFinalizedBlockNum,
         (forall b, blockNum b <= maxFinalizedBlockNum -> isSome (finalizedProposal b))
         /\ (forall b, blockNum b > maxFinalizedBlockNum -> isNone (finalizedProposal b))).

  

(** ignore the next 8 lines: Coq boilerplate *)
#[only(lens)] derive DbModel.
#[only(lens)] derive ProposalInDb.
#[only(lens)] derive BlockNumStateInDb.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
  Context  {MODd : trie_db.module ⊧ CU}.

  (* TODO: upstream *)
  Definition WithdrawalR (q: cQp.t) (w: Withdrawal) : Rep. Proof. Admitted.

  
(** *TrieD/TrieRODb rep predicates
  Rep predicates are one of the main ingredients of specifications.
  They define how an element of the model type in Coq is represented in memory/disk starting from the "this" memory location (base pointer of the object).
  They also assert ownership of such locations.
  If the object stores pointers to other memory locations or disk locations, Rep predicates can also assert what is stored at those locations and assert ownership of those locations.
  To understand this in more detail, please review the examples in the first quarter of tutorial2.
 *)
  
(** [this |-> TrieDb q m] asserts that at the memory location [this], there is an object representing the [DbModel] [m].
  the "Proof. Admitted." means that we have not defined it yet and asked Coq to leave it as a hole to be filled later.
  The Rep predicate(s) of a class is usually an implementation detail and clients do NOT need to know about the exact definition.
    
  [this |-> TrieDb q m] also asserts [q] fraction ownership of the object.
  The definition [TrieDb q m] will also assert ownership of the associated memory and disk cells/blocks as functions of this [q].
  q ∈ (0,1].
  q must be 1 to be able to call methods that update Db (e.g. commit, finalize). a smaller fraction suffices to read (e.g. read_storage).
   *)
  Definition TrieDbR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (** Even though the users of TrieDb (e.g. when writing Coq proofs of callers of TrieDb methods) do not need need to know the definition of
      TrieDbR, they do need a guarantee that it satisfies the following 3 properties *)

  (** this property says that [this |-> TrieDb q m] must imply that [m] is valid.
      As discussed in the first tutorial, `|--` is separation logic entailment and ** is the separating conjunction*)
  Lemma TrieDbREntailsValidity (q:Qp) (m: DbModel) : TrieDbR q m |--  TrieDbR q m ** [| validDbModel m|].
  Proof. Admitted.

  (** TrieDb is a concurrent library. When executing a block, the speculative executions of multiple transactions can concurrently read from the Db. But they know that they will read the pre-block state. No such thread updates the Db.
  The following lemma allows splitting the 1 ownership of the TrieDb into smaller pieces, as many as we want so that we can pass that ownership pieces to several threads to allow them all to read the Db concurrently.
   *)
  Lemma TrieDbRsplit (q1 q2:Qp) (m: DbModel) :
    TrieDbR (q1+q2) m |--  TrieDbR q1 m ** TrieDbR q2 m.
  Proof. Admitted.

(** can construct at most 1 TrieDb object underlying storage location (dbpath).
    This will be provable when TrieDbR is fully defined because TrieDbR will hod the full authoritative ownership of the storage at dbpath and thus only one object can hold this ownership.
   *)
  Lemma max1TrieDbObject  (base1 base2: ptr) (m1 m2: DbModel) :
    dbpath m1 = dbpath m2 ->
    base1 |-> TrieDbR 1 m1 ** base2 |-> TrieDbR 1 m2 |-- [| False |].
  Proof. Admitted.
  
(** We can construct several TrieRODb objects on the same underlying storage as an existing TrieDb object.
   Unlike ownership of primitive types, even if you hold [this |-> TrieDb 1 m],
   other thread/processes can read (but not update) the underlying Db storage using some TrieRODb object.

   To get a sense of how TrieDb and TrieRODb can be defined to achieve this using concurrency invariants,
   review the 2nd and 3rd quarters of tutorial2: [TrieDbR] is similar to uAuthR and [TrieRODbR] is similar to uFragR.

   Unlike TrieDbR, ownership of TrieRODb cannot assert the current state of the entire Db: there can be another process updating the Db concurrently. Nevertheless, operations on TrieRODb are logicall atomic, they read from a single proposal and not a mishmash of multiple propsals.
   [this |-> TrieRODb q dbpath (Some pr)] asserts that the read operations on the object (e.g. read_storage, read_account) will read from  the proposal [pr]. any fraction [q] suffices to do reads: write operations are not supported anyway: they have [| False |] as a precondition.
   q must be 1 to destruct the object or to call set_block_and_round which potentially changes the active proposal.
   [this |-> TrieRODb q dbpath None] does not suffice to issue any read: the client needs to first call `set_block_and_round` to
   transform [this |-> TrieRODb q None] to [this |-> TrieRODb q (Some pr)] for some [pr] in case the call succeeds.
 *)
  Definition TrieRODbR (q:Qp) (dbpath: DbPath) (activeProposal: option ProposalInDb) : Rep. Proof. Admitted.
  
(** [FinalizedProposalForBlockNum dbpath n p] asserts that p is the finalized proposal for block n. Because the TrieDb specs do NOT allow modifying finalized block numbers, this assertion is a [Persistent] assertion: once it is established, it always holds (unlike the assertion that the value of variable x is 2): thus, this assertion it can be freely duplicated and shared with other threads/processes. In particular, this assertion is a postconditon of TrieDb::finalize. After calling TrieDb::finalize,  client application can send this assertion to another process (e.g. attached to a socket messsage) and then the client can reason that if the recipient process calls TrieRODb::set_block_and_round(n), it will either fail (block n got evicted on garbage collection) or read p and nothing else. Its definition will use logical/ghost locations which were covered in tutorial3 () *)
  Definition FinalizedProposalForBlockNum (dbpath: DbPath) (blockNum: N) (p: ProposalInDb) : mpred. Proof. Admitted.



(** Finally, we have enough vocabulary to writ the specs.
    Except when committing the genesis block to the Db, before reading/updating the Db, we need to set the active block via set_block_and_round.
    So, lets see its spec first:
 *)

  (*TODO: upstream to libspecs. *)
  Definition optionalPrimR (q:Qp) (primty:type) (on: option N): Rep :=
    optionR primty
      (fun v:N => primR primty q (Vint v)) (cQp.mut q) on.
  
  cpp.spec "monad::TrieDb::set_block_and_round(unsigned long, std::optional<unsigned long>)"
    as set_block_and_round_spec with (fun (this:ptr) =>
    \prepost{preDb: DbModel} this |-> TrieDbR 1 preDb
    (** ^ requires full(1) ownernership of the TrieDb object.
        This guarantees that no other threads can be using this object concurrently to read (because reading requires non-zero ownership)
        This says that the object is in a state where the data it holds (together with the linked disk data)
        corresponds to some model element [preDb]. Because of the lemma [TrieDbREntailsValidity] above,
        this also means that all the class invariants defined in [validDbModel] hold just before the call
       *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))
    (** ^ the {pid: ProposalId} part universally quantifies over a proposal id that
        serves the combined model of the block_number and round_number arguments.
        [Vint (idBlockNum pid)] says that the block_number argument should be
        the number [idBlockNum pid]
     *)  

    \arg{roundLoc} "round_number" (Vptr roundLoc)
    \prepost roundLoc |-> optionalPrimR 1 "unsigned long" (idRoundNum pid)
    (** ^ the above 2 lines together describe the round_number argument
        unline block_number, which is a scalar value of type uint64_t,
        round, number has type std::optional<uint64_t>.
        in the formalization of C++ we use, such composite type (struct/array) arguments are represented as memory locations
        that store the composite value.
        So, the first line names that memory location as [roundLoc]. (this would typically be a location on stack)
        The next line line says that at [roundLoc] we have the representation of the optionl number [idRoundNum pid]
        which is of type [option N] in Coq. Note that pid was already quantified above, when specifyin the block_number argument.


        Above, we have connected all the arguments of the method (including the implicit `this` argument) to their corresponding
        models in Coq (e.g. DbModel) via their Rep predicates (e.g. TrieDbR, optionalPrimR).
        These Rep predicates already asser that the class invariants hold.
        Next, we specify any other condition that must hold at the beginning (precondition):
     *)  
    
    \pre [| isSome (lookupProposal pid preDb)|]
    (** ^ this precondition asserts that the chosen proposal id must exist in the db: the lookup in the db model (preDb) must not return None (analogous to std::nullopt)
     *)

    \post this |-> TrieDbR 1 (preDb &: _activeProposal .= Some pid)
     (** this is the post condition. it returns back the full ownernership of TrieDbR but with a modified model, capturing
         how the implementation updates the state of the Db.
         In the model, the update is merely to set the [activeProposal] field to the supplied [pid] (of type [ProposalId]).
         All other fields are unchanged.
         As we will see in the spec of read_storage, the read operations lookup this proposal id in the [blockNumsIndices] list of [DbModel]
     *)
  ).


  
  (** [read_storage(address, incarnation, key)] reads the 32-byte storage slot
      from the *active proposal* selected in [preDb]. It requires fractional ownership
      [q] of the current trie state [preDb], as well as ownership of the pointers
      for [address], [incarnation], and [key]. The precondition
      [lookupActiveProposal preDb = Some activeProposal] ensures there is an
      active proposal to read from. On return, [retp] points to the
      [bytes32] value obtained by [lookupStorage (postBlockState activeProposal)
      address key blockTxInd], and the trie state is preserved unchanged.
  *)
  cpp.spec "monad::TrieDb::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDbR q preDb
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

(** [lowestUnfinalizedBlockIndex d] finds the smallest block number
    among those groups that have not yet been finalized. *)
Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N :=
  let unfin := filter (fun b => finalizedProposal b = None) (blockNumsStates d) in
  match unfin with
  | [] => None
  | _ => Some (minL (map blockNum unfin))
  end.

(** [updateBlockNum d bnum f] applies a functional update [f] to the
    single [BlockNumStateInDb] in [d] whose block number is [bnum].
    All other groups remain unchanged. *)
Definition updateBlockNum
  (d: DbModel)
  (bnum: N)
  (f: BlockNumStateInDb -> BlockNumStateInDb) : DbModel :=
  d &: _blockNumsStates .= 
    map (fun b => if bool_decide (blockNum b = bnum) then f b else b)
        (blockNumsStates d).


  (** Spec of [TrieDb::finalize]:

      [finalize(blockNum, roundNum)] promotes the proposal snapshot at [blockNum]
      and [roundNum] into the finalized state, making it immutable under
      the [finalized_nibbles] prefix. It requires fractional ownership [q] of
      the current DB model [preDb], plus evidence that [preDb] contains a
      proposal at [blockNum, roundNum], and that [blockNum] is the lowest
      unfinalized block. On return, the trie state is updated so that the
      proposal at [blockNum] is marked finalized, and the caller gains
      [SelectedProposalForBlockNum blockNum prp] to record which proposal
      was frozen.
  *)
  cpp.spec "monad::TrieDb::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDbR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \let pid := {| idBlockNum := blockNum; idRoundNum:= Some roundNum |}
      \pre{prp} [| lookupProposal pid preDb = Some prp|]
      \pre [| lowestUnfinalizedBlockIndex preDb = Some blockNum |]
      \post
         this |-> TrieDbR q (updateBlockNum preDb blockNum (fun d => d &: _finalizedRoundNum .= (Some roundNum)))
         ** SelectedProposalForBlockNum blockNum prp (* this Knowledge assertion can be used to constrain the output of TrieRODB reads *)
                               ).
                               
  (* no finalize in TrieRODB *)

  (** Spec of [TrieDb::update_verified_block]:

      Marks [blockNum] as the last verified block in the DB model without
      changing any trie prefix. Requires fractional ownership [q] of [preDb]
      and that [blockNum] is strictly less than the next unfinalized block.
      On return, only [_lastVerifiedBlockIndex] is updated to [blockNum].
  *)
  cpp.spec "monad::TrieDb::update_verified_block(unsigned long)"
    as update_verified_block_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDbR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \pre [| match lowestUnfinalizedBlockIndex preDb with
              | Some s =>  blockNum < s
              | None => False (* if no block has been finalized yet, cannot call this method *)
              end |]
      \post this |-> TrieDbR q (preDb &: _lastVerifiedBlockIndex .= blockNum)).


  (** Spec of [TrieRODb::set_block_and_round] (first variant):

      Attempts to pin a read-only view on the proposal [pid]. Given full
      ownership of the read-only DB model [preActive], it returns a boolean
      indicating whether the proposal still exists. On success, the view
      is advanced to [Some proposal] and exposes [SelectedProposalForBlockNum]
      so future reads can locate the frozen proposal. On failure, the view
      remains at [None].
  *)
  cpp.spec "monad::TrieRODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" 
    as rodb_set_block_and_round_spec1 from (trie_rodb.module) with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{(preActive: option ProposalInDb) (dbpath: DbPath)} this |-> TrieRODbR 1 dbpath preActive

    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{(qo: Qp) (roundOpt: option N)}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" qo (Vint v)) (cQp.mut qo)
          (idRoundNum pid))


    \post{ret} [Vbool ret]
       if ret then Exists proposal,  this |-> TrieRODbR 1 dbpath (Some proposal)
                                     ** SelectedProposalForBlockNum (idBlockNum pid) proposal
      else  this |-> TrieRODbR 1 dbpath None
  ).

  (** Spec of [TrieRODb::set_block_and_round] (second variant):

      Validates that the previously selected proposal [proposal] is still
      present in the trie. Requires [SelectedProposalForBlockNum] in the
      precondition. Returns [true] and retains [Some proposal] if it has
      not been garbage-collected, or [false] and resets the view to [None]
      otherwise.
  *)
  cpp.spec "monad::TrieRODb::set_block_and_round(unsigned long, std::optional<unsigned long>)"
    as rodb_set_block_and_round_spec2  from (trie_rodb.module) with (fun (this:ptr) =>
    \prepost{preActive dbpath} this |-> TrieRODbR 1 dbpath preActive

    \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))

    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{(qo: Qp) (roundOpt: option N)}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" qo (Vint v)) (cQp.mut qo)
          (idRoundNum pid))

    \pre{proposal} SelectedProposalForBlockNum (idBlockNum pid) proposal

    \post{ret} [Vbool ret]
       if ret then this |-> TrieRODbR 1 dbpath (Some proposal)
      else  this |-> TrieRODbR 1 dbpath None (* the proposal got garbage collected *)
   ).

  (** Spec of [TrieDb::update_voted_metadata]:

      Records the highest‑round quorum certificate for [blockNum] in
      [_votedMetadata]. Requires full ownership of [preDb], and on return
      [_votedMetadata] is updated to [Some (blockNum, roundNum)].
  *)
  cpp.spec "monad::TrieDb::update_voted_metadata(unsigned long, unsigned long)"
    as update_voted_metadata_spec with (fun (this:ptr) =>
      \prepost{preDb} this |-> TrieDbR 1 preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round"        (Vint roundNum)
      \post this |-> TrieDbR 1 (preDb &: _votedMetadata .= Some (blockNum, roundNum))).

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

  
(** [stateAfterActiveProposal m] returns the EVM state after executing
    the active proposal, or [dummyEvmState] if none is pinned. Used by [read_storage]
    and [commit] specs to fetch the base state. *)
Definition stateAfterActiveProposal (m: DbModel) : evm.GlobalState :=
  match lookupActiveProposal m with
  | None => dummyEvmState
  | Some p => postBlockState p
  end.

  Definition ConsensusBlockHeaderR (q: cQp.t) (w: ConsensusBlockHeader) : Rep. Proof. Admitted.

  (** Spec of [TrieDb::commit]:

      Incorporates a new block proposal [newProposal] into the database state.
      Given full ownership of the current trie [preDb] and of all inputs
      (state deltas, code deltas, block header, receipts, call frames,
      senders, transactions, ommers, and optional withdrawals),
      and assuming that [newProposal] either extends the previous active block
      or is the genesis block,
      [commit] updates the in-memory list of proposals and returns the updated
      trie state [commitPostState preDb newProposal]. All EVM outputs in
      [newProposal] must match the provided arguments, and the existing state
      is preserved for other blocks.
  *)
  cpp.spec
    "monad::TrieDb::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<const monad::vm::interpreter::Intercode>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<const monad::vm::interpreter::Intercode>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
  as commit_spec with (fun (this:ptr) =>
    \prepost{(preDb:DbModel)} this |-> TrieDbR 1 preDb

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
    \post this |-> TrieDbR 1 (commitPostState preDb newProposal)).
End with_Sigma.

(*---------------------------------------------------------------------
 Ownership flow of [TrieDbR] in runloop_monad.cpp and execute_block:

 1) Before [execute_block]:
    +--------------------------------------+
    | TrieDbR (ownership = 1)             |
    +--------------------------------------+
    | set_block_and_round(...)            |
    +--------------------------------------+

 2) Inside [execute_block] (N fibers):
    Splits TrieDbR into N read-only slices for each transaction fiber:

      +-------+  +-------+  ...  +-------+
      |TrieDbR|  |TrieDbR|       |TrieDbR|
      | (1/N) |  | (1/N) |       | (1/N) |
      +-------+  +-------+       +-------+
        fiber1    fiber2         fiberN
        (read)    (read)         (read)

    Each fiber reads state and builds [BlockState] deltas only.

 3) After fibers finish, ownership is rejoined and commit is called:

    +--------------------------------------+
    | TrieDbR (ownership rejoined = 1)     |
    +--------------------------------------+
    | TrieDb::commit(...)                  |
    +--------------------------------------+

--------------------------------------------------------------------- *)
