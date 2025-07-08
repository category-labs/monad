(** * Specifications of TrieDb and TrieRODb.

This document presents formal specifications of the TrieDb and TrieRODb classes.
The goal of these Coq specs is to describe WHAT the methods of these classes do, not how. While the implementation is optimized be extremely computationally efficient,
the specs dont care about that and rather optimize for logical simplicity.

Using separation logic, these specs also precisely specify what kind of concurrency is allowed when calling the methods. Also, these specs should make it easier to understand what happens in case of various races that are allowed. Below, we will see examples of such reasonings.

Specs do not need to define exactly what methods do. Using existential quantification in the postcondition, they can force the clients to not depend on certain implementation details that may change later. Formally, there is a guarantee that proofs of such clients will not need to change if such implementation details change in the future. For example, in the spec of `TrieDb::commit` we allow the TrieDb implementation to garbage collect an arbitrary number of lowest block numbers, subject to certain bounds.

Using preconditions, specs can forbid certain calls in certain states. For example, the specs of TrieRODb::read_storage prohibit calls until after there has been a successful call to TrieRODb::set_block_and_round.



We have attempted to make this file understandable to anyone familiar with functional programming (OCaml/Haskell), but we highly recommend reviewing the first formal verification tutorial before reading this file. In many places, this file refers to analogous concepts explained in the tutorial.

   - #<a href="https://www.youtube.com/watch?v=zyyoWnF1QUE">Tutorial1 recording<a/># (can skip parts after 1:17:00)
   - #<a href="https://www.youtube.com/watch?v=9fjR_yQmiOU">Tutorial2 recording<a/># (can skip parts after 1:10:00) 

We also recommend Tutorial2 as background review if you want to more deeply understand the concurrency aspects of these specs.
*)


(** * Model types for TrieDb/TrieRODb

The first task for writing specs of a C++ class is typically to define a Coq type that models the data stored by objects of that class. This Coq type is also often called the model type.
The model type is ideally at a very high level and abstracts away C++-related implementation details.
For example, the model type of `bytes32` in C++ is just [N], the Coq type of unbounded (mathematical) natural numbers,
even though in C++ it is laid out as an array of 32 machine bytes.
Sequential C++ containers such as linked lists, arrays, vectors, and sets, share the same high-level model, also regardless of the supported level of concurrency.
We represent them uniformly using Coq lists.

Method specs typically tie the pre- and post-states of the object to elements of the Coq model type. In such specs, we can then use Coq's logic to write assertions on the model to capture pre- and post-conditions.

The next few definitions lead up to the definition of [DbModel], the model type of `monad::TrieDb`, starting with its subcomponents.
*)

Require Import monad.asts.trie_rodb.
Require Import  monad.asts.trie_db.
Require Import monad.proofs.prelude.

Notation EvmState := evm.GlobalState.
(** ^ [EvmState] is the persistent state of the entire EVM: the state of all accounts. *)

(** Below, the `ProposalInDb` record bundles all the information for a single block proposal
    stored in the trie: the consensus header [cheader], the raw [proposedBlock],
    its [postBlockState] after execution, and the per-transaction [txResults].
 *)
Record ProposalInDb : Type :=
  {
    cheader: ConsensusBlockHeader;
    proposedBlock: Block;
    postBlockState: EvmState;
    txResults: list TransactionResult;
  }.

(** In this document, almost everything is hyperliked to its definition, even references to Coq items in comments like this one. For example, you can click [Block] here or in the occurrence above to jump to its definition and then press the back button on your browser to come back.
*)

(** Next, `BlockNumStateInDb` groups together all proposals sharing the same block number.
*)
Record BlockNumStateInDb :=
  {
    proposals: list ProposalInDb;
    finalizedRoundNum: option N;
    (** ^ For any block number, the finalized round number, if any, is set by calling `TrieDb::finalize()`. [option T] is similar to `std::optional<T>` in C++. Clicking on [option] will take you to its definition in Coq's standard library. *)
  }.


(** Next, `ProposalId` identifies a single proposal in the model by its block number
    and an optional round number.  *)
Record ProposalId :=
  {
    idBlockNum: N;
    idRoundNum: option N;
    (** ^ [None] signifies the finalized round number for block number [idBlockNum]. *)
  }.

(** Multiple C++ objects can be created based on the same disk storage, e.g. a TrieDb and several TrieRODb objects. So, we track the underlying storage in the model to connect their specs, e.g. how a `TrieDb::commit` affects `TrieRODb::read_storage` if they have the same underlying storage *)
Inductive DbPath :=
| BlockDev (fullpath: PrimString.string)
| File (fullpath: PrimString.string).

(** Finally, `DbModel` is the complete model for [TrieDb], representing in Coq all the data it stores *)
Record DbModel : Type :=
  {
    blockNumsStates: list BlockNumStateInDb;
    (** ^ Each member of this list records all proposals (and finalized round number, if any) for some block number. Each member of this list represents a unique block number, as we will formalize in [validDbModel] below *)
    
    activeProposal: option ProposalId;
    (** ^ Records the id (block number, round number) of the active proposal. Read operations like `read_storage` read from the proposal with this id. Also TrieDb::commit uses this proposal as the base for applying diffs (`StateDeltas`).

     This field is set in the postcondition of the spec for `TrieDb::set_block_and_round`; [None] means `set_block_and_round` has never been called on this object. *)

    votedMetadata: option (N * N);
    (** ^ (block number, round number) from the latest [update_voted_metadata] call. [N * N] is analogous to `std::pair<N,N>` *)

    lastVerifiedBlockNum: N;
    (** ^ highest block index marked verified via [update_verified_block] *)

    dbpath: DbPath;
    (** ^ This field identifies the disk/file where the Db is stored. It is authoritatively owned by the TrieDb. A client can reason that a TrieRODb created with the same underlying path reads the same values that this TrieDb writes. *)
    
    cinvId: gname;
    (** ^ Ignore this Coq detail: invariant name for concurrent disk/memory ownership. *)
  }.


(** * Class Invariants of TrieDb (DbModel).

Not all members of the above [DbModel] type correspond to data stored in a TrieDb object (and associated disk structures).
There are some invariants, e.g.:
- The list [blockNumsStates] has a contiguous range of block numbers (no holes).
- Proposals in [blockNumsStates] have distinct round numbers. Even if commit() is called multiple times for the same round number, it atomically replaces the old proposal for that round number: after `commit()`, the old block cannot be accessed by TrieDb methods. Some TrieRODb methods can still access the old proposal until the next `set_block_and_round`, and we will see how our specs capture that below.

In this section, we have a sequence of definitions leading up to [validDbModel], which captures these invariants.
Class invariants hold before/after every method call.
For classes whose methods can be called concurrently, many of the class invariants always hold, even in the middle of the execution of a concurrent method. For more details, review concurrent invariants in Tutorial2 (linked at the top).
 *)


(** The definition below extracts the block number from a [ProposalInDb] *)
Definition pblockNum (p: ProposalInDb): N  := number (header (proposedBlock p)).

(** `blockNum` returns the block number of a [BlockNumStateInDb].
    clients must ensure that [b] is valid, as defined below by [validBlockNumStateInDb],
    which asserts that all proposals have the same block number and that there is at least one proposal
 *)
Definition blockNum (b: BlockNumStateInDb) : N :=
  match proposals b with
  | h :: _ => pblockNum h
  | [] => 0
  (** ^ Dummy return value: clients must ensure [proposals b] is not empty *)
  end.

(** `proposalsHaveSameBlockNum` asserts that all entries in the proposal list
    share the same block number, enforcing the group invariant. *)
Definition proposalsHaveSameBlockNum (b: BlockNumStateInDb) :=
  forall (p1 p2: ProposalInDb),
    p1 ∈  proposals b -> p2  ∈ proposals b -> pblockNum p1 = pblockNum p2.

Definition hasAtLeastOneProposal (b: BlockNumStateInDb) :=
  exists (p:ProposalInDb), p ∈ proposals b.

Notation NoDuplicate := List.NoDup.
(** ^ [NoDuplicate l] asserts that the list [l] has no dulicate elements. *)

(** Nex, `validBlockNumStateInDb` combines the key invariants on a block-number state:
    non-empty list, uniform block number, and no duplicate rounds within the group. *)
Definition validBlockNumStateInDb (b: BlockNumStateInDb) : Prop :=
  hasAtLeastOneProposal b /\
  proposalsHaveSameBlockNum b /\
  NoDuplicate (map (roundNum ∘ cheader) (proposals b)).

(** `validDbModel` will go beyond just asserting [validBlockNumStateInDb] for every item in the [blockNumsStates] list: there are some inter-block-number constrants as well, e.g.
    - block numbers in the db are continguous, with no duplicates
    - the active block is currently exists in the Db.
    - ...
 *)

(** `contiguousBlockNums lb` asserts that block numbers in lb are continguous: has no holes. assumes lb is nonempty *)
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
  | [] => 0
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
  | h :: _ => Some h
  (** ^ unique, assuming [validBlockNumStateInDb b] *)   
  | [] => None
  end.

(** finalized proposal for a round number, if any *)
Definition finalizedProposal (b : BlockNumStateInDb) : option ProposalInDb :=
  match finalizedRoundNum b with
  | None => None
  | Some rnd => lookupProposalByRoundNum b rnd
  end.

(** lookup a [ProposalId] (block number, optional round number) in the Db *)
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
    
(** `validActiveProposal m`  asserts that if [activeProposal] is set,
    it must correspond to an existing proposal in `m`. *)
Definition validActiveProposal (m: DbModel) : Prop :=
  match activeProposal m with
  | None => True
  | Some pid => isSome (lookupProposal pid m)
  end.

(** all the proposals in the Db, across all block numbers*)
Definition allProposalsInDb (d: DbModel) :=
  List.flat_map proposals (blockNumsStates d).

(** Finally, `validDbModel` combines all invariants on the top-level DB model:
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


(** Ignore the next 8 lines (Coq boilerplate) *)
#[only(lens)] derive DbModel.
#[only(lens)] derive ProposalInDb.
#[only(lens)] derive BlockNumStateInDb.

Section with_Sigma.
Context `{Sigma:cpp_logic} {CU: genv} {MODd : trie_db.module ⊧ CU}.


  
(** * TrieDb/TrieRODb [Rep] predicates
  Rep predicates are one of the main ingredients of specifications.
  They define how an element of the model type in Coq is represented in memory/disk starting from the "this" memory location (base pointer of the object).
  They also assert ownership of such locations.
  If the object stores pointers to other memory locations or disk locations, Rep predicates can also assert what is stored at those locations and assert ownership of those locations.
  To understand this in more detail, please review the examples in the first quarter of Tutorial2 (linked at the top).
 *)

Definition TrieDbR (q:Qp) (m: DbModel) : Rep. Admitted.
(** ^ [this |-> TrieDbR q m] asserts that at the memory location [this], there is an object representing the [DbModel] [m].
    The "Admitted." indicates that we have not defined it yet and have asked Coq to leave it as a hole to be filled later.
    Rep predicates are usually an implementation detail, and clients do not need to know the exact definition.

    [this |-> TrieDbR q m] also asserts [q] fraction ownership of the object.
    The definition [TrieDbR q m] will also assert ownership of the associated memory and disk cells/blocks as functions of this [q].
    q ∈ (0,1].
    q must be 1 to be able to call methods that update the Db (e.g. commit, finalize). A smaller fraction suffices to read (e.g. read_storage).
*)

(** Even though users of TrieDb (e.g. when writing Coq proofs of callers of TrieDb methods) do not need to know the definition of TrieDbR, they do need a guarantee that it satisfies the following 3 properties. *)

(** The first property (below) property says that [this |-> TrieDb q m] must imply that [m] is valid. As discussed in Tutorial1, `|--` is separation logic entailment (implication) and `**` is the separating conjunction. *)
Lemma TrieDbREntailsValidity (q:Qp) (m: DbModel) : TrieDbR q m |--  TrieDbR q m ** [| validDbModel m|].
Proof. Admitted.

(** TrieDb is a concurrent library. When executing a block, the speculative executions of multiple transactions can concurrently read from the Db, but they will all read the pre-block state. No thread updates the Db during that time. The following lemma allows splitting the full (1) ownership of the TrieDb into smaller pieces so that we can pass those ownership pieces to several threads to read the Db concurrently.
*)
Lemma TrieDbRsplit (q1 q2:Qp) (m: DbModel) :
 TrieDbR (q1+q2) m |--  TrieDbR q1 m ** TrieDbR q2 m.
Proof. Admitted.

(** Finally, the lemma below formalizes that we can construct at most one TrieDb object per underlying storage location (dbpath). This will be provable when TrieDbR is fully defined because TrieDbR will hold the full authoritative ownership of the storage at dbpath and thus only one object can hold this ownership.
*)
Lemma max1TrieDbObject  (base1 base2: ptr) (m1 m2: DbModel) :
 dbpath m1 = dbpath m2 ->
 base1 |-> TrieDbR 1 m1 ** base2 |-> TrieDbR 1 m2 |-- [| False |].
Proof. Admitted.

(** We can construct several TrieRODb objects on the same underlying storage as an existing TrieDb object.
 Unlike ownership of primitive types, even if you hold the full TrieDbR ownership ([this |-> TrieDb 1 m]),
 other threads/processes can read (but not update) the underlying Db storage using a TrieRODb object.

 To get a sense of how TrieDb and TrieRODb can be defined to achieve this using concurrency invariants, review the 2nd and 3rd quarters of Tutorial2: [TrieDbR] is similar to uAuthR and [TrieRODbR] is similar to uFragR.

Unlike TrieDbR, the ownership of TrieRODb cannot assert the current state of the entire Db: there can be another process updating the Db concurrently. Nevertheless, operations on TrieRODb are logically atomic: they read from a single proposal rather than a mishmash of multiple proposals. *)

Definition TrieRODbR (q:Qp) (dbpath: DbPath) (activeProposal: option ProposalInDb) : Rep. Admitted.

(** ^  [this |-> TrieRODb q dbpath (Some pr)] asserts that the read operations on the object (e.g. `TrieRODb::read_storage`, `TrieRODb::read_account`) will read from the proposal [pr]. Any fraction [q] suffices to do reads: write operations are not supported anyway (they have [False] as a precondition).
 [q] must be 1 to destruct the object or to call `TrieRODb::set_block_and_round`, which can change the active proposal.

 [this |-> TrieRODb q dbpath None] does not suffice to issue any read: the client needs to first call `TrieRODb::set_block_and_round` to
 transform [this |-> TrieRODb q None] to [this |-> TrieRODb q (Some pr)] for some [pr] in case the call succeeds.
  *)
Definition FinalizedProposalForBlockNum (dbpath: DbPath) (blockNum: N) (p: ProposalInDb) : mpred. Admitted.
(** ^ [FinalizedProposalForBlockNum dbpath n p] asserts that p is the finalized proposal for block n. Because the TrieDb specs do NOT allow modifying finalized block numbers, this assertion is a [Persistent] assertion: once it is established, it always holds (unlike the assertion that the value of variable x is 2); thus, this assertion can be freely duplicated and shared with other threads/processes. In particular, this assertion is a postcondition of TrieDb::finalize. After calling TrieDb::finalize, a client application can send this assertion to another process (e.g. attached to a socket message) and then reason that if the recipient process calls TrieRODb::set_block_and_round(n), it will either fail (block n got evicted on garbage collection) or read p and nothing else. (Its definition will use logical/ghost locations which were covered in #<a href="https://youtu.be/vunTJ28Rt34">Tutorial3</a>#).


 Finally, we have enough vocabulary to write the specs.
    Except when committing the genesis block to the Db, before reading or updating the Db, we need to set the active block via set_block_and_round.
    So, let's see its spec first:
*)

(** * Spec of TrieDb::set_block_and_round *)
cpp.spec "monad::TrieDb::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as set_block_and_round_spec with (fun (this:ptr) =>
  \pre{preDb: DbModel} this |-> TrieDbR 1 preDb
  (** ^ requires full(1) ownernership of the TrieDb object.
      This guarantees that no other threads can be using this object concurrently to read (because reading requires non-zero ownership)
      This says that the object is in a state where the data it holds (together with the linked disk data)
      corresponds to some model element [preDb]. Because of the lemma [TrieDbREntailsValidity],
      this also means that all the class invariants defined in [validDbModel] hold just before the call
     *)
  \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))
  (** ^ the [{pid: ProposalId}] part universally quantifies over a [ProposalId] that
      serves the combined model of the block_number and round_number arguments.
      [Vint (idBlockNum pid)] says that the block_number argument should be
      the number [idBlockNum pid]. Because [pid] is universally quantified, there is no loss in generality.
   *)  

  \arg{roundLoc} "round_number" (Vptr roundLoc)
  \prepost roundLoc |-> optionalPrimR 1 "unsigned long" (idRoundNum pid)
  (** ^ the above 2 lines together describe the round_number argument.
      Unlike `block_number`, which is a scalar value of type `uint64_t`, round_number has type `std::optional<uint64_t>`.
      In our C++ formalization, composite types (struct/array) are represented as memory locations that store the composite value.
      So, the first line names that location as [roundLoc] (typically on the stack).
      The next line says that at [roundLoc] we have the representation of the optional number [idRoundNum pid],
      which is of type [option N] in Coq. Note that pid was already quantified above when specifying the `block_number` argument.


      Above, we have connected all the arguments of the method (including the implicit `this` argument) to their corresponding
      models in Coq (e.g. DbModel) via their Rep predicates (e.g. TrieDbR, optionalPrimR).
      These Rep predicates already assert that the class invariants hold.
      Next, we specify any other condition that must hold at the beginning (precondition):
   *)  

  \pre [| isSome (lookupProposal pid preDb)|]
  (** ^ This precondition asserts that the chosen proposal id must exist in the Db: the lookup in the Db model ([preDb]) must not return [None] (analogous to `std::nullopt`). *)

  \post this |-> TrieDbR 1 (preDb &: _activeProposal .= Some pid)
   (** ^ this is the post condition. it returns back the full ownernership of TrieDbR but with a modified model, capturing
       how the implementation updates the state of the Db.
       In the model, the update is merely to set the [activeProposal] field to the supplied [pid] (of type [ProposalId]).
       All other fields are unchanged.
       As we will see in the spec of `TrieDb::read_storage`, the read operations lookup this proposal id ([activeProposal]) in the [blockNumsStates] list of [DbModel].
   *)
).


(** * Two specs of TrieRODb::set_block_and_round *)

(** The spec of the same method for TrieRODb looks very different. The main reason is that unlike TrieDb, TrieRODb does not have authoritative ownership of the underlying Db: while TrieRODb is reading, a TrieDb can be racing to write. Unlike [TrieDbR] which asserts what is the state of the whole Db, [TrieRODbR] just asserts the exact proposal (contents, not id) that the reads will read.


Intuitively, at `TrieRODb::set_block_and_round`, TrieRODb *logically atomically* "snapshots" the entire proposal. Until the next call to `TrieRODb::set_block_and_round`, future reads (e.g. `TrieRODb::read_storage`) will read from this snapshot *even* if a `TrieDb::commit` overwrote the proposal for this round number. One caveat is that the Db may decide to garbage collect this proposal (entire block number of this proposal) at some TrieDb::commit thus TrieRODb::read_storage may fail. But if it succeeds, it must read from the snapshot


The spec below specifies the intended implementation of  monad::TrieRODb::set_block_and_round, NOT the current implementation.
The current implementation crashes when the requested block/round number is not found.
Unlike TrieDb, TrieRODb has no control on updates to the Db. TrieDb::commit can trigger garbage collection and eviction of blocks.
Ideally, TrieRODb should be crash-resistant to arbitrary concurrent updates by a TrieDb on the same dbpath.


Formally, in the spec of `TrieDb::set_block_and_round` (above), there was no need to return an error because
the precondition  [isSome (lookupProposal pid preDb)] ensured that the error case will never happen.
However, [TrieRODbR] cannot talk about the whole Db state (it just asserts the currently active proposal content).
Thus we, cannot even write that precondition in the spec of TrieRODb. 
Indeed, there is already a #<a href="https://github.com/category-labs/monad/blob/3f5ea3fa8954025641cab230405738544a129d7f/libs/execution/src/monad/db/trie_rodb.hpp##L39">TODO comment</a># about returning an error instead of crashing.


Thus, the spec below is for the variant of the implementation that returns a bool indicating whether the operation succeeded.
The postcondition branches on this return value to assert what holds in each case.

 *)


cpp.spec "monad::TrieRODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" 
  as rodb_set_block_and_round_nd_spec from (trie_rodb.module) with (fun (this:ptr) =>
  \pre{(preActive: option ProposalInDb) (dbpath: DbPath)} this |-> TrieRODbR 1 dbpath preActive
  (** ^ same as the TrieDb case, except that here we have [TrieRODbR] instead of [TrieDbR].
      [preActive] is the previously active proposal, possibly [None].
      As mentioned above, if [preActive] is not [None], it has the entire content ("snapshot") of the proposal (e.g. account states,..)
      and is not just the id: check the definition of [ProposalInDb].
      Note that this method requires a full (1) ownership of this object: this ensures that no other thread is concurrently invoking any other method on this object, not even `TrieRODb::read_storage`.
      This is necessary to avoid UB races on the `prefix_cursor_` field.

      However, another TrieRODb object could be doing racy method calls including monad::TrieRODb::set_block_and_round.
      But that is not a problem because they change the `prefix_cursor_` field of that object, not this object.
      Also, the underlying Db is well protected by other synchronization mechanisms.
   *)
  \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))
  \arg{roundLoc} "round_number" (Vptr roundLoc)
  \prepost roundLoc |-> optionalPrimR 1 "unsigned long" (idRoundNum pid)
  (** the above 3 lines are exactly as in the TrieDb spec variant above*)

  \post{ret:bool} [Vbool ret]
    if ret then Exists proposal,
                  this |-> TrieRODbR 1 dbpath (Some proposal)
                 ** if idRoundNum pid is None
                    then FinalizedProposalForBlockNum dbpath (idBlockNum pid) proposal
                    else emp
    else this |-> TrieRODbR 1 dbpath None
  (** ^ the above 5 lines are the interesting bits of this spec. It says that the function returns a boolean value.
      Depending on the return value, different assertions hold.
      If [false], it means the operation failed, e.g. because all data for that block number got garbage collected.
      The [None] in [this |-> TrieRODbR 1 dbpath None] means that no shapshot is active and reads are forbidden in this state.
      A client will need to try again, e.g. with a different (e.g. higher) block number and get it to succeed before issuing any reads like `TrieRODb::read_storage`.

     If the return value is [true], we get [this |-> TrieRODbR 1 dbpath (Some proposal)]
     which asserts that [proposal] is now the active snapshot. The [Exists] existential quantification means that
     proposal is arbitrary from the client's point of view.
     In this spec, the client gets no guarantee about what proposal will be returned.
     Below, we will see a different spec where there is a guarantee, but it requires a stronger precondition
     and requires that this block number was already finalized.

     To appreciate the added power of the spec below, it is important to understand the second conjunct above in the case
     [ret] is [true]: if [idRoundNum pid is None], meaning that the block number was already finalized, we get as postcondition another assertion:
      [FinalizedProposalForBlockNum dbpath (idBlockNum pid) proposal].
     As explained where [FinalizedProposalForBlockNum] was introduced (can click it to go there), this is a persistent assertion and can be freely duplicated and shared.
     In particular, it can be used as a precondition to the next spec of the same method
   *)
).

cpp.spec "monad::TrieRODb::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as rodb_set_block_and_round_det_spec  from (trie_rodb.module) with (fun (this:ptr) =>
  \pre{preActive dbpath} this |-> TrieRODbR 1 dbpath preActive
  \arg{pid: ProposalId} "block_number" (Vint (idBlockNum pid))
  \arg{roundLoc} "round_number" (Vptr roundLoc)
  \prepost roundLoc |-> optionalPrimR 1 "unsigned long" (idRoundNum pid)

  \pre{proposal} FinalizedProposalForBlockNum dbpath (idBlockNum pid) proposal
  (** the above line is new w.r.t. the spec above. In the proof of the caller, when using this spec,
      they have to pass in a proof that the snapshot [proposal] was finalized for block number [idBlockNum pid].
      In return, now they get a guarantee in the postcondition that if the operation is succcessful,
      the snapshot will be exactly [proposal] and nothing else.
      This is because finalized blocks cannot change: the       TrieDb::commit   specs forbid that as we will see below.
      However, this operation can fail nevertheless if the block number was garbage collected.
   *)
  \post{ret} [Vbool ret]
     if ret then this |-> TrieRODbR 1 dbpath (Some proposal)
     (** ^ [proposal] is not existentially quantified here: we know exactly which snapshot will be chosen *)              
     else  this |-> TrieRODbR 1 dbpath None
   (** ^ the block number got garbage collected *)
 ).

(** As an example application of the above 2 specs, we can prove that the following function must return true.
[[
bool readTwice(TrieRODb & rdb, Address const &addr, Incarnation inc, bytes32_t const &key) {
 bool success;
 success=rdb.set_block_and_round(10);
 if(!success)
      return true;
 bytes32_t r1 = rdb.read_storage(addr, inc, key);
 success=rdb.set_block_and_round(10);// use the second spec to guarantee that we get the same snapshot again
 if(!success)
      return true;
 bytes32_t r2 = rdb.read_storage(addr, inc, key);
 if (r1<>r2)
    return false;
 return true;
}
]]

 To understand it why fully, we need to first look at the spec of `TrieRODb::read_storage`:
 *)

(** * Spec of TrieRODb::read_storage *)

cpp.spec "monad::TrieRODb::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
  as rodb_read_storage_spec from (trie_rodb.module) with (fun (this:ptr) =>
  \prepost{(q:Qp) (activeProposal: ProposalInDb) (dbpath: DbPath)} this |-> TrieRODbR q dbpath (Some activeProposal)
 (** ^ \prepost means that this is both a precondition and a postcondition: reading does not change the active proposal. for read_storage, any positive fraction ownership suffices. This means that other thread can be racing to do reads. The assertion [this |-> TrieRODbR q dbpath (Some activeProposal)] can only be obtained as a postcondition of a successful call to `TrieRODb::set_block_and_round`, where the call chose the snapshot [activeProposal]. As the postcondition shows below, the storage would be read from this proposal. [ProposalInDb] has the [postBlockState] field which captures the state after executing this proposal. So the postcondition just looks up the storage in that state *)

  \arg{addressp} "address" (Vptr addressp)
  \prepost{q address} addressp |-> addressR q address
  \arg{incp} "incarnation" (Vptr incp)
  \prepost{q blockTxInd} incp |-> IncarnationR q blockTxInd
  \arg{keyp} "key" (Vptr keyp)
  \prepost{key:N} keyp |-> bytes32R q key
  (**  The above 6 lines just connect the 3 arguments (each of a composite type) to corresponding Coq models *)
  \post{retp:ptr} [Vptr retp]
    retp |-> bytes32R 1
               (lookupStorage (postBlockState activeProposal) address key blockTxInd)).

(** * Spec of TrieDb::read_storage *)

(** The spec of `TrieDb:read_storage` is similar. The main difference is that [TrieDbR] can talk about the whole db state [DbModel]. Also, `TriedDb::set_block_and_round` (spec discussed above) just sets the block number and round numbers in the [activeProposal] field of [DbModel]. Unlike `TrieRODb::set_block_and_round`, it does NOT do a logical snapshot. So, the last \pre requires that the lookup of the active proposal succeds and evaluates to [Some activeProposal] for some [activePropsal].
The postcondition then looks up the key in the [postBlockState] of that proposal
*)
cpp.spec "monad::TrieDb::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
  as read_storage_spec with (fun (this:ptr) =>
  \prepost{q preDb} this |-> TrieDbR q preDb
  \arg{addressp} "address" (Vptr addressp)
  \prepost{q address} addressp |-> addressR q address
  \arg{incp} "incarnation" (Vptr incp)
  \prepost{q blockTxInd} incp |-> IncarnationR q blockTxInd
  \arg{keyp} "key" (Vptr keyp)
  \prepost{key:N} keyp |-> bytes32R q key

  \pre{activeProposal} [| lookupActiveProposal preDb = Some activeProposal |]
  \post{retp:ptr} [Vptr retp]
      retp |-> bytes32R 1
         (lookupStorage (postBlockState activeProposal) address key blockTxInd)).


(** * Spec of TrieDb::commit *)

(** The specs of other read functions (e.g. read_account, root_hash ...) in TrieDb are very similar to the spec of `TrieDb::read_storage`: just replace [lookupStorage] by appropriate Coq functions on [ProposalInDb].
Similarly, the specs of other read functions (e.g. read_account, root_hash ...) in TrieRODb are very similar to the spec of TrieRODb::read_storage.
So we will not discuss specs of the other read methods.
The other interesting functions from execution perspective are `TrieDb::commit` and `TrieDb::finalize`. We will look at their spec below. 
(TrieRODb does not support update methods like commit, finalize.)

But before that, we sketch why the above specs of TrieRODb suffice to prove the logical atomicity of eth_call even though it does several calls to TrieRODb.

eth_call implementation first #<a href="https://github.com/category-labs/monad/blob/3f5ea3fa8954025641cab230405738544a129d7f/libs/rpc/src/monad/rpc/eth_call.cpp##L102">calls</a>#  TrieRODb::set_block_and_round. After that, it only issues reads, which happen in the #<a href="https://github.com/category-labs/monad/blob/3f5ea3fa8954025641cab230405738544a129d7f/libs/rpc/src/monad/rpc/eth_call.cpp##L214">call</a># to `execute_impl_no_validation`.

It has been claimed that eth_call can be requested even for unfinalized proposals and that execution can commit multiple distinct proposals for the *same* round number. (every round has 1 leader and 1 block number). Thus there it is important that if execution "overwrites" a round number with a different proposal in between 2 reads by `execute_impl_no_validation`, eth_call does not produce results that correspond to a mishmash of 2 different proposals. The TrieRODb specs above already allows us to prove that no matter what TrieDb does after a successfull call to TrieRODb::set_block_and_round, the TrieRODb read methods will keep reading from the snapshot in the postcondition of TrieRODb::set_block_and_round. Thus, eth_call will never see any overwrite that happens after the only call to TrieRODb::set_block_and_round.

The (only) call to TrieRODb::set_block_and_round in eth_call_impl is the commit point of eth_call_impl. In concurrency proofs of logical atomicity, the main challenge is typically to identify and prove a commit point, which is a logically atomic operation in the implementation such that from the perspective of other threads/processes the entire implementation can be equivalently considered to execute at that point. Before and after the TrieRODb::set_block_and_round, whatever eth_call does does not affect and is not affected by any TrieDb operation that may be racing.

Next, we will discuss the spec of TrieDb::commit. Towards that, we need to define some helper functions to define the model state (DbModel) in the postcondition.
Intuitively, TrieDb::commit just adds a new proposal to the Db, along with the full EVM state after executing the block.
We already have the Coq type ProposalInDb which captures the entire proposal including full EVM state after executing the block, and the receipts from the execution of the block.
So we just need to define how to add a new [ProposalInDb] to a [DbModel].
So, the next 2 items define [addNewProposal].
This is much simpler than the implementation where the focus is on efficiency: so TrieDb::commit cannot take the entire EVM state (state of all accounts) as an argument: that would be prohibitively big. So it only takes the diff w.r.t the [postBlockState] of the currently active proposal. But in specifications, simplicity not efficiency is the main concern: so the specs take the whole [ProposalInDb], which includes the whole EVM state after executing the proposal, as the main logical argument.
*)

(** Next, `updateBlockNum d bnum f` applies an update function [f] to the single [BlockNumStateInDb] in [d] whose block number is [bnum]. All other block numbers remain unchanged. This is used in defiining the postcondition states after the commit and finalize methods *)
Definition updateBlockNum (d: DbModel) (bnum: N)
  (f: BlockNumStateInDb -> BlockNumStateInDb) : DbModel :=
  d &: _blockNumsStates .= 
           map (fun b => if bool_decide (blockNum b = bnum) then f b else b)
           (blockNumsStates d).


(** The next definition is the main ingredient of the postcondition of TrieDb::commit. it first checks whether the there is already a [BlockNumStateInDb] preDb with the exact same block number as the one of [newProposal]. If there is, it just updates that block number state to add the new proposal to its list of proposals. In case that block number state does not exist, it adds a new one with the singleton list of proposals, containing just [newPrpoposal]. The [blockNumsStates] field of [BlockStateInDb] is always used in an order insensitive way in the specs. so it suffices to just add it to the beginning. *)
Definition addNewProposal
  (preDb       : DbModel)
  (newProposal : ProposalInDb) : DbModel :=
  let bnum := pblockNum newProposal in
  match lookupBlockByNum bnum preDb with
  | Some _ =>
      updateBlockNum preDb bnum (fun bs => bs &: _proposals .= (newProposal::proposals bs))
   (** ^ add proposal into existing [BlockNumStateInDb] *)
  | None =>
      preDb &: _blockNumsStates .=
            ({| proposals := [newProposal]; finalizedRoundNum := None |}::(blockNumsStates preDb)) 
   (** ^ add a new [BlockNumStateInDb] *)
  end.

(** The final ingredient in the postcondition of TrieDb::commit is to model garbage collection. Garbage collection only happens during TrieDb::commit calls, and not during any other method. Also, there is no separate thread doing garbage collection spontaneously: that could have complicated the specs. Next, `gcToHistoryLen len dbm` trims the lower block number states to ensure that the number of block numbers stored in dbm is no more than len. The spec choses [len] non-deterministically (existential quantification) so the client cannot depend on concrete implementation details on which commits do garbage collection and how much. However, there is a guarantee that [256<len].
*)

Definition gcToHistoryLen (len: N) (d: DbModel) : DbModel :=
  let blockNums := List.map blockNum (blockNumsStates d) in
  let maxBlockNum := maxL blockNums in
  let minBlockNum := minL blockNums in
  if bool_decide (maxBlockNum <= minBlockNum + len)
  then d
  else let newBlockNumsStates :=
         List.filter (fun b => bool_decide (maxBlockNum-blockNum b <= len)) (blockNumsStates d) in
       d &: _blockNumsStates .= newBlockNumsStates.


(** `stateAfterActiveProposal m` returns the EVM state after executing the active proposal. The StateDeltas argument in TrieDb::commit is
  diff between the state after the active propposal and the state after executing the new proposal on top of the active proposal *)
Definition stateAfterActiveProposal (m: DbModel) : evm.GlobalState :=
  match lookupActiveProposal m with
  | None => dummyEvmState
  | Some p => postBlockState p
  end.

(** Finally, we have all the ingredients for the spec of TrieDb::commit: *)

  cpp.spec
    "monad::TrieDb::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<const monad::vm::interpreter::Intercode>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<const monad::vm::interpreter::Intercode>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
    as commit_spec with (fun (this:ptr) =>
    \pre{(preDb:DbModel) (newProposal : ProposalInDb)} this |-> TrieDbR 1 preDb
   (** ^ requires full(1) ownernership of the TrieDb object. This guarantees that no other threads can be using this object concurrently, not even to read (because reading requires non-zero ownership). However, there can be another thread/process using a TrieRODb object to do a concurrent read.

     [preDb] and [newProposal] are the only 2 arguments of this function at the logical level of this spec. All C++ arguments can be tied to these:
    *)

    \arg{(dloc: ptr) (q: Qp)} "state_deltas" (Vptr dloc)
    \prepost dloc |-> StateDeltasR q (stateAfterActiveProposal preDb, postBlockState newProposal)
    (** ^ the \arg line above asserts that the the state_deltas argument has a memory location [dloc]. Then, the \prepost line asserts that [dloc] has an object that represents delta/diff between thefull  EVM state after the active proposal in preDb and the full EVM state after executing [newProposal]. More generally [l |-> StateDeltasR q (old, new)] asserts that at location [l] we have an object of type StateDeltas which represents the difference between the full EVM states [old] and [new]. StateDeltas is a map from account addresses to diffs in account states. Every account that has a different value between [old] and [new] must have an entry in this map. The diff in account states stores the new/old balance/nonce etc and also has another map that maps storage keys to pairs of values (oldkv, newkv).
     *)

    \arg{(cloc:ptr)} "code" (Vptr cloc)
    \prepost cloc |-> CodeDeltaR q (stateAfterActiveProposal preDb, postBlockState newProposal)
    (** the code argument is similar. it is a map from code hashes to code. this map must contain an entry for all the code hashes that exist in [postBlockState newProposal] but does not exist in [stateAfterActiveProposal preDb]. Intuitively, it has one entry for every new code hash that got deployed in [newProposal].

    The other arguments are just other contents of [newProposal], e.g. transactions, ommers, withdrawals, senders. The specification below of the other arguments are much more straightforward: [newProposal] of type [ProposalInDb] already includes the models for all those parts of a Proposal as fields or fields of fields. So the specs of args below just connect the C++ argument to the corresponding parts of the [newProposal] model.
     *)

  \arg{hloc} "consensus_header" (Vptr hloc)
  \prepost hloc |-> ConsensusBlockHeaderR q (cheader newProposal)
      
  \arg{rloc} "receipts" (Vptr rloc)
  \prepost rloc |-> VectorR "monad::Receipt" ReceiptR q (txResults newProposal)
          
  \arg{cfloc} "cfloc" (Vptr cfloc)
  \prepost cfloc |->  EmptyCallFramesR q
   
  \arg{sloc} "senders" (Vptr sloc)
  \prepost sloc |-> VectorR "evmc::address" (addressR q) q
                         (map sender (transactions (proposedBlock newProposal)))

  \arg{tloc} "transactions" (Vptr tloc)
  \prepost tloc |-> VectorR "monad::Transaction" (TransactionR q) q
                        (transactions (proposedBlock newProposal))

  \arg{oloc} "ommers" (Vptr oloc)
  \prepost oloc |-> VectorR "monad::BlockHeader" (BheaderR q) q
                         (ommers (proposedBlock newProposal))

  \arg{wloc} "withdrawals" (Vptr wloc)
  \prepost wloc |-> optionR
        "std::vector<monad::Withdrawal>"
          (VectorR "monad::Withdrawal" (WithdrawalR q) q)
          q
          (withdrawals (proposedBlock (newProposal)))

  \pre [| match activeProposal preDb with
              | Some activeProp =>
                  pblockNum newProposal = 1 + idBlockNum activeProp
              | None => pblockNum newProposal = 0
              end
         |]
    (** ^ other than the class invariants already captured in the Rep predicates TrieDbR and those of the arguments above, the only other precondition is in the \pre line above. It says that if there is an active proposal (set by calling set_block_and_round), the block number of [newProposal] must be 1+ block number of the active proposal.
If there is no active proposal, than [newProposal] must be the genesis block (block number 0).
     *)
  \post Exists (postGcHistLen:N), [| 256 <= postGcHistLen|]
            ** this |-> TrieDbR 1 (gcToHistoryLen postGcHistLen (addNewProposal preDb newProposal))).
  (** ^ the postcondition just asserts that the state of the Db changes to one that corresponds to the new model ([DbModel]) computed by the [addNewproposal] followed by the [gcToHistoryLen] functions that were explained just above the spec. [postGcHistLen] is existentially quantification so the caller's proof cannot assume anything about how many blocks numbers, if any, the garbage collection (GC) phase will reclaim, except that it reduce the history length (number of block numbers) to less thatn 256. Also, if the history length was alredy less thant 256 no GC will happen: this follows from the definition of [gcToHistoryLen].


   Our final spec is for TrieDb::finalize(). We just need one helper function for the spec.
   
   *)

(** * Spec of TrieDb::finalize *)
  
(** The defn below finds the smallest block number that does not have a finalized proposal *)
Definition minUnfinalizedBlockNum (d: DbModel) : option N :=
  let unfin := filter (fun b => finalizedProposal b = None) (blockNumsStates d) in
  match unfin with
  | [] => None
  | _ => Some (minL (map blockNum unfin))
  end.

cpp.spec "monad::TrieDb::finalize(unsigned long, unsigned long)"
  as finalize_spec with (fun (this:ptr) =>
  \pre{preDb} this |-> TrieDbR 1 preDb
  \arg{blockNum:N}   "block_number" (Vint blockNum)
  \arg{roundNum:N}   "round_number" (Vint roundNum)
  \let pid := {| idBlockNum := blockNum; idRoundNum:= Some roundNum |}
  \pre{prp} [| lookupProposal pid preDb = Some prp|]
  \pre [| minUnfinalizedBlockNum preDb = Some blockNum |]
    (** ^ 2 preconditions: the proposal to be finalized must exist in the Db and must have the lowest unfinalized block number: we cannot finalize a proposal for block number 5 before something for block 4 is fianlized *)
  \post
       this |-> TrieDbR 1 (updateBlockNum preDb blockNum (fun d => d &: _finalizedRoundNum .= (Some roundNum)))
       ** FinalizedProposalForBlockNum (dbpath preDb) blockNum prp
                             ).
(** ^ the first conjunct in the postcondition is straightforward: just asserts that the state of the Db changes to one that corresponds to the new model ([DbModel]) computed by [updateBlockNum], which updates the target block number to record the finalized round number. The second conjunct is more interesting. It is an assertion/token that can be used to claim that the finalized proposal for [blockNum] is [prp], which was obtained by looking up the round number and block number. For example, it can be passed on as a precondition to the second spec of TrieRODb::set_block_and_round to reason that if it succeeds, the chosen snapshot must be prp. For example, in the application below, one can use this to reason that the second read_storage (done by another process) returns the same value:
[[
Process1:
tdb.finalize(2,3)
tdb.set_block_and_round(2);
v=tdb.read_storage(ac, inc, (*key= *) 100);
write v to shared memory location l;
Process2.signal();


Process2:
Process2.wait();
v1= read shared memory location l;
bool success=trodb.set_block_and_round(2);// use the second spec
if (!success) exit;
v2=trodb.read_storage(ac, inc, (*key= *) 100);
if (v1<>v2) launch nuclear missiles
]]
 *)

(** * Spec of other TrieDb methods *)

(** the spec of other functions are straightforward: *)

Definition maxFinalizedBlockNum (d: DbModel) : option N :=
  let unfin := filter (fun b => isSome (finalizedProposal b)) (blockNumsStates d) in
  match unfin with
  | [] => None
  | _ => Some (maxL (map blockNum unfin))
  end.

cpp.spec "monad::TrieDb::update_verified_block(unsigned long)"
  as update_verified_block_spec with (fun (this:ptr) =>
  \prepost{q preDb} this |-> TrieDbR q preDb
  \arg{blockNum:N}   "block_number" (Vint blockNum)
  \pre [| lastVerifiedBlockNum preDb<= blockNum |]
    (** ^ lastVerifiedblockNum can never decrease *)
  \pre [| match maxFinalizedBlockNum preDb with
            | Some s =>  blockNum <= s
          (** ^ cannot verify an unfinalized block. *)
            | None => False
         (** ^ if no block has been finalized yet, cannot call this method *)
            end |]
  \post this |-> TrieDbR q (preDb &: _lastVerifiedBlockNum .= blockNum)).



cpp.spec "monad::TrieDb::update_voted_metadata(unsigned long, unsigned long)"
  as update_voted_metadata_spec with (fun (this:ptr) =>
  \pre{preDb} this |-> TrieDbR 1 preDb
  \arg{blockNum:N}   "block_number" (Vint blockNum)
  \arg{roundNum:N}   "round"        (Vint roundNum)
  \post this |-> TrieDbR 1 (preDb &: _votedMetadata .= Some (blockNum, roundNum))).


  
End with_Sigma.

(**  Ownership flow of [TrieDbR] in monad::propose_block in runloop_monad.cpp:
[[
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

    Each fiber reads can concurrently read the db and builds [BlockState] deltas only: no updates to the db

 3) After all fibers finish, the final state is in BlockState, encoded as StateDeltas w.r.t. the preblock state. ownership of TrieDb is rejoined and then commit is called:

    +--------------------------------------+
    | TrieDbR (ownership rejoined = 1)     |
    +--------------------------------------+
    | TrieDb::commit(...)                  |
    +--------------------------------------+

]]
*)
