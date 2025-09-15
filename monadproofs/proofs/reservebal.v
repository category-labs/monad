(** * Appendix: Coq proof of reserve-balance safety
    This file accompanies the blog post and serves as a literate
    walkthrough of the final model.

    The guiding idea is simple:

    - *Consensus* computes a **worst-case, fee-only budget** (the “effective
      reserve”) for the yet-to-be-executed suffix and only proposes blocks when
      that budget stays non-negative for every **sender** that appears later.

    - *Execution* runs the actual EVM step and enforces that **no account dips
      below its protected reserve slice** (with a carefully fenced “emptying”
      exception). If a transaction would violate that, it is reverted in place.

    The definitions below encode those two algorithms and the invariants we prove
    about them. The consensus check is defined in [consensusAcceptableTxs], the execution check is in [execTx]. The main soundness theorem is [fullBlockStep]. References to any Coq item are hyperlinked to its definition if the definition is in this file or in the Coq standard library.
*)


Require Import monad.proofs.evmopsem.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.misc.
Require Import bluerock.hw_models.utils.
Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.
Import Forward.
Import miscPure. (* has a better version of forward_reason *)
Set Default Goal Selector "!".
Require Import bluerock.auto.cpp.tactics4.
Open Scope N_scope.


(** * Preliminaries *)

(** This is the full EVM state that EVM execution takes as input and returns as output. *)
Definition StateOfAccounts : Type := EvmAddr -> AccountM.

Definition addrDelegated  (s: StateOfAccounts) (a : EvmAddr) : bool :=
  match delegatedTo (s a) with
  | [] => false
  | _ => true
  end.

(** Many of the EVM semantics definitions we use come from Yoichi's EVM semantics, developed several years ago. The definition of [Transaction] there lacks fields to support newer features like delegation. Also, the last field is to support user-configurable reserve balances in Monad. There is a new transaction type which can update the configured reserve balance of the sender. Such transactions do nothing else. *)
Record TxExtra :=
  {
    dels: list EvmAddr;
    undels: list EvmAddr;

    (** The fields above should ultimately come from EVM semantics and not here. The fields below are monad-specific. *)
    reserveBalUpdate': option N
   (** ^ updates the reserve balance of the sender if Some. In that case, the transaction does nothing else, e.g., smart contract invocation or transfer. *)
  }.

Definition isEmpty {T} (t:list T) : bool :=
  match t with
  | [] => true
  | _ => false
  end.
    
Definition reserveBalUpdate (t: TxExtra) : option N :=
  if isEmpty (dels t ++ undels t) then reserveBalUpdate' t else None.

Definition TxWithHdr : Type := (BlockHeader * TxExtra) * (Transaction).

(** Our **fee upper bound** is intentionally pessimistic: the consensus rule
    reasons about [gas_limit × gas_price], never about *actual* gas used.  This
    mismatch is the source of slack that makes safety proofs simple while
    remaining implementable. *)
Definition maxTxFee (t: TxWithHdr) : N :=
  ((w256_to_N (block.tr_gas_price t.2)) * (w256_to_N (block.tr_gas_limit t.2))).


(** The proofs in this file never unfold the definition of [maxTxFee], so nothing will break if this definition is changed.  *)
Opaque maxTxFee.
Ltac sauto := intros; forward_reason; rwHyps; simpl in *; autorewrite with syntactic in *; try lia; try congruence; try eauto;(case_match_concl; simpl in *; autorewrite with syntactic; try lia; try congruence; fail).

Section K.
(** Parameterization by the lookahead window [K]:
consensus can be ahead of execution by at most K. n+Kth block must have the state root hash after execution block n. the next 2 variables are parameters for the rest of the proofs.
All “emptying” checks therefore only look at activity within a [K]-sized
window. We also fix a default reserve cap used when an account has never reconfigured its reserve.
 *)
Variable K: N.
Variable DefaultReserveBal: N.

Definition sender (t: TxWithHdr): EvmAddr := tsender t.2.

Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value t.2).

Definition addrsDelUndelByTx  (tx: TxWithHdr) : list EvmAddr := (dels tx.1.2 ++undels tx.1.2).

Definition txDelUndelAddr (addr: EvmAddr) (tx: TxWithHdr) : bool :=
  bool_decide (addr ∈ addrsDelUndelByTx tx).

Definition txBlockNum (t: TxWithHdr) : N := number t.1.1.

Definition reserveBalUpdateOfTx (t: TxWithHdr) : option N :=
  reserveBalUpdate t.1.2.

(** To implement reserve balance checks, execution needs to maintain some extra state (beyond the core EVM state) for each account:  *)
Record ExtraAcState :=
  {
    lastTxInBlockIndex : option N;
    (** ^ last block index where this account sent a transaction. In the implementation, we can just track the last 2K range, e.g. this can be None if the last tx was more than 2K block before. we do not need to store this information in the db as it can be easily computed *)
    lastDelUndelInBlockIndex : option N;
    (** ^ last block index where this address was delegated or undelegated. In the implementation, we can just track the last 2K range.*)
    configuredReserveBal: N;
    (** ^ the current configured reserve balance of the account. will either be [DefaultReserveBal] or something else if the account sent a transaction where [reserveBalUpdate] is not [None] *)
  }.

#[only(lens)] derive ExtraAcState.
#[global] Instance inhabitedeacs : Inhabited ExtraAcState := populate (Build_ExtraAcState None None DefaultReserveBal).


Definition ExtraAcStates := (EvmAddr -> ExtraAcState).

(** Our modified execution function which does reserve balance checks will use the following type as input/output. Consensus checks also take this as input, where the [Augmentedstate] is the state after N-K block when proposing a new block. However, when next pending (already proposed) block is executed, it can be a later state. *)
Definition AugmentedState : Type := StateOfAccounts * ExtraAcStates.



Definition hasCode (s: StateOfAccounts) (addr: EvmAddr): bool:=
  block.block_account_hascode (coreAc (s addr)).

Opaque hasCode.

Definition updateKey  {T} `{c: EqDecision T} {V}  (oldmap: T -> V) (updKey: T) (f: V -> V) : T -> V :=
  fun k => if (bool_decide (k=updKey)) then f (oldmap updKey) else oldmap k.

Disable Notation "!!!".

(* TODO: remove *)
Lemma updateKeyLkp3  {T} `{c: EqDecision T} {V} (m: T -> V) (a b: T) (f: V -> V) :
  (updateKey m a f)  b = if (bool_decide (b=a)) then (f (m a)) else m  b.
Proof using.
  reflexivity.
Qed.

(** * Consensus Check (algo 1)
Below, we build up the definition of the consensus check [consensusAcceptableTxs]
 *)
(**  The “emptying” gate:

    A sender may “empty” (i.e., allow value to eat into reserve for this one tx)
    iff all three are true:

    - it is *not* currently delegated,
    - it had no delegation change within the last [K] blocks (including the
      in-flight suffix),
    - it did not send a transaction in the last [K] blocks (including the
      in-flight suffix).

    This gate is what lets consensus handle fee-only budgets and still tolerate
    occasional value drains safely. *)
(** the number is just the effective reserve balance.

 TODO: tell coqdoc to print Set as Type*)
(* shallow exec info for 1 account *)
Record ShallowExecRes  : Set := mkNotDelCase
  {
    balanceLb: Z;
    configuredRB: N;
    delegated: bool;
    feeSolvent: bool (* if not delegated, balanceLb being negative does not necessarily mean fee insolvency, e.g when the balanceLb is sufficient to cover fees but not enough to cover value transfer of an emptying tx  *)
  }.

(** The effective reserve map:

    Consensus reasons about *how much of the protected (reserve) slice of the balance
    can be consumed* by
    the yet-to-run suffix.  This is the “effective reserve” map:
    - It is initialized with [min(balance, configuredReserve)].
    - Every transaction removes *at most* its fee from the sender’s entry,
      except for the “emptying” hole, where the pessimistic removal accounts
      for [value + fee] in one shot.

    Notice the type is [Z]: negative entries encode an *over-consumption* that
    should make the proposal unacceptable.
TODO: rename to ShallowExecResults
 *)
Definition ShallowExecResults := EvmAddr -> ShallowExecRes. (* 2nd item is the configured reserve balance *)

Definition configuredReserveBalOfAddr (s: ExtraAcStates) addr := configuredReserveBal (s addr).

Open Scope Z_scope.

Definition balanceOfAc (s: StateOfAccounts) (a: EvmAddr) : N :=
  balance (s a).

Definition updateBalanceOfAc (s: StateOfAccounts) (addr: EvmAddr) (upd: N -> N) : StateOfAccounts :=
  updateKey s addr (fun old => old &: _balance %= upd).

Definition balanceOfAcA (s: AugmentedState) (ac: EvmAddr) := balanceOfAc  s.1 ac.
(*
where do we get the block index of the block being built ? we have no tx here 
Definition consideredDelegated
  (state : AugmentedState) addr: bool :=
  let consideredDelegated := (addrDelegated state.1 addr)
                   || indexWithinKOf state.2 
*)
Definition initialShallowExecResults (s: AugmentedState) : ShallowExecResults :=
  fun addr =>
    let crb := configuredReserveBalOfAddr s.2 addr in 
    let del := addrDelegated s.1 addr in
    let bal := balanceOfAc s.1 addr in 
    {|
      balanceLb := if del then bal `min` crb else bal;
      configuredRB := crb;
      feeSolvent := true; (* the caller ensures that this state is obtained after successful execution, so it must be feeSolvent *)
      delegated := del; 
    |}.

(*
AA: balance 10
reservebal:=5
newtx: value 6, fee 1
undelegated.

 *)

(*
AA: balance 10
reservebal:=5
newtx: value 1, fee 6
undelegated: accepted
delegated: rejected
*)

(** Consensus’ decrement step:

    [shallowExectTx] is the algebraic heart of consensus check algorithm:
    fold this function left-to-right over the suffix, and you get the remaining
    worst-case protected reserve for every sender.
    Formally, this function conservatively estimates the remaining effective reserve balance after executing [candidateTx], assuming [preCandidateTxResBalances] is the estimate before [candidateTx]. This is done in a setting where the latest available state is [preIntermediatesState] and [intermediates] are all the transactions between [preIntermediatesState] and [candidateTx].

    Only the current sender’s entry changes; all other entries are unchanged.

    In the defn of [newBal] (let binding), the subtraction is capped below at 0: the result is a natural number ([N]).
    So, if if [sbal < maxTxFee next + value next] but  [maxTxFee next <= sbal], this transaction ([next]) will be accepted but all
    subsequent ones from the same sender will be rejected as the remaining effective reserve balance becomes 0.

TODO: move updateKey preTxResBalances addr to the top
 *)

(* TODO: rename to shallowExecTx *)
Open Scope Z_scope.
Notation asbool := bool_decide.

Definition delegatedAfterTx prevDelegated (tx: TxWithHdr) (addr: EvmAddr) : bool :=
      (prevDelegated && asbool (addr ∉ undels tx.1.2))
      || asbool (addr ∈ dels tx.1.2).

Definition shallowExecTx (preRes: ShallowExecResults) (candTx: TxWithHdr)
  : ShallowExecResults := fun addr =>
  let prev := preRes addr in
  let maxTxFee := maxTxFee candTx in
  let newCrb :=
    if bool_decide (sender candTx <> addr)
    then configuredRB prev
    else
      match reserveBalUpdateOfTx candTx with
      | Some newRb => newRb
      | None => configuredRB prev
      end in
  let newDelegated := delegatedAfterTx (delegated prev) candTx addr
 in
 let isNotSender := asbool (sender candTx <> addr) in
 let startingRb := balanceLb prev `min` newCrb in
  {|
    balanceLb :=
      if newDelegated
      then (if isNotSender then startingRb else startingRb - maxTxFee)
             
      else
        if isNotSender
        then balanceLb prev
        else balanceLb prev - maxTxFee - value candTx; 
    configuredRB := newCrb ;
    feeSolvent := feeSolvent prev && asbool (maxTxFee <= balanceLb prev);
    (* feeSolvent <> balanceLb >=0 *)
    delegated := newDelegated; 
  |}.

(*
Alice 100MON, undelegated
Alice, value 100, fee 1
 *)

Fixpoint shallowExecTxL (preRestResBalances: ShallowExecResults) (rest: list TxWithHdr)
  : ShallowExecResults:=
  match rest with
  | [] => preRestResBalances
  | hrest::tlrest =>
      let remainingReserves :=
        shallowExecTx preRestResBalances hrest in
      shallowExecTxL remainingReserves tlrest
  end.

(** ** Algorithm 1 (consensus): acceptability of a suffix

    A suffix is **consensus-acceptable** if, after pessimistically removing the
    head-then-tail debits, *every sender that appears later still has a
    non-negative effective reserve*.  This is exactly the safety condition
    proposers maintain as they build blocks up to [K] ahead.

    When evaluating a new tx at block number N to add at the end of [postStateSuffix],
    [latestState] must be the state after N-K block when proposing a new block.
    However, when the next pending (already proposed) block is executed, we need to derive that the remaining already proposed transactions are still valid on top of the more recent state: this is what the main soundness lemma [fullBlockStep] proves, in addition to proving that [postStateSuffix] will execute without running out of fees to pay. *)
Definition consensusAcceptableTxs (latestState : AugmentedState) (proposedTxs: list TxWithHdr) : Prop :=
  forall addr,
    addr ∈ map sender proposedTxs
    -> feeSolvent
         (shallowExecTxL
            (initialShallowExecResults latestState) proposedTxs addr) = true.

(** * Execution Check (algo 2)

 The execution logic is also tweaked to ensure that a transaction cannot dip too much into reserves so as to not have enough fees for a transaction already included by consensus. First, some helpers for that.


[isAllowedToEmptyExec] is a trivial wrapper used in execution, where there are intermediate transactions between the current transaction and the last known fully executed state.
 *)

Definition senderDelegatedAfterTx s tx :=
  delegatedAfterTx (addrDelegated s (sender tx)) tx (sender tx).

(* TODO: inline *)
Definition isAllowedToEmptyExec
  (s : AugmentedState)  (t: TxWithHdr) : bool :=
  negb (senderDelegatedAfterTx s.1 t).



(** [updateExtraState] is the execution-time maintenance of the tiny history we
    need for emptiness checks and reserve-config changes.  It is deliberately
    side-effect-free except for the fields it touches. *)

Definition updateExtraState (a: ExtraAcStates) (tx: TxWithHdr) : ExtraAcStates :=
  (fun addr =>
     let oldes := a addr in
       {|
         lastTxInBlockIndex :=
           if bool_decide (sender tx = addr)
           then Some (txBlockNum tx)
           else lastTxInBlockIndex oldes;
         lastDelUndelInBlockIndex :=
           if bool_decide (addr ∈ addrsDelUndelByTx tx)
           then Some (txBlockNum tx)
           else lastDelUndelInBlockIndex oldes;
         configuredReserveBal:=
           if bool_decide (sender tx = addr)
           then
             match reserveBalUpdateOfTx tx with
             | Some newRb => newRb
             | None => configuredReserveBal oldes
             end
           else configuredReserveBal oldes
       |}
    ).


Hint Rewrite @balanceOfUpd: syntactic.
Open Scope N_scope.

(** ** Abstract execution and revert

    We postulate a single-step EVM core ([evmExecTxCore]) that returns the new
    state and the set of changed accounts; and the revert step for failed checks.
    This keeps the reserve logic orthogonal to the (much larger) EVM semantics. *)

Axiom evmExecTxCore : StateOfAccounts -> TxWithHdr -> StateOfAccounts * (list EvmAddr) (* the list contains all the changed accounts *).
Axiom revertTx : StateOfAccounts -> TxWithHdr -> StateOfAccounts.


(** ** Algorithm 2 (execution): execute a transaction

    This assumes that [t] has already been validated to ensure that the sender has
    enough balance to cover [maxTxFee].

    Execution proceeds as follows:

    - Special “reserve update” tx: pay fee; set new configured reserve.
    - Otherwise, run the core EVM step to obtain the *actual* post state.
    - For *changed* accounts, enforce reserve discipline:
        - Non-sender: their *previous* protected slice must still fit in the
          *current* balance (unless they have code, deployed in this tx or before). if the account does have code, the address was generated by a keccak, so the proof assumes that nobody has the corresponding private key and thus the address can never send a transaction, thus this step can empty the balance.
        - Sender: either allowed to empty, or must retain at least
          [min(R, balance_before) − maxTxFee].
    - If any check fails, revert the tx *and still* update the extra history
      (so K-window bookkeeping remains accurate). *)

Definition execValidatedTx  (s: AugmentedState) (t: TxWithHdr)
  : AugmentedState :=
  match reserveBalUpdateOfTx t with
  | Some n => (updateBalanceOfAc s.1  (sender t) (fun b => b - maxTxFee t)
                 , updateExtraState s.2 t)
  | None =>

     let (si, changedAccounts) := evmExecTxCore (fst s) t in
     let balCheck (a: EvmAddr) :=
       let ReserveBal := configuredReserveBalOfAddr s.2 a in
       let erb:N := ReserveBal `min` (balanceOfAcA s a) in
       if hasCode si a (* important that si is not s, making it more liberal: allow just deployed contracts to empty *)
       then true
       else
         if bool_decide (sender t =a)
         (* TODO: figure out what breaks if [isAllowedToEmptyExec] is changed to addrDelegated s (sender t) || (sender t) ∈ dels t *)
         then if isAllowedToEmptyExec s t
              then true
              else bool_decide ((erb  - maxTxFee t) <= balanceOfAc si a)
         else bool_decide (erb <= balanceOfAc si a) in
     let allBalCheck : bool := (forallb balCheck changedAccounts) in (* in impl, only do for updates *)
     if (allBalCheck)
     then (si, updateExtraState s.2 t)
     else (revertTx s.1 t, updateExtraState s.2 t)
  end
.

(* accepted in new, not in old
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 1
tx2: alice, fee 6, value 1
 *)


(* old consensus accept, new reject
   old execution: unexpected revert possible,  
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 1
93 min 5=5
balanceLb := 93
tx2: alice, fee 2, value 92
balanceLb := 0
 *)


(* 
Alice: bal 100, reserve 5, undelegated
tx1: alice, fee 6, value 1
93 min 5=5
balanceLb := 93
tx2: alice, fee 6, value 1
balanceLb := 0
 *)

(** Note that because the [hasCode] check is done on [si] (the result of running the EVM blackbox to execute [t]), not [s] (the pre-exec state), the following scenario is allowed.

   - Alice sends money to addr2 in some contract. Alice is EOA.
   - Alice sends tx foo to a smart contract address addr.
   - addr execution deploys code at addr2 and calls it, and the call empties addr2.
 *)


(** Basic pre-validation: proposers guaranteed fee solvency for senders of the
    head transaction; executors re-check that cheaply before doing real work.
    The implementation checks nonces as well, but here we are only concerned with tx fees.
 *)
Definition validateTx (preTxState: StateOfAccounts) (t: TxWithHdr): bool :=
   bool_decide (maxTxFee t  <= balanceOfAc preTxState (sender t))%N.


(** Top-level execution wrapper that fails fast when validation fails.
   [None] means the execution of the whole block containing [t] aborts, which is what the consensus/execution checks must guarantee to never happen. *)
Definition execTx (s: AugmentedState) (t: TxWithHdr): option (AugmentedState) :=
  if (negb (validateTx (fst s) t)) (* if this fails. the execution of the entire block aborts *)
  then None
  else Some (execValidatedTx  s t).

(** execute a list of transactions one by one. note that the execution of any tx returns [None] (balance insufficient to cover fees), the entire execution (of the whole list of txs) returns [None] *)
Fixpoint execTxs  (s: AugmentedState) (ts: list TxWithHdr): option AugmentedState :=
  match ts with
  | [] => Some s
  | t::tls =>
      match execTx s t with
      | Some si => execTxs si tls
      | None => None
      end
  end.

(** * Main correctness theorem *)
Open Scope Z_scope.
(** our correctness property only holds when the set of proposed transactions are within K.
  this helps capture that assumption *)
Fixpoint blockNumsInRange (ltx: list TxWithHdr) : Prop :=
  match ltx with
  | [] => True
  | htx::ttx =>
      (forall txext, txext ∈ ttx ->  txBlockNum txext - K ≤ txBlockNum htx ≤ txBlockNum txext)
      /\ blockNumsInRange ttx
  end.

Definition txCannotCreateContractAtAddrs tx (eoasWithPrivateKey: list EvmAddr) :=
  forall s, let sf := (execValidatedTx  s tx) in
            forall addr,  addr ∈ eoasWithPrivateKey -> hasCode s.1 addr = false -> hasCode sf.1 addr = false.

(** The lemma below is probably what one would come up first as the main correctness theorem.
[blocks] represents the transactions in the blocks proposed after [latestState].
It says that consensus checks ([consensusAcceptableTxs latestState blocks]) implies
that the execution of all transactions [blocks] one by one, starting from the state [latestState] will succeed and not abort ([None]) due to preTx balance being less than [maxTxFee].

*)
Theorem fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender blocks) -> hasCode latestState.1 ac = false)
  -> (forall txext, txext ∈ blocks ->  txCannotCreateContractAtAddrs txext (map sender blocks))
  -> blockNumsInRange blocks
  -> consensusAcceptableTxs latestState blocks
  -> match execTxs latestState blocks with
     | None =>  False
     | Some si => True
     end. Abort.

(** ** main correctness theorem
We will prove the above correctness theorem below, but the actual correctness theorem we need is slightly different.
Suppose we split [blocks] in the theorem above into [firstblock] and [restblocks] such that [blocks=firstblocks++blocksrest] and suppose these blocks together are all transactions from the K proposed blocks since the last consensed state. Now, consenus will wait for execution to catch up and compute the state after [firstblock], say [latestState'].
After that, consensus should check the next block after [blocksrest] w.r.t [latestState'].
At that time, it needs to know that [blocksrest] is already valid w.r.t [latestState'], i.e. [consensusAcceptableTxs latestState' blocksrest].  This is precisely what the main theorem, shown next does:
*)
Theorem fullBlockStep  (latestState : AugmentedState) (firstblock: list TxWithHdr) (restblocks: list TxWithHdr) :
  blockNumsInRange (firstblock++restblocks)
  -> consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) -> txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> hasCode latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
        (** ^ execution cannot abort (indicated by returning None) due to balance being insufficient to even pay fees *)
     | Some si =>
        (** in this case, we have enough conditions to guarantee fee-solvency of block2, so that it can be extended and then this lemma reapplied *)
         consensusAcceptableTxs si restblocks
         /\ blockNumsInRange restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> hasCode si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof. Abort.

(** * Proof *)
Open Scope N_scope.
(** ** core execution assumptions
To prove the theorem [fullBlockStep], we need to make some assumptions about how the core EVM execution updates balances and delegated-ness. The names of these axioms are fairly descriptive.

 *)

Axiom balanceOfRevertSender: forall s tx,
  maxTxFee tx <= balanceOfAc s (sender tx)
  -> reserveBalUpdateOfTx tx = None
  -> balanceOfAc (revertTx s tx) (sender tx)
     = balanceOfAc s (sender tx) - maxTxFee tx.

Axiom balanceOfRevertOther: forall s tx ac,
  reserveBalUpdateOfTx tx = None
  -> ac <> (sender tx)
  -> balanceOfAc (revertTx s tx) ac
     = balanceOfAc s ac.


Axiom revertTxDelegationUpdCore: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTx s tx) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && bool_decide (ac ∉ (undels tx.1.2)))
                || bool_decide (ac ∈ (dels tx.1.2))).

Axiom execTxDelegationUpdCore: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && bool_decide (ac ∉ (undels tx.1.2)))
                || bool_decide (ac ∈ (dels tx.1.2))).


Axiom execTxSenderBalCore: forall tx s,
  maxTxFee tx <= balanceOfAc s (sender tx) ->
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  senderDelegatedAfterTx s tx = false
   ->  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - (maxTxFee tx).


(** One caveat in the assumption below is that it assumes that the account [ac] does not receive so much credit that it overflows 2^256. In practice, this should never happen, assuming the ETH supply is well below 2^256. Thus, we can assume that [evmExecTxCore] caps the balance at [2^256] should it overflow, instead of wrapping around, which may violate this assumption. *)
Axiom execTxCannotDebitNonDelegatedNonContractAccountsCore: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  forall ac, ac <> sender tx
              -> (addrDelegated sf ac || hasCode sf ac) = false
                 ->  balanceOfAc s ac <= balanceOfAc sf ac.


Axiom changedAccountSetSound: forall tx s,
  reserveBalUpdateOfTx tx = None ->
  let (sf, changedAccounts) :=  (evmExecTxCore s tx) in
  (forall ac, ac ∉ changedAccounts -> sf ac = s ac).


(** ** lemmas about execution
Unless there is a comment before a lemma, the lemma follows easily from  the axioms above about [evmExecTxCore] and [revertTx] and by the definition of [execTx]
 *)

Lemma addrDelegatedUnchangedByBalUpd s  f addr baladdr:
  addrDelegated (updateBalanceOfAc s baladdr f) addr = addrDelegated s addr.
Proof.
  unfold addrDelegated.
  simpl.
  Transparent updateBalanceOfAc.
  unfold updateBalanceOfAc.
  symmetry.
  unfold updateKey.
  case_bool_decide; subst; auto.
  simpl.
  destruct (s baladdr); simpl.
  reflexivity.
Qed.


    

Lemma execTxDelegationUpdCoreImpl tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || bool_decide (ac ∈ (addrsDelUndelByTx tx))).
Proof.
  simpl.
  intros ? ?.
  rewrite execTxDelegationUpdCore; auto.
  repeat rewrite Is_true_true.
  intros Hp.
  autorewrite with iff in Hp.
  destruct Hp; forward_reason; rwHyps; auto;[].
  unfold addrsDelUndelByTx.
  simpl.
  resdec ltac:(set_solver).
  autorewrite with syntactic.
  reflexivity.
Qed.

Lemma revertTxDelegationUpdCoreImpl tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTx s tx) in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || bool_decide (ac ∈ (addrsDelUndelByTx tx))).
Proof.
  simpl.
  intros ? ?.
  rewrite revertTxDelegationUpdCore;auto.
  repeat rewrite Is_true_true.
  intros Hp.
  autorewrite with iff in Hp.
  destruct Hp; forward_reason; rwHyps; auto;[].
  unfold addrsDelUndelByTx.
  simpl.
  resdec ltac:(set_solver).
  autorewrite with syntactic.
  reflexivity.
Qed.

Lemma balanceOfUpd s ac f acp:
  balanceOfAc (updateBalanceOfAc s ac f) acp = if (bool_decide (ac=acp)) then f (balanceOfAc s ac) else (balanceOfAc s acp).
Proof.
  unfold updateBalanceOfAc, updateKey, balanceOfAc. simpl.
  case_bool_decide; simpl; subst; auto; resdec ltac:(congruence);[].
  destruct (s ac); auto.
Qed.

Lemma execTxOtherBalanceLB tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf :=  (execValidatedTx s tx) in
  (forall ac,
      let ReserveBal := configuredReserveBalOfAddr s.2 ac in
      (ac <> sender tx)
       -> if (hasCode sf.1 ac)
          then True
          else ReserveBal `min` (balanceOfAcA s ac) <= (balanceOfAcA sf ac)).
Proof using.
  intros.
  subst ReserveBal.
  unfold execValidatedTx in *.
  simpl in *.

  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{  subst sf. unfold balanceOfAcA.  simpl.
       rewrite balanceOfUpd. case_match; auto. try lia.
       case_bool_decide; try lia.
  }
  pose proof (changedAccountSetSound tx s.1 ltac:(auto)) as Hsnd.
  rdestruct (evmExecTxCore s.1 tx) as [si changed].
  remember (hasCode sf.1 ac) as sac.
  destruct sac; auto.
  rememberForallb.
  unfold balanceOfAcA in *.
  destruct fb; simpl in *.
  2:{ subst sf.
      rewrite balanceOfRevertOther; auto;[].
      resolveDecide congruence.
      lia.
  }
  symmetry in Heqfb.
  rewrite  forallb_spec in Heqfb.
  destruct (decide (ac ∈ changed)).
  {
    specialize (Heqfb ac ltac:(auto)).
    rewrite <- Heqsac in Heqfb.
    resolveDecide congruence.
    case_bool_decide; try lia.
  }
  {
    unfold balanceOfAc.
    rewrite Hsnd; auto. lia.
  }

Qed.

Lemma execTxSenderBal tx s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let ReserveBal := configuredReserveBalOfAddr s.2 (sender tx) in
  let sf :=  (execValidatedTx s tx) in
  hasCode sf.1 (sender tx) = false->
  (if isAllowedToEmptyExec s tx
   then balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
  else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx))).
Proof.
  intros ? ? ? Hsc.
  subst ReserveBal.
  pose proof (execTxSenderBalCore tx s.1) as Hc.
  simpl in Hc.
  subst sf.
  revert Hsc.
  unfold execValidatedTx.
  remember ((reserveBalUpdateOfTx tx)) as rb.
  destruct rb; simpl in *.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite balanceOfUpd.
       resolveDecide congruence.
       case_match_concl; auto; try lia.
  }
  specialize (Hc ltac:(auto)).
  pose proof (changedAccountSetSound tx s.1 ltac:(auto)) as Hsnd.
  rdestruct (evmExecTxCore s.1 tx) as [si changed].
  unfold isAllowedToEmptyExec, delegatedAfterTx.
  intros.
  unfold balanceOfAcA in *.
  destruct (senderDelegatedAfterTx s.1 tx); simpl in *.
  {
    rememberForallb.
    unfold balanceOfAcA in *.
    destruct fb; try lia.
    2:{
      simpl in *. rewrite balanceOfRevertSender; auto.
      resolveDecide congruence. lia.
    }
    symmetry in Heqfb.
    rewrite  forallb_spec in Heqfb.
    rwHyps.
    destruct (decide (sender tx ∈ changed));
      [| unfold balanceOfAc; simpl; rewrite Hsnd;try sauto].
    specialize (Heqfb (sender tx) ltac:(auto)).
    resolveDecide congruence.
    simpl in *.
    rewrite -> Hsc in Heqfb.
    case_bool_decide; try lia.
  }
  {
    autorewrite with syntactic in *.
    rememberForallb.
    forward_reason.
    destruct fb; destruct Hc; simpl in *; orient_rwHyps; simpl in *;
      repeat (rewrite balanceOfRevertSender;sauto);
        try resolveDecide congruence; try auto;
      try lia.
  }
Qed.

Lemma isEmptyImpl {T} (t:list T) :
  isEmpty t = true -> t=[].
Proof using.
  unfold isEmpty.
  destruct t; sauto.
Qed.
  
Lemma execTxDelegationUpd tx s:
  let sf :=  (execValidatedTx s tx) in
  (forall ac, addrDelegated (fst sf) ac  -> addrDelegated (fst s) ac || bool_decide (ac ∈ (addrsDelUndelByTx tx))).
Proof.
  intros ? ? Hd.
  subst sf.
  unfold execValidatedTx in Hd.
  simpl in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite addrDelegatedUnchangedByBalUpd in Hd.
       auto.
  }
  rewrite pairEta in Hd.
  case_match.
  {
    apply execTxDelegationUpdCoreImpl in Hd; auto.
  }
  {
    apply revertTxDelegationUpdCoreImpl in Hd; auto.
  }
Qed.

Hint Rewrite @app_nil : iff.
Lemma execTxDelegationUpdDerived: forall tx s,
  let sf :=  (execValidatedTx s tx).1 in
  forall ac, addrDelegated sf ac  =
                delegatedAfterTx (addrDelegated s.1 ac) tx ac.
Proof using.
  intros ? ? ? ?.
  subst sf.
  unfold execValidatedTx, delegatedAfterTx.
  simpl in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *; try congruence.
  1:{  unfold balanceOfAcA. simpl in *.  intros.
       repeat rewrite addrDelegatedUnchangedByBalUpd.
       unfold reserveBalUpdateOfTx in Heqrb.
       unfold reserveBalUpdate in Heqrb.
       case_match; try 
                     congruence.
       applyToSomeHyp @isEmptyImpl.
       autorewrite with iff in *.
       sauto.
  }
  rewrite pairEta. simpl.
  case_match.
  {
    rewrite execTxDelegationUpdCore; auto.
  }
  {
    rewrite revertTxDelegationUpdCore; auto.
  }
Qed.

Lemma execTxCannotDebitNonDelegatedNonContractAccounts tx s:
  let sf :=  (execValidatedTx s tx) in
  (forall ac, ac <> sender tx
              -> if (addrDelegated (fst sf) ac || hasCode (fst sf) ac)
                 then True
                 else balanceOfAcA s ac <= balanceOfAcA sf ac).
Proof using.
  intros. subst sf.
  pose proof (fun p => execTxCannotDebitNonDelegatedNonContractAccountsCore tx s.1 p ac ltac:(auto)) as Htx.
  unfold execValidatedTx.
  simpl in *.
  case_match_concl;  auto;[].
  unfold balanceOfAcA in *.
  remember (reserveBalUpdateOfTx tx) as rb.
  destruct rb; simpl in *.
  1:{  simpl in *.
       rewrite balanceOfUpd.
       case_bool_decide; try lia.
  }
  specialize (Htx ltac:(auto)).
  rewrite pairEta.
  rewrite pairEta in Heqb. simpl in *.
  case_match_concl; simpl in *; try lia.
  {
    rewrite Heqb in Htx.
    lia.
  }
  {
    rewrite balanceOfRevertOther;auto.
  }
Qed.

(** This lemma combines many of the execution lemmas above to build a
    lower bound of the balance of any account after executing a transaction.
*)
Lemma execBalLb ac s tx:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  let sf :=  (execValidatedTx s tx) in
  let ReserveBal := configuredReserveBalOfAddr s.2 ac in
  if (bool_decide (ac=sender tx)) then
    hasCode sf.1 (sender tx) = false->
    (if isAllowedToEmptyExec s tx
     then balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx)
          \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
     else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx)))
  else
    if (hasCode sf.1 ac)
    then True
    else (if addrDelegated (fst sf) ac then ReserveBal `min` (balanceOfAcA s ac) else balanceOfAcA s ac)
         <= (balanceOfAcA sf ac).
Proof using.
  simpl. intros.
  case_bool_decide; subst; auto; [apply execTxSenderBal; auto|].
  pose proof (execTxOtherBalanceLB tx s ltac:(auto) ac ltac:(auto)).
  pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s ac ltac:(auto)).
  destruct (hasCode (execValidatedTx s tx).1 ac); auto;[].
  autorewrite with syntactic in *.
  case_match; lia.
Qed.

Lemma execS2 s txlast:
  ((execValidatedTx s txlast)).2 = updateExtraState s.2 txlast.
Proof using.
  unfold execValidatedTx.
  repeat (case_match; try reflexivity).
Qed.


Lemma lastTxInBlockIndexUpd s txlast:
  lastTxInBlockIndex ((((execValidatedTx s txlast)).2) (sender txlast))
  = Some (txBlockNum txlast).
Proof using.
  rewrite execS2.
  unfold updateExtraState.
  simpl.
  resdec congruence.
Qed.

Lemma otherTxLstSenderLkp s addr txlast :
  addr <> sender txlast
  ->
    lastTxInBlockIndex ((((execValidatedTx s txlast)).2) addr)
    = lastTxInBlockIndex (s.2 addr).
Proof.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  resdec congruence.
Qed.


Lemma delgUndelgUpdTx txlast s addr:
  addr ∈  addrsDelUndelByTx txlast
  -> lastDelUndelInBlockIndex (((execValidatedTx s txlast)).2  addr) = Some (txBlockNum txlast).
Proof using.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  resdec congruence.
Qed.

Lemma otherDelUndelLkp s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    lastDelUndelInBlockIndex (((execValidatedTx s txlast)).2 addr)
    = lastDelUndelInBlockIndex (s.2  addr).
Proof.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  resdec congruence.
Qed.

Lemma otherDelUndelDelegationStatusUnchanged s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    addrDelegated ((execValidatedTx s txlast)).1 addr
    = addrDelegated s.1 addr.
Proof.
  intros Hn.
  unfold execValidatedTx.
  case_match; auto.
  {
    simpl.
    rewrite addrDelegatedUnchangedByBalUpd. reflexivity.
  }
  rewrite pairEta. simpl in *.
  case_match;
    simpl in *.
  2:{
    rewrite revertTxDelegationUpdCore;auto;[].
    unfold addrsDelUndelByTx in *.
    (*
    resdec ltac:(set_solver). *)
    rewrite bool_decide_true;[| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
  {
    pose proof (execTxDelegationUpdCore txlast s.1 ltac:(auto )addr) as Hd.
    revert Hd. rwHyps.
    simpl.
    intros.
    rewrite Hd.
    clear Hd. revert Hn. clear.
    unfold addrsDelUndelByTx in *.
    intros.
    rewrite bool_decide_true; [| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
Qed.

Set Nested Proofs Allowed.


Definition rbAfterTx s tx :=
  match reserveBalUpdateOfTx tx with
  | Some rb => rb
  | None => configuredReserveBalOfAddr s (sender tx)
  end.


Lemma configuredReserveBalOfAddrSpec s tx a:
  configuredReserveBalOfAddr (execValidatedTx s tx).2 a
  = if bool_decide (a=sender tx)
    then rbAfterTx s.2 tx
    else configuredReserveBalOfAddr s.2 a.
Proof.
  unfold configuredReserveBalOfAddr.
  rewrite execS2.
  unfold updateExtraState.
  simpl. intros.
  unfold rbAfterTx.
  resdec solver.
  case_bool_decide;  resdec congruence; subst; auto.
Qed.

Lemma configuredReserveBalOfAddrSame s tx  a:
  sender tx <> a
  -> (configuredReserveBalOfAddr (execValidatedTx s tx).2 a
      =
        configuredReserveBalOfAddr s.2 a).
Proof using.
  intros Hn.
  rewrite configuredReserveBalOfAddrSpec.
  case_bool_decide; try congruence.
Qed.

Lemma hasCodeFalsePresExec l s tx:
  (forall txext, txext ∈ (tx::l) ->  txCannotCreateContractAtAddrs txext (map sender (tx::l)))
  -> (forall ac, ac ∈ (map sender (tx::l)) -> hasCode s.1 ac = false)
  -> (forall ac, ac ∈ (map sender (tx::l)) -> hasCode (execValidatedTx s tx).1 ac = false).
Proof using.
  intros Heoac Hsc.
  intros.
  pose proof (Hsc ac ltac:(set_solver)).
  specialize (Heoac tx ltac:(set_solver) s ac ltac:(set_solver) ltac:(assumption)).
  auto.
Qed.


Open Scope Z_scope.

(** **  [isAllowedToEmpty] lemmas

  Recall [isAllowedToEmpty s (txInterfirst :: rest) txnext]
  determines whether the transaction [txnext] is allowed to empty its balance,
  in the setting where [s] is the last available state and
  [(txInterfirst :: rest)] are the transactions between [s] and [txnext].

  This lemma proves that to be equivalen to executing [txInterfirst]
  at state [s] and considering the result as the latest available state
  and thereby removing [txInterfirst] from intermediates.

*)

Hint Rewrite @updateKeyLkp3 : syntactic.

Definition sresLe (rb1 rb2: ShallowExecRes) :=
  delegated rb1 = delegated rb2
  /\ balanceLb rb1 <= balanceLb rb2
  /\ configuredRB rb1 = configuredRB rb2
  /\ (feeSolvent rb1 = true -> feeSolvent rb2 = true).

Notation "l '`resLe`' r" := (sresLe l r) (at level 50).

Definition rbLe (eoas: list EvmAddr) (rb1 rb2: ShallowExecResults) :=
  forall addr, addr ∈ eoas -> (rb1 addr) `resLe` (rb2 addr).

(** ** lemmas about [shallowExecTx]

    The next pair of lemma states that the “remaining effective reserve”
    function is monotone: if you start from a pointwise larger map, you end at a
    pointwise larger map. [rbLe] is defined right above.

 *)

Lemma rbLeImpl a b :
  a `resLe` b ->
   feeSolvent a = true
   -> feeSolvent b = true.
Proof.
  intros Hr.
  hnf in Hr.
  tauto.
Qed.


Lemma mono eoas rb1 rb2 tx:
  rbLe eoas rb1 rb2
  -> rbLe eoas (shallowExecTx rb1 tx)
       (shallowExecTx rb2 tx).
Proof using.
  intros Hrb addr Hin.
  unfold shallowExecTx.
  pose proof (Hrb addr Hin) as Hrba.
  unfold sresLe in Hrba.
  forward_reason.
  unfold sresLe. simpl.
  autorewrite with iff in *.
  split_and !; try sauto;[].
  rwHyps.
  case_match_concl; case_bool_decide_concl; sauto.
Qed.



(** lifts [mono] from [shallowExecTx] to [shallowExecTxL]:
proof follows a straightforward induction on the list [extension],
using [mono] to fulfil the obligations of the induction hypothesis
 *)
Lemma monoL eoas rb1 rb2 extension:
  map sender extension ⊆ eoas
  -> rbLe eoas rb1 rb2
  -> rbLe eoas (shallowExecTxL rb1 extension)
          (shallowExecTxL rb2 extension).
Proof using.
  revert rb1 rb2.
  induction extension; auto;[].
  unfold rbLe in *.
  intros ? ?  Hs Hrb addr Hin. simpl in *.
  simpl.
  apply IHextension;[set_solver | | set_solver].
  apply mono.
  assumption.
Qed.


Hint Rewrite configuredReserveBalOfAddrSpec addrDelegatedUnchangedByBalUpd: syntactic.

(** This lemma captures a key property of [shallowExecTx]: it underapproximates
the resultant effective balance after execution of the transaction
*)
Lemma exec1 tx extension s :
  maxTxFee tx <= balanceOfAc s.1 (sender tx)
  -> let sf := (execValidatedTx s tx) in
     (∀ ac : EvmAddr, ac ∈ sender tx :: map sender extension → hasCode sf.1 ac = false)
     -> ∀ addr : EvmAddr,
         addr ∈ sender tx :: map sender extension
         -> (shallowExecTx (initialShallowExecResults s) tx addr)
              `resLe` (initialShallowExecResults sf addr).
Proof using.
  intros Hfee ? Hscf.
  intros ? Hin.
  unfold shallowExecTx.
  unfold initialShallowExecResults. unfold sresLe. simpl.
  split_and !; try sauto.
  { subst sf. simpl.
    rewrite execTxDelegationUpdDerived.
    reflexivity.
  }

  2:{
    rewrite configuredReserveBalOfAddrSpec.
    case_bool_decide; resdec congruence;[].
    subst. reflexivity.
  }

  (* core balanceLb goal *)
  pose proof (execBalLb addr s tx ltac:(lia)) as Hlb.
  rewrite execTxDelegationUpdDerived.
  simpl in Hlb. fold sf in Hlb.
  unfold isAllowedToEmptyExec, senderDelegatedAfterTx in Hlb.
  repeat rewrite execTxDelegationUpdDerived in Hlb.
  rewrite Hscf in Hlb;[|set_solver].
  rewrite Hscf in Hlb;[|set_solver].
  unfold balanceOfAcA in *.
  rewrite configuredReserveBalOfAddrSpec.
  autorewrite with syntactic.
  case_match_concl.
  { (*  delegatedAfterTx (addrDelegated s.1 addr) tx addr = true *)
    case_bool_decide_concl; resdec congruence; try lia.
    { (* addr <> sendr *)
      case_match; try lia.
    }
    {
      forward_reason.
      subst.
      rewrite Heqb in Hlb.
      simpl in *.
      unfold rbAfterTx.
      case_match_concl; try lia;[].
      (* addrDelegated s.1 (sender tx) = false *)
      assert (reserveBalUpdateOfTx tx = None) as Hn.
      {
        unfold reserveBalUpdateOfTx.
        unfold reserveBalUpdate.
        unfold delegatedAfterTx in *.
        simpl in *.
        autorewrite with iff in *.
        case_match; auto.
        applyToSomeHyp @isEmptyImpl.
        autorewrite with iff in *.
        forward_reason.
        rewrite autogenhypl in Heqb.
        set_solver.
      }
      rewrite Hn.
      lia.
    }

  }
  { (* delegatedAfterTx (addrDelegated s.1 addr) tx addr = false *)
    case_bool_decide_concl; resdec congruence; try lia.
    { case_match; try sauto. }
    subst. rewrite  Heqb in Hlb.
    simpl in *.
    forward_reason.
    case_match; lia.
  }
Qed.


(** you can pick the first tx in the proposed extension and the consensus checks would
    still hold on the resultant state for the remaining transactions in the proposal.
*)
Lemma execPreservesConsensusChecks tx extension s:
  maxTxFee tx <= balanceOfAc s.1 (sender tx) ->
  (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> hasCode s.1 ac = false)
  -> consensusAcceptableTxs s (tx::extension)
  -> consensusAcceptableTxs (execValidatedTx s tx) extension.
Proof using.
  intros Hfee Heoac Hsc.
  pose proof (hasCodeFalsePresExec _ _ _ Heoac Hsc) as Hscf.
  clear Heoac.
  set (sf:=(execValidatedTx s tx).1).
  intros Hc.
  simpl in *.
  intros ac Hin.
  specialize (Hc ac).
  forward_reason.
  simpl in *.
  specialize (Hc ltac:(set_solver)).
  revert Hc.
  apply rbLeImpl.
  pose proof (monoL (map sender (tx::extension))) as Hm.
  unfold rbLe in Hm.
  apply Hm; auto; simpl in *; auto; [ set_solver | | set_solver].
  intros.
  clear Hm.
  apply exec1 with (extension := extension); auto.
Qed.

(** TODO: fix name *)
Lemma decreasingRemTxSender irb txc addr:
  feeSolvent (shallowExecTx irb txc addr) = true
  -> feeSolvent (irb addr) = true.
Proof using.
  simpl.
  intros Hp.
  autorewrite with iff in Hp.
  tauto.
Qed.

(** lifts the previous lemma from [shallowExecTx] to [shallowExecTx]. induction on [nextL] *)
Lemma decreasingRemL irb  (nextL: list TxWithHdr) addr:
  feeSolvent (shallowExecTxL irb nextL addr) = true
  -> feeSolvent (irb addr) = true.
Proof using.
  revert  irb.
  induction nextL; simpl; [ auto; fail|].
  intros.
  pose proof (IHnextL (shallowExecTx irb a)).
  forward_reason.
  eapply decreasingRemTxSender; eauto.
Qed.

(** Finally, here is one of the key stepping stones to the main theorem, it says that
    the consensus checks guarantee that execution of the first transaction
    will pass validation during execution, i.e. the balance would be sufficient to cover
    [maxTxFee].

    This doesn't say anything about whether the execition of the later transactions ([extension]) will also pass the check. That is where the next lemma comes in handy.
 *)
Lemma execValidate tx extension s:
  consensusAcceptableTxs s (tx::extension)
  -> validateTx s.1 tx = true.
Proof using.
  intros Hc.
  unfold consensusAcceptableTxs in *.
  specialize (Hc (sender tx)).
  simpl in *.
  specialize (Hc ltac:(set_solver)).
  (*
  autorewrite with syntactic in Hc.
  rewrite updateKeyLkp3 in Hc.
  resolveDecide ltac:(congruence). *)
  unfold validateTx.
  autorewrite with iff.
  apply decreasingRemL in Hc.
  simpl in Hc.
  autorewrite with iff in Hc.
  case_match; try lia.
Qed.



(** the above 2 lemmas can be combined to yield the following: *)
Lemma inductiveStep  (latestState : AugmentedState) (tx: TxWithHdr) (extension: list TxWithHdr) :
  maxTxFee tx <= balanceOfAc latestState.1 (sender tx)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtAddrs txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> hasCode latestState.1 ac = false)
 ->  consensusAcceptableTxs latestState (tx::extension)
  -> match execTx latestState tx with
     | None =>  False
     | Some si =>
         consensusAcceptableTxs si extension
     end.
Proof.
  intros Hext Heoac Hsc Hc.
  unfold execTx.
  intros.
  rewrite -> (execValidate tx extension) by assumption.
  simpl.
  apply execPreservesConsensusChecks in Hc; auto.
Qed.

Set Printing Coercions.

Fixpoint blockNumsInRange2 (ltx: list TxWithHdr) : Prop :=
  match ltx with
  | [] => True
  | htx::ttx =>
      (forall txext, txext ∈ ttx ->  txBlockNum txext ≤ txBlockNum htx + K  /\ txBlockNum htx ≤ txBlockNum txext)
      /\ blockNumsInRange2 ttx
  end.

Lemma bnequiv ltx: blockNumsInRange2 ltx -> blockNumsInRange ltx .
Proof using.
  induction ltx; auto;[].
  simpl.
  intros Hyp.
  forward_reason.
  split_and; auto.
  intros.
  pose proof (Hypl txext ltac:(assumption)).
  lia.
Qed.

Lemma bnequiv2 ltx: blockNumsInRange ltx -> blockNumsInRange2 ltx .
Proof using.
  induction ltx; auto;[].
  simpl.
  intros Hyp.
  forward_reason.
  split_and; auto.
  intros.
  pose proof (Hypl txext ltac:(assumption)).
  lia.
Qed.


Lemma  txCannotCreateContractAtAddrsMono tx l1 l2:
  l1 ⊆ l2
  -> txCannotCreateContractAtAddrs tx l2
  -> txCannotCreateContractAtAddrs tx l1.
Proof using.
  unfold txCannotCreateContractAtAddrs.
  intros Hs Hp.
  intros.
  apply Hp; auto.
Qed.

Lemma  txCannotCreateContractAtAddrsTrimHead tx h l:
  txCannotCreateContractAtAddrs tx (h::l)
  -> txCannotCreateContractAtAddrs tx l.
Proof using.
  apply txCannotCreateContractAtAddrsMono.
  set_solver.
Qed.

(** * Proof of main theorem:
    Straightforward induction on [firstblock],
    with [inductiveStep] used in the inductive step.
*)

Lemma fullBlockStep  (latestState : AugmentedState) (firstblock restblocks: list TxWithHdr) :
  blockNumsInRange (firstblock++restblocks)
  -> consensusAcceptableTxs latestState (firstblock++restblocks)
  -> (forall txext, txext ∈ (firstblock++restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (firstblock++restblocks)))
  -> (forall ac, ac ∈ (map sender (firstblock++restblocks)) -> hasCode latestState.1 ac = false)
  -> match execTxs latestState firstblock with
     | None =>  False
     | Some si =>
         (* enough conditions to guarantee fee-solvency of block2, so that it can be extended and then this lemma reapplied *)
         consensusAcceptableTxs si restblocks
         /\ blockNumsInRange restblocks
         /\ (forall ac, ac ∈ (map sender restblocks) -> hasCode si.1 ac = false)
         /\ (forall txext, txext ∈ (restblocks) ->  txCannotCreateContractAtAddrs txext (map sender (restblocks)))
     end.
Proof.
  intros Hrange Hacc.
  induction firstblock as [|hb1 firstblock IH] in latestState, Hrange, Hacc |- *; simpl in *; auto.
  intros Heoa Hsc.
  change  ((hb1 :: firstblock) ++ restblocks) with (hb1::(firstblock++restblocks)) in Hacc.
  forward_reason.
  pose proof (execValidate _ _ _ Hacc) as Hv.
  unfold validateTx in Hv.
  autorewrite with iff in Hv.
  eapply inductiveStep in Hacc;  auto;[| lia].
  unfold execTx in *.
  destruct (validateTx latestState.1 hb1); simpl in *; try contradiction;[].
  pose proof (hasCodeFalsePresExec _ _ _ Heoa Hsc) as Hsci.
  remember (execValidatedTx latestState hb1) as si.
  simpl in *.
  pose proof (fun txext p => txCannotCreateContractAtAddrsTrimHead _ _ _
                               (Heoa txext (elem_of_list_further _ _ _ p))).
  specialize (IH si ltac:(auto) ltac:(auto) ltac:(auto)).
  lapply IH; auto;[].
  intros.
  apply Hsci. set_solver.
Qed.

Print Assumptions fullBlockStep.
(** All assumptions of the proof:
[[

Section Variables:
K
: N
Axioms:
revertTxDelegationUpdCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := revertTx s tx) (ac : EvmAddr),
        addrDelegated sf ac =
        addrDelegated s ac && asbool (ac ∉ undels tx.1.2) || asbool (ac ∈ dels tx.1.2)
revertTx : StateOfAccounts → TxWithHdr → StateOfAccounts
execTxSenderBalCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    (maxTxFee tx ≤ balanceOfAc s (sender tx))%N
    → reserveBalUpdateOfTx tx = None
      → let sf := (evmExecTxCore s tx).1 in
        senderDelegatedAfterTx s tx = false
        → balanceOfAc sf (sender tx) = (balanceOfAc s (sender tx) - (maxTxFee tx + value tx))%N
          ∨ balanceOfAc sf (sender tx) = (balanceOfAc s (sender tx) - maxTxFee tx)%N
execTxDelegationUpdCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := (evmExecTxCore s tx).1) (ac : EvmAddr),
        addrDelegated sf ac =
        addrDelegated s ac && asbool (ac ∉ undels tx.1.2) || asbool (ac ∈ dels tx.1.2)
execTxCannotDebitNonDelegatedNonContractAccountsCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := (evmExecTxCore s tx).1) (ac : EvmAddr),
        ac ≠ sender tx
        → addrDelegated sf ac || hasCode sf ac = false
          → (balanceOfAc s ac ≤ balanceOfAc sf ac)%N
evmExecTxCore : StateOfAccounts → TxWithHdr → StateOfAccounts * list EvmAddr
changedAccountSetSound :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → let (sf, changedAccounts) := evmExecTxCore s tx in
      ∀ ac : EvmAddr, ac ∉ changedAccounts → sf ac = s ac
balanceOfRevertSender :
  ∀ (s : StateOfAccounts) (tx : TxWithHdr),
    (maxTxFee tx ≤ balanceOfAc s (sender tx))%N
    → reserveBalUpdateOfTx tx = None
      → balanceOfAc (revertTx s tx) (sender tx) = (balanceOfAc s (sender tx) - maxTxFee tx)%N
balanceOfRevertOther :
  ∀ (s : StateOfAccounts) (tx : TxWithHdr) (ac : EvmAddr),
    reserveBalUpdateOfTx tx = None
    → ac ≠ sender tx → balanceOfAc (revertTx s tx) ac = balanceOfAc s ac


]]
 *)


Corollary fullBlockStep2  (latestState : AugmentedState) (blocks: list TxWithHdr) :
  (forall ac, ac ∈ (map sender (blocks)) -> hasCode latestState.1 ac = false)
  -> (forall txext, txext ∈ (blocks) ->  txCannotCreateContractAtAddrs txext (map sender (blocks)))
  -> blockNumsInRange (blocks)
  -> consensusAcceptableTxs latestState (blocks)
  -> match execTxs latestState blocks with
     | None =>  False
     | Some si => True
     end.
Proof.
  intros.
  pose proof (fullBlockStep latestState blocks []) as Hf.
  autorewrite with syntactic in Hf.
  specialize (Hf ltac:(auto) ltac:(auto) ltac:(auto) ltac:(auto)).
  case_match; auto.
Qed.


Lemma acceptableNil lastConsensedState:
  consensusAcceptableTxs lastConsensedState [].
Proof using.
  unfold consensusAcceptableTxs.
  intros.
  simpl.
  reflexivity.
Qed.

(* Consensus Invariant and how its steps preserve the invariant
At any given time, consensus has some [latestConsensedState] and a list of transactions/blocks (say [ltx]) proposed on top of that.
The main invariant is that it maintains is [consensusAcceptableTxs latestConsensedState ltx].
There are also side conditions like [blockNumsInRange ltx] and that the transactions in [ltx] are not sent an address that has code: the latter is just a formal assumption in Coq but is guaranteed by cryptographic hardness of generating private keys.

This invariant needs to be preserve on the 2 mains steps of consensus:
- extend ltx with a new block of transactions.
- once execution catches up to the next block remove a prefix of ltx that corresponds to the block whose execution results are now available.

The lemma [fullBlockStep] is exactly what is needed to preserve the invariant at the latter step.
To preserve the invariant at the first step, the proposed new txs (e.g. grabbed from mempool) need to be checked so that they satisfy the [consensusAcceptableTxs] property.

 *)

(*
Below is an illustration of how the blockchain evolves starting from the genesis block b0.
It assumes an oracle nextBlockPicker that picks the next block while satisfying the conditions.

 *)

(* begin hide *)
Section consensusInvariantsAndPreservation.
  Variable b0: list TxWithHdr.
  Variable sb0 : AugmentedState. (* state after b0 *)
  Hypothesis b0range: blockNumsInRange b0.
  Definition cannotCreateCodeAtSenderAddrs ltx := ∀ txext : TxWithHdr,
   txext ∈ ltx
   → txCannotCreateContractAtAddrs txext (map sender ltx).
  Hypothesis b0csa: cannotCreateCodeAtSenderAddrs b0.

  Hypothesis nextBlockPicker:
    forall (lastConsensedState: AugmentedState) (proposedTxs: (list TxWithHdr)),
      consensusAcceptableTxs lastConsensedState proposedTxs
      -> blockNumsInRange proposedTxs
      -> cannotCreateCodeAtSenderAddrs proposedTxs
      -> (∀ ac : EvmAddr, ac ∈ map sender proposedTxs → hasCode lastConsensedState.1 ac = false)
      -> exists nextBlock,
          consensusAcceptableTxs lastConsensedState (proposedTxs++nextBlock)
          /\ blockNumsInRange (proposedTxs++nextBlock)
          /\ cannotCreateCodeAtSenderAddrs (proposedTxs++nextBlock)
          /\ (∀ ac : EvmAddr, ac ∈ map sender (proposedTxs++nextBlock) → hasCode lastConsensedState.1 ac = false).
  Open Scope N_scope.

  (** The statement below is of course unprovable. But the proof script below illustrates how the state of the consensus module evolves from the genesis block b0, showing how the 2 steps are taken and how they preserve the invaraints. At every time, the proof context (hypotheses) has the assertion that the invariants are satisified for the latest consensed block and the proposal so far. The proof script itself is not useful to see: the Coq goal at every step is illuminating.
   *)

  Lemma operation  : False.
    intros.
    revert nextBlockPicker.
    rwHyps.
    intros.
    (** now we invoke the oracle to pick the next block after b0 *)
    pose proof (nextBlockPicker sb0 []  (acceptableNil _) I ltac:(set_solver) ltac:(set_solver)) as b1.
    destruct b1 as [b1 b1ok].
    simpl in b1ok.
    forward_reason.
    (** now we invoke the oracle to pick the next block after b1 *)
    pose proof (nextBlockPicker sb0 b1 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b2.
    destruct b2 as [b2 b2ok].
    forward_reason.
    unfold cannotCreateCodeAtSenderAddrs in *.
    apply fullBlockStep in b2okl; auto.
    (** assuming K=2, we wait for execution to execute b1 and give us the new state sb1  *)
    destruct (execTxs sb0 b1) as [sb1 ?|]; auto.
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb1 rather than sb0 *)
    pose proof (nextBlockPicker sb1 b2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b3.
    destruct b3 as [b3 b3ok].
    forward_reason.
    apply fullBlockStep in b3okl; auto.
    (** we wait for execution to execute b2 and give us the new state sb2  *)
    destruct (execTxs sb1 b2) as [sb2 ?|]; auto;[].
    forward_reason.
    (** now we pick the new block b3, but with the latestConsensedState of sb2 rather than sb1 *)
    pose proof (nextBlockPicker sb2 ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption))  as b4.
 Abort.
End consensusInvariantsAndPreservation.
(* end hide *)
End K.

(* consensus: both new and old will accept
   execution: only old will unnecessarily revert tx4

Alice 100, undelegated, reservebal =5
tx1: sender Alice, delegates Alice, value 10, fee 1
tx2: Bob sends to Alice, Alice balance debited by 20.
tx3: sender Alice, undelegates Alice, value 0, fee 1
tx4: sender Alice, value 67, fee 1
*)


