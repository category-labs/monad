Require Import monad.EVMOpSem.block.
Require Import stdpp.gmap.
Require Import Lens.Elpi.Elpi.
Require Import Lens.Lens.
#[local] Open Scope lens_scope.


(* delete and inline? *)
Definition Transaction := transaction.

Record Indices :=
  {
    block_index: N;
    tx_index: N;
  }.

Record AccountM : Type :=
  {
    coreAc: block.block_account;
    incarnation: Indices; (* the blocknumber, tx number when this "incarnation" of the account was created. the EVM semantics does not really track this but we do to help reason about concurrent execution of transactions. This seems to be useful mainly in caching to avoid confusing different incarnations of the same address *)
    relevantKeys: list N; (* only the storage keys listed here are relevant. for assumptions, there are the only read keysk. for updates, these are the only updated keys. In C++, storage maps typically will have only these keys.
    must be [] if coreState is []*)
    lastDelegatedInBlockIndex : option Indices; (* last block/tx index where this address was delegated or some code was deployed at this address using CREATE(2): get back to the latter point *)
    lastTxInBlockIndex : option Indices (* last block/tx index where this address sent a tx *) 
  }.

Module evm.
  Definition log_entry: Type := EVMOpSem.evm.log_entry.
  Definition address: Type := EVMOpSem.evm.address.
  Definition account_state: Type (* TODO: investigate why Set doesnt work here *) := AccountM.

  #[global] Instance : EqDecision address. Proof. Admitted.
   #[global] Instance : Countable address. Proof. Admitted.
  
  Definition GlobalState := gmap address account_state. (* EVMOpSem defines it as a function type which can cause hassles for computation and for separation logic reasoning *)
End evm.
Notation StateOfAccounts := evm.GlobalState.

(* delete and inline? *)
Definition sender: Transaction -> evm.address:= tr_from.

Definition w256 := N.

Record BlockHeader :={
    base_fee_per_gas: option w256;
    number: N;
    beneficiary: evm.address;
    timestamp: N;
    }.
Record TransactionResult :=
  {
    gas_used: N;
    gas_refund: N;
    logs: list evm.log_entry;
    (* sender : evm.address *)
  }.

Definition stateAfterTransactionAux  (hdr: BlockHeader) (s: StateOfAccounts) (txindex: nat) (t: Transaction): StateOfAccounts * TransactionResult.
Admitted. (* To be provided by an appropriate EVM semantics *)

(* similar to what execute_final does *)
Definition applyGasRefundsAndRewards (hdr: BlockHeader) (s: StateOfAccounts) (t: TransactionResult): StateOfAccounts. Admitted.

(* txindex can be used to store incarnation numbers *)
Definition stateAfterTransaction (hdr: BlockHeader) (txindex: nat) (s: StateOfAccounts) (t: Transaction): StateOfAccounts * TransactionResult :=
  let (si, r) := stateAfterTransactionAux hdr s txindex t in
  (applyGasRefundsAndRewards hdr si r, r).

Fixpoint stateAfterTransactions' (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction) (start:nat) (prevResults: list TransactionResult): StateOfAccounts * list TransactionResult :=
  match ts with
  | [] => (s, prevResults)
  | t::tls => let (sf, r) := stateAfterTransaction hdr start s t in
              stateAfterTransactions' hdr sf tls (1+start) (prevResults++[r])
  end.
    
    
Definition stateAfterTransactions  (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction): StateOfAccounts * list TransactionResult := stateAfterTransactions' hdr s ts 0 [].


      Lemma stateAfterTransactionsC' (hdr: BlockHeader) (s: StateOfAccounts) (c: Transaction) (ts: list Transaction) (start:nat) (prevResults: list TransactionResult):
        stateAfterTransactions' hdr s (ts++[c]) start prevResults
        = let '(sf, prevs) := stateAfterTransactions' hdr s (ts) start prevResults in
          let '(sff, res) := stateAfterTransaction hdr (length ts+start) sf c in
          (sff, prevs ++ [res]).
      Proof using.
        revert s.
        revert start.
        revert prevResults.
        induction ts;[reflexivity|].
        intros. simpl.
        destruct (stateAfterTransaction hdr start s a).
        simpl.
        rewrite IHts.
        repeat f_equiv.
        rewrite <- Nat.add_succ_r.
        reflexivity.
      Qed.

      
      Lemma stateAfterTransactionsC (hdr: BlockHeader) (s: StateOfAccounts) (c: Transaction) (ts: list Transaction):
        stateAfterTransactions hdr s (ts++[c])
        = let '(sf, prevs) := stateAfterTransactions hdr s (ts) in
          let '(sff, res) := stateAfterTransaction hdr (length ts) sf c in
          (sff, prevs ++ [res]).
      Proof using.
        setoid_rewrite stateAfterTransactionsC'.
        repeat rewrite <- plus_n_O.
        reflexivity.
      Qed.

      Lemma  rect_len g l lt h bs : (g, l) = stateAfterTransactions h bs lt ->
                                    length l = length lt.
      Proof using. Admitted. (* easy *)
      
Record Withdrawal:=
  {
    recipient: evm.address;
    value_wei: N;
  }.

Record Block :=
  {
    transactions: list Transaction;
    header: BlockHeader;
    ommers: list BlockHeader;
    withdrawals: option (list Withdrawal);
  }.

Definition applyWithdrawals (s: StateOfAccounts) (ws: option (list Withdrawal)): StateOfAccounts.
Proof. Admitted.

Definition applyBlockReward (s: StateOfAccounts) (num_omsers: nat): StateOfAccounts.
Proof. Admitted.

Definition stateAfterBlock (b: Block) (s: StateOfAccounts): StateOfAccounts * list TransactionResult :=
  let '(s, tr) := stateAfterTransactions (header b) s (transactions b) in
  let s:= applyWithdrawals s (withdrawals b) in
  (applyBlockReward s (length (ommers b)), tr).

(* Coq model of the Chain type in C++ *)
Record Chain := {
    chainid: N
  }.
Inductive Revision := Shanghai | Frontier.

Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
Definition stateRoot (b: evm.GlobalState) : N. Proof. Admitted.
Definition receiptRoot (b: list TransactionResult) : N. Proof. Admitted.
Definition transactionsRoot (b: Block) : N. Proof. Admitted.
Definition withdrawalsRoot (b: Block) : N. Proof. Admitted.



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


Definition txMaxFee (t: Transaction) : N. Proof. Admitted.

Definition w256_to_Z (w: monad.EVMOpSem.keccak.w256) : Z :=
  monad.EVMOpSem.Zdigits.binary_value 256 w.

Definition w256_to_N (w: monad.EVMOpSem.keccak.w256) : N :=
  Z.to_N (w256_to_Z w).

Definition Z_to_w256 wnz : monad.EVMOpSem.keccak.w256 := Zdigits.Z_to_binary _ wnz.

Opaque Zdigits.binary_value Zdigits.Z_to_binary.

Definition zbvfun (fz: Z -> Z) (w: keccak.w256): keccak.w256:=
  let wnz := fz (w256_to_Z w) in
  Z_to_w256 wnz.

Import LensNotations.
Require Import bluerock.prelude.lens.

Opaque w256_to_Z.
Opaque Z_to_w256.
(* TODO: add other checks:

   uint512_t const v0 =
        tx.value + max_gas_cost(tx.gas_limit, tx.max_fee_per_gas);

    if (MONAD_UNLIKELY(!sender_account.has_value())) {
        // YP (71)
        if (tx.nonce) {
            return TransactionError::BadNonce;
        }
        // YP (71)
        if (v0) {
            return TransactionError::InsufficientBalance;
        }
        return success();
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->code_hash != NULL_HASH)) {
        return TransactionError::SenderNotEoa;
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->nonce != tx.nonce)) {
        return TransactionError::BadNonce;
    }

    // YP (71)
    if (MONAD_UNLIKELY(sender_account->balance < v0)) {
        return TransactionError::InsufficientBalance;
    }

    // Note: Tg <= B_Hl - l(B_R)u can only be checked before retirement
    // (It requires knowing the parent block)

    return success();
 *)

Definition balanceOfAc (s: evm.GlobalState) (a: evm.address) : N (* 0 if account does not exist *) :=
  match s !! a with
  | Some ac => w256_to_N (block.block_account_balance (coreAc ac))
  | None => 0
  end.
    

Definition validateTx (preTxState: StateOfAccounts) (t: Transaction): bool :=
   bool_decide (txMaxFee t (* max_gas fee + value (* TO be removed *) *) <= balanceOfAc preTxState (sender t))%N.

Definition execTxAfterValidation hdr s txindex t:=
    let (si, r) := stateAfterTransactionAux hdr s txindex t in
    (applyGasRefundsAndRewards hdr si r, r).

(* txindex can be used to store incarnation numbers *)
Definition stateAfterTransactionV (hdr: BlockHeader) (txindex: nat) (s: StateOfAccounts) (t: Transaction): option (StateOfAccounts * TransactionResult) :=
  if (negb (validateTx s t))
  then None
  else Some (execTxAfterValidation hdr s txindex t).

Fixpoint stateAfterTransactionsV' (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction) (start:nat) (prevResults: list TransactionResult): option (StateOfAccounts * list TransactionResult) :=
  match ts with
  | [] => Some (s, prevResults)
  | t::tls => match stateAfterTransactionV hdr start s t with
              | Some (sf, r)=>
                  stateAfterTransactionsV' hdr sf tls (1+start) (prevResults++[r])
              | None => None
              end
                
  end.
    
    
Definition stateAfterTransactionsV  (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction): option (StateOfAccounts * list TransactionResult) := stateAfterTransactionsV' hdr s ts 0 [].


Definition stateAfterBlockV (b: Block) (s: StateOfAccounts): option (StateOfAccounts * list TransactionResult) :=
  match stateAfterTransactionsV (header b) s (transactions b) with
  | None => None
  | Some (s, tr) =>
      let s:= applyWithdrawals s (withdrawals b) in
      Some (applyBlockReward s (length (ommers b)), tr)
  end.

Open Scope N_scope.
Fixpoint totalTxFees (lt: list Transaction): gmap evm.address N :=
  match lt with
  | t::tl => 
      let r:= totalTxFees tl in
      let feesr := r !!!  (sender t) in 
      <[ sender t := feesr + txMaxFee t]> r
  | [] => ∅
  end.

Definition ReserveBal : N. Proof. Admitted. (* TODO: make it per/account and possibly dynamic *)

Definition txsFeesUB (s: evm.GlobalState) (lt: list Transaction) : Prop:=
  forall addr,
    match (totalTxFees lt) !! addr with
    | Some total => total <= balanceOfAc s addr /\ total <= ReserveBal
    | None => True
    end.

Definition isEOA (s: evm.GlobalState) (t: evm.address) : Prop. Proof. Admitted.

Fixpoint txSendersAreEOA (s: evm.GlobalState) (lt: list Transaction) : Prop:=
  match lt with
  | t::tl => isEOA s (sender t) /\ txSendersAreEOA s tl
  | [] => True
  end.

Lemma positiveFeesForEOAOnly s lt:
  forall (addr:evm.address),
    match (totalTxFees lt) !! addr with
    | Some total => isEOA s addr
    | None => True
    end.
Proof. Admitted. (* easy *)


Lemma noLowBalAbort bheader s lt :
  txsFeesUB s lt ->
  match stateAfterTransactionsV bheader s lt with
  | None => False
  | Some _ => True
  end.
Proof using.
Abort.

Require Import bluerock.auto.rwdb.
Require Import bluerock.auto.miscPure.
Require Import bluerock.hw_models.utils.
Require Import monad.proofs.bigauto.

Open Scope N_scope.
Definition noAccountAbs: Prop :=
  forall bheader s index tx,
  let '(sf, rct) := execTxAfterValidation bheader s index tx in
  forall addr, isEOA s addr
               -> isEOA sf addr
                  /\ if (decide (addr =  sender tx))
                     then (balanceOfAc sf addr >= balanceOfAc s addr - txMaxFee tx)
                     else (balanceOfAc sf addr >= balanceOfAc s addr).

Lemma eoaPres: noAccountAbs ->
  forall bheader s index tx,
  let '(sf, rct) := execTxAfterValidation bheader s index tx in
  forall lt, txSendersAreEOA s lt -> txSendersAreEOA sf lt.
Proof. Admitted.


    Lemma txFeesAreEoa s lt :
      txSendersAreEOA s lt-> forall addr,
      match totalTxFees lt !! addr with
      | Some _ => isEOA s addr
      | None => True
      end.
    Proof. Admitted.
    
Lemma noLowBalAbort' bheader s (lt: list Transaction) res index:
  noAccountAbs ->
  txSendersAreEOA s lt ->
  txsFeesUB s lt ->
  match stateAfterTransactionsV' bheader s lt index res with
  | None => False
  | Some _ => True
  end.
Proof using.
  intros Hnabs Hts.
  revert Hts.
  revert res index s.
  induction lt;[ simpl; auto; fail|].
  simpl.
  intros ? ? ? ? Htx.
  pose proof (eoaPres Hnabs bheader s index a) as Hpres.
  specialize (Hnabs bheader s index a).
  unfold txsFeesUB in *.
  simpl in *.
  forward_reason.
  pose proof (txFeesAreEoa s lt ltac:(auto)) as Hfeoa.
  pose proof (Htx (sender a)) as Htxs.
  Hint Rewrite @gmap.lookup_insert_iff : syntactic.
  rewrite  @gmap.lookup_insert_iff in Htxs;[| exact 0%N].
  miscPure.resolveDecide tauto.
  GC.
  unfold stateAfterTransactionV.
  unfold validateTx.
  forward_reason.
  resolveDecide lia.
  simpl.
  remember (execTxAfterValidation bheader s index a) as sf.
  destruct sf as [sf rcpt].
  apply IHlt; eauto;[].
  clear IHlt.
  intros addr.
  specialize (Htx addr).
  specialize (Hnabs addr).
  specialize (Hfeoa addr).
  destruct (decide (addr= evmopsem.sender a)).
  {
    subst.
    unfold lookup_total in *.
    specialize (Hnabs ltac:(auto)).
    simpl in *.
    unfold map_lookup_total in *.
    remember (totalTxFees lt !! evmopsem.sender a) as ltfeesa.
    destruct ltfeesa as [ltfeesa |]; auto;[].
    simpl in *.
    resolveDecide tauto.
    forward_reason.
    lia.
  }
  {
    rewrite  @gmap.lookup_insert_iff in Htx;[| exact 0%N].
    resolveDecide congruence.
    destruct (totalTxFees lt !! addr); auto;[].
    forward_reason.
    lia.
  }
Qed.

Definition dummyAc : AccountM := Build_AccountM block_account_default (Build_Indices 0 0) [] None None.

Definition DippedTooMuchIntoReserve (t: Transaction): TransactionResult. Proof. Admitted.

Definition updateBalanceOfAc (s: evm.GlobalState) (addr: evm.address) (upd: N -> N) : evm.GlobalState. Proof. Admitted.

(* every tx has a field: list DelegationAuth.  *)
Definition txDelegatedEOAs (*s: evm.GlobalState*) (tx: Transaction) : list evm.address. Proof. Admitted.


Definition accountDelegatedInState (s: evm.GlobalState) (a:evm.address) : bool. Proof. Admitted.
Definition accountDelegatedInTx (a:evm.address) : bool. Proof. Admitted.

Definition sendersInLastKBlocks (s: evm.GlobalState) : list evm.address . Proof. Admitted.


Definition execTxAfterValidationV2 (hdr: BlockHeader) (s: evm.GlobalState) (txindex: nat) (t: Transaction) : (evm.GlobalState * TransactionResult). Proof. Admitted.
(*
  let (si, r) := stateAfterTransactionAux hdr s txindex t in
  if (bool_decide (ReserveBal - txMaxFee t <= balanceOfAc si (sender t) (* debit gas fee from paymaster account?*)))
  then (applyGasRefundsAndRewards hdr si r, r)
      else if (accountDelegatedInState s (sender t) || accountDelegatedInTx (sender t))
           then (updateBalanceOfAc s (sender t) (fun oldBal => oldBal - txMaxFee t),  DippedTooMuchIntoReserve t)
           else if (bool_decide (sender t ∈ (sendersInLastKBlocks)))
                       then 
                         (updateBalanceOfAc s (sender t) (fun oldBal => oldBal - txMaxFee t),  DippedTooMuchIntoReserve t)
                       else (applyGasRefundsAndRewards hdr si r, r).
*)
(* txindex can be used to store incarnation numbers *)
Definition stateAfterTransactionV2 (hdr: BlockHeader) (txindex: nat) (s: StateOfAccounts) (t: Transaction): option (StateOfAccounts * TransactionResult) :=
  if (negb (validateTx s t)) (* if this fails. the execution of the entire block aborts *)
  then None
  else Some (execTxAfterValidationV2 hdr s txindex t).

Fixpoint stateAfterTransactionsV2' (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction) (start:nat) (prevResults: list TransactionResult): option (StateOfAccounts * list TransactionResult) :=
  match ts with
  | [] => Some (s, prevResults)
  | t::tls => match stateAfterTransactionV2 hdr start s t with
              | Some (sf, r)=>
                  stateAfterTransactionsV2' hdr sf tls (1+start) (prevResults++[r])
              | None => None
              end
                
  end.
    
Definition stateAfterTransactionsV2  (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction): option (StateOfAccounts * list TransactionResult) := stateAfterTransactionsV2' hdr s ts 0 [].

Lemma eoaPresV2:
  forall bheader s index tx,
  let '(sf, rct) := execTxAfterValidationV2 bheader s index tx in
  forall lt, txSendersAreEOA s lt -> txSendersAreEOA sf lt.
Proof. Admitted.

Lemma balanceOfUpd s ac f acp:
  balanceOfAc (updateBalanceOfAc s ac f) acp = if (bool_decide (ac=acp)) then f (balanceOfAc s ac) else (balanceOfAc s acp).
Proof. Admitted.

(*
- other failure modes.
- simpler&more user-friendly impl: just pass the txMaxFees counts down the tx
 *)

Definition evmTxDebits: Prop :=
  forall bheader s index tx,
  let '(sf, rct) := execTxAfterValidationV2 bheader s index tx in
  forall addr, isEOA s addr
               -> isEOA sf addr
                  /\ if (decide (addr =  sender tx))
                     then (balanceOfAc sf addr >= balanceOfAc s addr - txMaxFee tx)
                     else (balanceOfAc sf addr >= balanceOfAc s addr).

Definition consensusChecks (kpreState: evm.GlobalState) (intermediateTxs: list Transaction) (tx: Transaction) : Prop. Proof. Admitted.

(*
B1:
  t1
    t2

B2: 
    t3
    t4
*)

(*
Lemma noLowBalAbortV2' skre intermediateTxs bheader s lt res index:
  consensusChecks skpre intermediateTxs  ->
  stateAfterTransactionsV2' bheader intermediateTxs lt index res = Some s ->
  match stateAfterTransactionsV2' bheader s lt index res with
  | None => False
  | Some _ => True
  end.
Proof using.
  intros Hts.
  revert Hts.
  revert res index s.
  induction lt;[ simpl; auto; fail|].
  simpl.
  intros ? ? ? ? Htx.
  pose proof (eoaPresV2 bheader s index a) as Hpres.
  unfold txsFeesUB in *.
  simpl in *.
  forward_reason.
  pose proof (txFeesAreEoa s lt ltac:(auto)) as Hfeoa.
  pose proof (Htx (sender a)) as Htxs.
  Hint Rewrite @gmap.lookup_insert_iff : syntactic.
  rewrite  @gmap.lookup_insert_iff in Htxs;[| exact 0%N].
  miscPure.resolveDecide tauto.
  GC.
  unfold stateAfterTransactionV2.
  unfold validateTx.
  forward_reason.
  resolveDecide lia.
  simpl.
  unfold execTxAfterValidationV2 in *.
  destruct (stateAfterTransactionAux bheader s index a) as [si tr].
  simpl in *.
  case_bool_decide.
  2:{ (* transaction reverts *)
      apply IHlt; eauto.
      clear IHlt.
      intros addr.
      specialize (Htx addr).
      specialize (Hfeoa addr).
      rewrite balanceOfUpd.
      destruct (decide (addr= evmopsem.sender a)).
      {
        subst.
        unfold lookup_total in *.
        simpl in *.
        unfold map_lookup_total in *.
        remember (totalTxFees lt !! evmopsem.sender a) as ltfeesa.
        destruct ltfeesa as [ltfeesa |]; auto;[].
        simpl in *.
        resolveDecide tauto.
        forward_reason.
        lia.
      }
      {
        rewrite  @gmap.lookup_insert_iff in Htx;[| exact 0%N].
        resolveDecide congruence.
        destruct (totalTxFees lt !! addr); auto;[].
        revert Htx.
        case_bool_decide. tauto.
        intros.
        Search n1.
        lia.
      }
  }
  {
      apply IHlt; eauto.
      clear IHlt.
      intros addr.
      specialize (Htx addr).
      specialize (Hfeoa addr).
      destruct (decide (addr= evmopsem.sender a)).
      {
        subst.
        unfold lookup_total in *.
        simpl in *.
        unfold map_lookup_total in *.
        remember (totalTxFees lt !! evmopsem.sender a) as ltfeesa.
        destruct ltfeesa as [ltfeesa |]; auto;[].
        simpl in *.
        resolveDecide tauto.
        forward_reason.
        lia.
      }
      {
        rewrite  @gmap.lookup_insert_iff in Htx;[| exact 0%N].
        resolveDecide congruence.
        destruct (totalTxFees lt !! addr); auto;[].
        revert Htx.
        case_bool_decide. tauto.
        intros.
        Search n1.
        lia.
      }
    
  
Qed.
*)
