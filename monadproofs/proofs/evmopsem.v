Require Import monad.EVMOpSem.block.
Require Import stdpp.gmap.

(* delete and inline? *)
Definition Transaction := transaction.

Record Indices :=
  {
    block_index: N;
    tx_index: N;
  }.

Definition AccountM : Type := (block.block_account * Indices).

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

Definition validateTx (preTxState: StateOfAccounts) (t: Transaction): bool :=
  match preTxState !! (sender t) with
  | None => false
  | Some (ac,_) => bool_decide (txMaxFee t <= w256_to_N (block.block_account_balance ac))%N
  end.
  
(* txindex can be used to store incarnation numbers *)
Definition stateAfterTransactionV (hdr: BlockHeader) (txindex: nat) (s: StateOfAccounts) (t: Transaction): option (StateOfAccounts * TransactionResult) :=
  if (negb (validateTx s t))
  then None
  else
    let (si, r) := stateAfterTransactionAux hdr s txindex t in
    Some (applyGasRefundsAndRewards hdr si r, r).

Fixpoint stateAfterTransactionsV' (hdr: BlockHeader) (s: StateOfAccounts) (ts: list Transaction) (start:nat) (prevResults: list TransactionResult): option (StateOfAccounts * list TransactionResult) :=
  match ts with
  | [] => Some (s, prevResults)
  | t::tls => let (sf, r) := stateAfterTransaction hdr start s t in
              stateAfterTransactionsV' hdr sf tls (1+start) (prevResults++[r])
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
Definition totalTxFees (lt: list Transaction): gmap evm.address N :=
  List.fold_left (fun r t =>
                    let feesr := r !!!  (sender t) in 
                    <[ sender t := feesr + txMaxFee t]> r
    ) lt ∅.

Definition ReserveBal : N. Proof. Admitted. (* TODO: make it per/account and possibly dynamic *)


Definition txsFeesUB (s: evm.GlobalState) (lt: list Transaction) : Prop:=
  forall addr,
    match (totalTxFees lt) !! addr with
    | Some total =>
        match s !! addr with
        | None => False
        | Some (f,_) => total <= w256_to_N (block.block_account_balance f)
                    /\ total <= ReserveBal
        end
    | None => True
    end.

(*
Lemma noLowBalAbort bheader lt : txFeesUB s lt ->
    execTra
*)
