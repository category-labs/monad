(* proofs about reserve balances:
- consensus guarnatees when it sends a block for executions
- what consensus assumes execution guarantees
- how those guarantees ensure execution will never run into a chase when an account has insufficient balance to pay gas fees
 *)
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.proofs.evmopsem.


(*
In the above latex document, there is an algorithm within \begin{algorithm} with caption
"Consensus Checks for block $n$ for sequencing transaction $t$ from account $a$".
Implement it in Gallina as a function by filling in the following:

```gallina
Definition consensusAcceptableTx (s: evm.GlobalState) (intermediate: list Transaction) (a: Transaction) : bool :=
```

Unlike in the latex document, assume that list `intermediate` does NOT contain the candidate transaction `a`. Above `s` can be considered as the $state^{n-k}$ argument in the latex document.
Ignore the $\mathcal{P}_{n-2k+2}^{t}$ argument, which is only needed in the call to is_emptying_transaction, which you can leave admitted for now.

Use N to do operations on balances, not monad.EVMOpSem.keccak.w256.
We have w256_to_N and Z_to_w256.

Use bool_decide for boolean decisions: e.g. use `bool_decide (a<b)%N` instead of `N.ltb a b`.
Once your definitions typecheck and you are satisfied, do the beautification stage where you reduce the fully qualified names to more readable names and use more notations. Keep a TOFIXLATER until then so that the outer bot keeps coming back to you.
 
+++ QUERIES
Print evm.GlobalState.
Print w256_to_N.
Print Z_to_w256.
Print balanceOfAc.
Print updateBalanceofAc.

+++ FILES
../proofs/reservebal.md

 *)

(*
(* ----------------------------------------------------------------------- *)
(* Read the “reserve balance” of account [sender] at consensus state [s].  *)
(* Here we use the on‐chain balance, i.e. no per‐account override.          *)
Definition user_reserve_balance
  (s : monad.proofs.evmopsem.evm.GlobalState)
  (sender : monad.proofs.evmopsem.evm.address)
  : N := 100.
 *)


(* just a field in the Transaction record *)
Definition tx_allowed_to_empty
 (*s : StateOfAccounts*) (a : Transaction) : bool :=
  false.

(*
(* Interpret the legacy gas_price field as our gas_bid. *)
Definition gas_bid_of (t : monad.proofs.evmopsem.Transaction) : N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_gas_price t).

(* Convert the w256‐typed gas_limit to N. *)
Definition gas_limit_of (t : monad.proofs.evmopsem.Transaction) : N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_gas_limit t).
*)

(* only gas fees. does not include value transfers *)
Definition maxTxFee (s_n_minus_k: StateOfAccounts) (t: Transaction) : N. Proof. Admitted.

(* Sum over gas_limit * gas_bid for a list of transactions. *)
Fixpoint sum_gas_bids (s_n_minus_k: StateOfAccounts) (l : list Transaction) : N :=
  match l with
  | [] => 0
  | tx :: xs => maxTxFee s_n_minus_k tx + sum_gas_bids s_n_minus_k xs
  end.

Definition staticReserveBal : N. Proof. Admitted.
(* Consensus‐side acceptability check for sequencing [a], given state s = state^{n-k}
   and the list [intermediate] of prior txns from this sender after block n-k. *)
Definition consensusAcceptableTx (stateAfterLastExecuted : StateOfAccounts) (intermediate : list Transaction) (a : Transaction) :=
  let bal0 := balanceOfAc stateAfterLastExecuted (sender a) in
  match List.filter (fun tx: Transaction  => bool_decide (sender tx = sender a))intermediate with
  | [] =>
      let reserve := staticReserveBal `min` bal0 in
      bool_decide (maxTxFee stateAfterLastExecuted a ≤ reserve)
  | t0 :: rest =>
      (negb (tx_allowed_to_empty a)) &&
      if tx_allowed_to_empty (*stateAfterLastExecuted *) t0
      then
       let bal1 := bal0 - w256_to_N (block.tr_value t0) - maxTxFee stateAfterLastExecuted t0 in
       let reserve := staticReserveBal `min` bal1 in
       bool_decide (sum_gas_bids stateAfterLastExecuted (a::rest) ≤ reserve)
      else
       let reserve := staticReserveBal `min` bal0 in
       bool_decide (sum_gas_bids stateAfterLastExecuted (a::intermediate) ≤ reserve)
  end.

Fixpoint consensusAcceptableTxs (s : StateOfAccounts) (intermediateTxs ltx : list Transaction) : bool :=
  match ltx with
  | [] => true
  | h::tl => consensusAcceptableTx s intermediateTxs h && consensusAcceptableTxs s (intermediateTxs++[h]) tl
  end.
    
Definition consensusAcceptableBlocks (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) : bool :=
  let allTx := flat_map transactions proposedChainExtension in
  consensusAcceptableTxs stateAfterLastExecuted [] allTx.

Definition stateAfterBlockV2 (b: Block) (s: StateOfAccounts): option (StateOfAccounts * list TransactionResult) :=
  match stateAfterTransactionsV2 (header b) s (transactions b) with
  | None => None
  | Some (s, tr) =>
      let s:= applyWithdrawals s (withdrawals b) in
      Some (applyBlockReward s (length (ommers b)), tr)
  end.

Fixpoint stateAfterBlocks (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) :
  option (StateOfAccounts * list (list TransactionResult)) :=
  match proposedChainExtension with
  | [] => Some (stateAfterLastExecuted, [])
  | h::tl => match stateAfterBlockV2 h stateAfterLastExecuted with
             | None => None
             | Some (si, rcpts) =>
                 match stateAfterBlocks si tl with
                 | None => None
                 | Some (sf, lrcpts) => Some (sf, rcpts::lrcpts)
                 end
             end
  end.
    
               
Lemma soundness (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks stateAfterLastExecuted proposedChainExtension = true
  -> isSome (stateAfterBlocks stateAfterLastExecuted proposedChainExtension).
Abort.

Definition maxFeeHeader (lb: list Block) : BlockHeader. Proof. Admitted.


Lemma execTxMono header (s1 s2 : StateOfAccounts) i (tx: Transaction) :
  (forall addr, balanceOfAc s1 addr <= balanceOfAc s2 addr)
  -> isSome (stateAfterTransactionV2 header i s1 tx)
  -> isSome (stateAfterTransactionV2 header i s2 tx).
Proof. Admitted.

Lemma execTxsMono header (s1 s2 : StateOfAccounts) (ltx: list Transaction) :
  (forall addr, balanceOfAc s1 addr <= balanceOfAc s2 addr)
  -> isSome (stateAfterTransactionsV2 header s1 ltx)
  -> isSome (stateAfterTransactionsV2 header s2 ltx).
Proof. Admitted.


Lemma execBlockAsTxs (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) :
  isSome (stateAfterTransactionsV (maxFeeHeader proposedChainExtension) stateAfterLastExecuted
            (flat_map transactions proposedChainExtension))
         ->
  isSome (stateAfterBlocks stateAfterLastExecuted proposedChainExtension).
Proof using. Admitted.

Lemma soundnessAsTx (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) (lt : list Transaction):
  consensusAcceptableTxs stateAfterLastExecuted [] lt = true
    → isSome (stateAfterTransactionsV (maxFeeHeader proposedChainExtension) stateAfterLastExecuted lt).
Proof using. Admitted.

Lemma soundness (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks stateAfterLastExecuted proposedChainExtension = true
  -> isSome (stateAfterBlocks stateAfterLastExecuted proposedChainExtension).
Proof using.
  unfold consensusAcceptableBlocks.
  intros Hp.
  apply execBlockAsTxs.
  apply soundnessAsTx.
  assumption.
Qed.    
        
Definition execTxAfterValidationV2 (hdr: BlockHeader) (s: evm.GlobalState) (txindex: nat) (t: Transaction) : (evm.GlobalState * TransactionResult) :=
  let (si, r) := stateAfterTransactionAux hdr s txindex t in
  let erb := N.min ReserveBal (balanceOfAc s (sender t)) in
  if (bool_decide (erb (* - txMaxFee t *) <= balanceOfAc si (sender t)) || tx_allowed_to_empty t)
  then (applyGasRefundsAndRewards hdr si r, r)
  else (updateBalanceOfAc s (sender t) (fun oldBal => oldBal - txMaxFee t),  DippedTooMuchIntoReserve t).



(* txindex can be used to store incarnation numbers *)
        

(*
Questions:
- what is maxHeader
- what is delagation. can an account be delegated beyond a tx. with delegation, which accounts can a tx debit?
- before vs after account abstraction: how debit bounds changed: previously, debit bounded by tx.value put tx.maxGasFees, now no boung?
*)

