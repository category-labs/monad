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

Definition addr_delegated  (s: evm.GlobalState) (a : evm.address) : bool :=
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


Definition TxWithHdr : Type := BlockHeader * Transaction.

(* only gas fees. does not include value transfers *)
Definition maxTxFee (t: TxWithHdr) : N. Proof. Admitted.

(* Sum over gas_limit * gas_bid for a list of transactions. *)
Fixpoint sum_gas_bids (l : list TxWithHdr) : N :=
  match l with
  | [] => 0
  | tx :: xs => maxTxFee tx + sum_gas_bids xs
  end.

Definition staticReserveBal : N. Proof. Admitted.
(* intermediate does not include [candidate] *)

(*
candidate: block n
stateAfterLastExecuted : state after n-k

The design below works. it has a allowed_to_empty field in each tx.
The leader sets this flag in the manner described in the relation below: the relation constrains the value of the field for [candidate] in each case.

The main problem though is that followers may have a difficult time verifying
this field:
Suppose k=10.
Block 19 and 20 have pure withdrawal transactions (no smart contract) from Alice.
The block 20 tx will be marked as allowed_to_empty if it is verifying starting block 19, but not if it
is verifyied starting from block 18 state.

Need to maintain fixed distance.
 *)


(* assume:
   - all transactions in intermediate have their [isAllowedToEmpty] fields properly set. that field is garbage for [candidate]
   - stateNminusK: is the state after executing block n-k
   - intermediate has ALL transactions between the end of block n-k and candidate
   - candidate is from block n: TODO: fix this
 *)
Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.

Definition sender (t: TxWithHdr): evm.address := sender (snd t).
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value (snd t)).
Axiom _isAllowedToEmptyC : Lens.Lens Transaction Transaction bool bool.


Definition _isAllowedToEmpty : Lens.Lens TxWithHdr TxWithHdr bool bool := lens._snd .@ _isAllowedToEmptyC.

Definition consensusAcceptableTx (stateNminusK : StateOfAccounts) (intermediate : list TxWithHdr) (candidate : TxWithHdr) : bool * bool :=
  let bal0 := balanceOfAc stateNminusK (sender candidate) in
  match List.filter (fun tx: TxWithHdr  => bool_decide (sender tx = sender candidate)) intermediate with
  | [] =>
      let reserve := staticReserveBal `min` bal0 in
      if addr_delegated stateNminusK (sender candidate) then
        (true,
          bool_decide (maxTxFee candidate <= balanceOfAc stateNminusK (sender candidate)))
      else (false, bool_decide (maxTxFee candidate ≤ reserve))
  | t0 :: rest =>
      (false, 
      if (t0 .^ _isAllowedToEmpty) 
      then
       let bal1 := bal0 - value t0 - maxTxFee t0 in
       let reserve := staticReserveBal `min` bal1 in
       bool_decide (sum_gas_bids  (candidate::rest) ≤ reserve)
      else
       let reserve := staticReserveBal `min` bal0 in
       bool_decide (sum_gas_bids (candidate::intermediate) ≤ reserve))
  end.

Fixpoint consensusAcceptableTxs (s : StateOfAccounts) (acceptedIntermediateTxs ltx : list TxWithHdr) : (bool * list TxWithHdr) :=
  match ltx with
  | [] => (true, acceptedIntermediateTxs)
  | h::tl => let '(allowedToEmpty,  acceptableHead) := consensusAcceptableTx s acceptedIntermediateTxs h in 
             let '(acceptableTail, markedTxs) := consensusAcceptableTxs s (acceptedIntermediateTxs++[h &: _isAllowedToEmpty .= allowedToEmpty]) tl in
             (acceptableHead && acceptableTail, markedTxs)
  end.

Definition consensusAcceptableBlocksBuggy (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) : bool :=
  let allTx := flat_map transactions proposedChainExtension in
  fst (consensusAcceptableTxs stateNminusK [] allTx).


Definition consensusAcceptableBlocks (stateNminusK : N -> StateOfAccounts)
  (proposedChainExtension: list Block) : bool :=
  let allTx := flat_map transactions proposedChainExtension in
  fst (consensusAcceptableTxs stateNminusK [] allTx).

    

Definition execTxAfterValidationV2 (hdr: BlockHeader) (s: evm.GlobalState) (txindex: nat) (t: Transaction) : (evm.GlobalState * TransactionResult) :=
  let (si, r) := stateAfterTransactionAux hdr s txindex t in
  let erb := N.min ReserveBal (balanceOfAc s (sender t)) in
  if (bool_decide (erb (* - txMaxFee t *) <= balanceOfAc si (sender t)) || (t .^ _isAllowedToEmpty))
  then (applyGasRefundsAndRewards hdr si r, r)
  else (updateBalanceOfAc s (sender t) (fun oldBal => oldBal - txMaxFee t),  DippedTooMuchIntoReserve t).

Axiom _transactions : Lens.Lens Block Block (list Transaction) (list Transaction).

(*
Definition consensusAcceptableBlocksMarked (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) : bool* (list Block) :=
  let allTx := flat_map transactions proposedChainExtension in
  fst (consensusAcceptableTxs stateNminusK [] allTx).
 *)

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

               
Lemma soundness (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks stateNminusK proposedChainExtension = true
  -> isSome (stateAfterBlocks stateNminusK proposedChainExtension).
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


Lemma execBlockAsTxs (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) :
  isSome (stateAfterTransactionsV (maxFeeHeader proposedChainExtension) stateNminusK
            (flat_map transactions proposedChainExtension))
         ->
  isSome (stateAfterBlocks stateNminusK proposedChainExtension).
Proof using. Admitted.

Lemma soundnessAsTx (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) (lt : list Transaction):
  fst (consensusAcceptableTxs stateNminusK [] lt) = true
    → isSome (stateAfterTransactionsV (maxFeeHeader proposedChainExtension) stateNminusK lt).
Proof using. Admitted.

Lemma soundness (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks stateNminusK proposedChainExtension = true
  -> isSome (stateAfterBlocks stateNminusK proposedChainExtension).
Proof using.
  unfold consensusAcceptableBlocks.
  intros Hp.
  apply execBlockAsTxs.
  apply soundnessAsTx.
  assumption.
Qed.    


Lemma subchainValid (stateNminusK : StateOfAccounts)
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks stateNminusK proposedChainExtension = true
  -> forall (subchain1 subchain2: list Block),
      proposedChainExtension = subchain1 ++ subchain2
      -> match (stateAfterBlocks stateNminusK subchain1) with
         | None => False (* cannot happen *)
         | Some (stateAfterSubchain1, rcpts) =>
             consensusAcceptableBlocks stateAfterSubchain1 subchain2 = true
         end.
Abort.           
           
Proof using.
  unfold consensusAcceptableBlocks.
  intros Hp.
  apply execBlockAsTxs.
  apply soundnessAsTx.
  assumption.
Qed.    




(* txindex can be used to store incarnation numbers *)
        

(*
Questions:
- what is maxHeader
- what is delagation. can an account be delegated beyond a tx. with delegation, which accounts can a tx debit?
EIP 7702
- before vs after account abstraction: how debit bounds changed: previously, debit bounded by tx.value put tx.maxGasFees, now no bound?
*)

