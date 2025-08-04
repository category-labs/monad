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

Definition addrDelegated  (s: evm.GlobalState) (a : evm.address) : bool. Proof. Admitted.

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


Definition TxWithHdr : Type := BlockHeader * (Transaction * N).

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

Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.

Definition sender (t: TxWithHdr): evm.address := sender (fst (snd t)).
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value (fst (snd t))).

Definition K : N. Proof. Admitted.


Definition txDelegatesAddr (addr: evm.address) (tx: TxWithHdr) : bool. Proof. Admitted.

(*
#[global] Instance inhAddr: Inhabited evm.address. Proof. Admitted.
#[global] Instance inhBlockHeader : Inhabited BlockHeader := { Build_BlockHeader None 0 inhabitant 0. *)
#[global] Instance inhBlock : Inhabited Block. Proof. Admitted. (* := Build_Block [] dummyHeader [] None. *)
Definition blocksInRange (prevBlocks: gmap N Block) (start len: N) : list Block:=
  List.map  (fun n=> prevBlocks !!! n) (seqN start len).


Definition txIndexInBlock  (tx: TxWithHdr) : N:= (snd (snd tx)).

Definition transactions (b: Block) : list TxWithHdr :=
  map (fun p => (header b, p)) (combine (transactions b) (seqN 0 (lengthN (transactions b)))).

Definition txBlockNum (t: TxWithHdr) : N := number (fst t).

Definition intermediateTxs (knownBlocks: gmap N Block) (stateBlockIndex: N) (tx: TxWithHdr) :=
  let txBlock := knownBlocks !!! (txBlockNum tx) in
  let prevTxsInSameBlock := (firstn (N.to_nat (txIndexInBlock tx)) (transactions txBlock)) in 
   prevTxsInSameBlock ++ (flat_map transactions (blocksInRange knownBlocks (txBlockNum tx - K) (K-1))).

Definition emptyingCheckRange (knownBlocks: gmap N Block) (tx: TxWithHdr) :=
  let txBlock := knownBlocks !!! (txBlockNum tx) in
  let prevTxsInSameBlock := (firstn (N.to_nat (txIndexInBlock tx)) (transactions txBlock)) in
  ((flat_map transactions (blocksInRange knownBlocks (txBlockNum tx - K) (K-1)))
                                                                 ++  prevTxsInSameBlock).

Definition isAllowedToEmpty (knownBlocks: gmap N Block)
  (state : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr)  (tx: TxWithHdr) : bool :=
  let notDelegated := negb (addrDelegated state (sender tx)) &&
                        forallb (fun txx => negb (txDelegatesAddr (sender tx) txx)) intermediateTxsSinceState in
  let prevTxsFromSameSender := 
    List.filter (fun t => bool_decide (sender t = sender tx)) (emptyingCheckRange knownBlocks tx)
                in notDelegated && bool_decide (lengthN prevTxsFromSameSender = 0).


Definition maxTotalReserveDippableDebit (knownBlocks: gmap N Block) (latestKnownState : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr) tx :=
  maxTxFee tx +
  (if isAllowedToEmpty knownBlocks latestKnownState intermediateTxsSinceState tx
  then value tx 
   else 0).

Fixpoint maxTotalReserveDippableDebitL (knownBlocks: gmap N Block) (latestKnownState : StateOfAccounts) (postStateAccountedSuffix rest: list TxWithHdr) (a: evm.address) : N:=
  match rest with
  | [] => 0
  | h::tl =>
      (maxTotalReserveDippableDebitL knownBlocks latestKnownState (postStateAccountedSuffix++[h]) tl a)
      + (if bool_decide (sender h = a)
         then (maxTotalReserveDippableDebit knownBlocks latestKnownState postStateAccountedSuffix h)
         else 0)
  end.

Definition consensusAcceptableTxG (knownBlocks: gmap N Block) (latestKnownState : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr) (candidate : TxWithHdr) : bool :=
  let bal0 := balanceOfAc latestKnownState (sender candidate) in
  let NminusK := (txBlockNum candidate - K) in
  if isAllowedToEmpty knownBlocks latestKnownState intermediateTxsSinceState candidate
  then bool_decide (maxTxFee candidate <= balanceOfAc latestKnownState (sender candidate))
  else
    bool_decide (maxTotalReserveDippableDebitL knownBlocks latestKnownState [] intermediateTxsSinceState (sender candidate)
                 <= balanceOfAc latestKnownState (sender candidate)).

Definition consensusAcceptableTx (knownBlocks: gmap N Block) (stateNminusK : StateOfAccounts) (candidate : TxWithHdr) : bool :=
  let NminusK := (txBlockNum candidate - K) in
  let intermediate := (intermediateTxs knownBlocks NminusK candidate) in 
  consensusAcceptableTxG knownBlocks stateNminusK intermediate candidate.

  

Definition consensusAcceptableBlock (knownBlocks: gmap N Block) (stateNminusK : StateOfAccounts) (block: Block) : bool :=
  forallb  (consensusAcceptableTx knownBlocks stateNminusK) (transactions block).

Definition consensusAcceptableBlocks (knownBlocks: gmap N Block) (knownStates: gmap N StateOfAccounts)
  (proposedChainExtension: list Block) : bool :=
  forallb (fun b => consensusAcceptableBlock knownBlocks (knownStates !!! (number (header b) - K)) b) proposedChainExtension.

Definition isAllowedToEmptyLatestState (knownBlocks: gmap N Block)
  (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  let notDelegated := negb (addrDelegated state (sender tx)) in
  let prevTxsFromSameSender := 
    List.filter (fun t => bool_decide (sender t = sender tx)) (emptyingCheckRange knownBlocks tx)
                in bool_decide (lengthN prevTxsFromSameSender = 0).

Definition allAccounts: list evm.address. Proof. Admitted. (* define it opaquely with Qed: never unfold *)

Definition execTxAfterValidationV2 (knownBlocks: gmap N Block) (s: evm.GlobalState) (t: TxWithHdr) : (evm.GlobalState * TransactionResult) :=
  let '(hdr, (tx, txindex)) := t in 
  let (si, r) := stateAfterTransactionAux hdr s (N.to_nat txindex) tx in
  let balCheck (a: evm.address) :=
    let erb := N.min ReserveBal (balanceOfAc s a) in
    bool_decide (erb  - (if bool_decide (sender t =a ) then maxTxFee t else 0) <= balanceOfAc si a) in
  let allBalCheck := (forallb balCheck allAccounts) in
  if (isAllowedToEmptyLatestState knownBlocks s t || allBalCheck)
  then (applyGasRefundsAndRewards hdr si r, r) (* this cannot debit any account. move such steps to stateAfterTransactionAux *)
  else (updateBalanceOfAc s (sender t) (fun oldBal => oldBal - txMaxFee (fst (snd t))),  DippedTooMuchIntoReserve (fst (snd t))) (* revert tx *).


Definition validateTx (preTxState: StateOfAccounts) (t: TxWithHdr): bool :=
   bool_decide (maxTxFee t  <= balanceOfAc preTxState (sender t))%N.

Definition stateAfterTransactionV2 (knownBlocks: gmap N Block) (s: StateOfAccounts) (t: TxWithHdr): option (StateOfAccounts * TransactionResult) :=
  if (negb (validateTx s t)) (* if this fails. the execution of the entire block aborts *)
  then None
  else Some (execTxAfterValidationV2 knownBlocks  s t).

Fixpoint stateAfterTransactionsV2 (knownBlocks: gmap N Block)  (s: StateOfAccounts) (ts: list TxWithHdr): option (StateOfAccounts * list TransactionResult) :=
  match ts with
  | [] => Some (s, [])
  | t::tls =>
      match stateAfterTransactionV2 knownBlocks s t with
      | Some (si, r)=>
          match stateAfterTransactionsV2 knownBlocks si tls with
          | Some (sf, lr)=> Some (sf, r::lr)
          | None => None
          end
      | None => None
      end
  end.

Lemma isEmptyingEq (knownBlocks: gmap N Block) (s1 s2 : StateOfAccounts) n tx :
  (forall a, addrDelegated s1 a = addrDelegated s2 a)
  -> isAllowedToEmpty knownBlocks s1 n tx =  isAllowedToEmpty knownBlocks s2 n tx.
Proof using.
  intros Hd.
  unfold isAllowedToEmpty.
  rewrite Hd.
  reflexivity.
Qed.

Set Nested Proofs Allowed.

Lemma maxTotalReserveDippableDebitEq (knownBlocks: gmap N Block) (s1 s2 : StateOfAccounts) (accountedSuffix: list TxWithHdr) (candidate : TxWithHdr) :
  (∀ a : evm.address, addrDelegated s1 a = addrDelegated s2 a)
  ->   maxTotalReserveDippableDebit knownBlocks s1 accountedSuffix candidate =
         maxTotalReserveDippableDebit knownBlocks s2 accountedSuffix candidate.
Proof using.
  intros Hd.
  unfold maxTotalReserveDippableDebit.
  symmetry.
  rewrite -> isEmptyingEq with (s2:=s1) by auto.
  reflexivity.
Qed.

Lemma maxTotalReserveDippableDebitLeq (knownBlocks: gmap N Block) (s1 s2 : StateOfAccounts) (accountedSuffix unaccountedSuffix: list TxWithHdr) (candidate : TxWithHdr) :
  (∀ a : evm.address, addrDelegated s1 a = addrDelegated s2 a)
  -> maxTotalReserveDippableDebitL knownBlocks s1 accountedSuffix unaccountedSuffix (sender candidate)
     = maxTotalReserveDippableDebitL knownBlocks s2 accountedSuffix unaccountedSuffix (sender candidate).
Proof using.
  intros Hd. revert accountedSuffix.
  induction unaccountedSuffix; simpl in *; auto;[].
  intros.
  rewrite IHunaccountedSuffix.
  f_equal.
  case_bool_decide; auto.
  apply maxTotalReserveDippableDebitEq; auto.
Qed.


Lemma consensusAcceptableTxGmono (knownBlocks: gmap N Block) (s1 s2 : StateOfAccounts) (intermediate: list TxWithHdr) (candidate : TxWithHdr) :
  (forall a, balanceOfAc s1 a <= balanceOfAc s2 a)
  -> (forall a, addrDelegated s1 a = addrDelegated s2 a)
  -> consensusAcceptableTxG knownBlocks s1 intermediate candidate = true
  -> consensusAcceptableTxG knownBlocks s2 intermediate candidate = true.
Proof.
  intros Hb Hd Hc.
  unfold consensusAcceptableTxG in *.
  specialize (Hb (sender candidate)).
  rewrite -> isEmptyingEq with (s2:=s1) by auto.
  case_match; rewrite -> bool_decide_eq_true in *; try lia;[].
  rewrite -> maxTotalReserveDippableDebitLeq with (s2:=s1) by auto.
  lia.
Qed.
Print Assumptions consensusAcceptableTxGmono.

(*
Axioms:
txDelegatesAddr : evm.address → TxWithHdr → bool
maxTxFee : TxWithHdr → N
inhBlock : Inhabited Block
addrDelegated : StateOfAccounts → evm.address → bool
evm.RelDecision_instance_0 : EqDecision evm.address
K : N
evm.Countable_instance_0 : Countable evm.address

 *)

Lemma inductiveStep (knownBlocks: gmap N Block) (latestState : StateOfAccounts) (intermediateHd: TxWithHdr) (intermediateTl: list TxWithHdr) (candidate : TxWithHdr) :
  consensusAcceptableTxG knownBlocks latestState (intermediateHd::intermediateTl) candidate = true
  -> match stateAfterTransactionV2 knownBlocks latestState intermediateHd with
     | None =>  False
     | Some (si, tr) =>
         consensusAcceptableTxG knownBlocks si intermediateTl candidate = true
     end.
Proof.
  intros Hc.
  unfold consensusAcceptableTxG in Hc.
  case_match.
  {
    

  here
Abort.


Lemma inductiveSteps (knownBlocks: gmap N Block) (latestState : StateOfAccounts) (intermediate1 intermediate2: list TxWithHdr) (candidate : TxWithHdr) :
  consensusAcceptableTxG knownBlocks latestState (intermediate1++intermediate2) candidate = true
  -> match stateAfterTransactionsV2 knownBlocks latestState intermediate1 with
     | None =>  False
     | Some (si, tr) =>
         consensusAcceptableTxG knownBlocks si intermediate2 candidate = true
     end.
Proof. Abort.

Definition stateAfterBlockV2 (knownBlocks: gmap N Block) (s: StateOfAccounts) (b: Block): option (StateOfAccounts * list TransactionResult) :=
  match stateAfterTransactionsV2 knownBlocks s (transactions b) with
  | None => None
  | Some (s, tr) =>
      let s:= applyWithdrawals s (withdrawals b) in
      Some (applyBlockReward s (length (ommers b)), tr)
  end.

Fixpoint stateAfterBlocks knownBlocks (stateAfterLastExecuted : StateOfAccounts)
  (proposedChainExtension: list Block) :
  option (StateOfAccounts * list (list TransactionResult)) :=
  match proposedChainExtension with
  | [] => Some (stateAfterLastExecuted, [])
  | h::tl => match stateAfterBlockV2 knownBlocks stateAfterLastExecuted h with
             | None => None
             | Some (si, rcpts) =>
                 match stateAfterBlocks knownBlocks si tl with
                 | None => None
                 | Some (sf, lrcpts) => Some (sf, rcpts::lrcpts)
                 end
             end
  end.

Definition firstBlockNumber (l : list Block): N :=
  hd 0 (map (fun b => number (header b)) l).
               
Lemma soundness knownBlocks knownStates
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks knownBlocks knownStates proposedChainExtension = true
  -> isSome (stateAfterBlocks knownBlocks (knownStates !!! (firstBlockNumber proposedChainExtension  - 1)) proposedChainExtension).
Abort.

Lemma stateAfterBlocksSnoc knownBlocks (stateAfterLastExecuted : StateOfAccounts)
                              (tl: list Block) b:
    stateAfterBlocks knownBlocks stateAfterLastExecuted (tl ++ [b]) =
  match stateAfterBlocks knownBlocks stateAfterLastExecuted tl with
  | None => None
  | Some (si, lrcpts) =>
      match stateAfterBlockV2 knownBlocks si b with
      | None => None
      | Some (sf, rcpts) => Some (sf, lrcpts++[rcpts])
      end
  end.
Proof. Admitted.

  Set Nested Proofs Allowed.
  Lemma takenSCases {T} (l : list T) (n:nat) :
    take (S n) l=
    match l !! n with
    | Some x=> take n l ++ [x]
    | None => take n l
    end.
  Proof.
    remember (l !! n) as ln.
    destruct ln.
    - rewrite -> take_S_r with (x:= t); auto.
    - admit.
  Admitted.

Lemma soundnessInd knownBlocks knownStates
  (proposedChainExtension: list Block) :
  consensusAcceptableBlocks knownBlocks knownStates proposedChainExtension = true
  -> forall n:nat, isSome (stateAfterBlocks knownBlocks (knownStates !!! (firstBlockNumber proposedChainExtension  - 1)) (firstn n proposedChainExtension)).
Proof using.
  intros Hc n.
  induction n;[simpl in *; tauto|].

  rewrite takenSCases.
  simpl.
  remember (proposedChainExtension !! n) as lastb.
  destruct lastb as [lastb |]; simpl; auto;[].
  rewrite stateAfterBlocksSnoc.
  unfold isSome in *.
  match goal with
    [|- context[stateAfterBlocks ?a ?b ?c]] => remember (stateAfterBlocks a b c) as si
  end.
  destruct si as [si |]; auto.
  destruct si as [si  lrcpts].
  simpl in *.
  clear IHn.
  
Abort. (* TODO: finish this proof *)

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

