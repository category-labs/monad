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

Definition addrsDelegatedByTx  (tx: TxWithHdr) : list evm.address. Proof. Admitted.

Definition txDelegatesAddr (addr: evm.address) (tx: TxWithHdr) : bool :=
  bool_decide (addr ∈ addrsDelegatedByTx tx).

Opaque txDelegatesAddr.
  

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

Definition indicesOfTx (tx: TxWithHdr): Indices := {| block_index := number (fst tx); tx_index := snd (snd tx) |}.

Definition indLe (l r: Indices):= block_index l  <= block_index r /\ tx_index l <= tx_index r.
Definition indexWithinK (proj: AccountM -> option Indices) (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  let startIndex := {| block_index := number (fst tx) -K ; tx_index := 0 |} in
  match option_bind _ _ proj (state !! (sender tx))  with
  | Some lastSameSenderTx =>
      bool_decide (indLe startIndex lastSameSenderTx /\ indLe lastSameSenderTx (indicesOfTx tx))
  | None => false
  end.

Definition existsTxWithinK (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  indexWithinK lastTxInBlockIndex state tx.

Definition existsDelegatingTxWithinK (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  indexWithinK  lastDelegatedInBlockIndex state tx.

(*
[StateOfAccounts] already stores the [Indices] (block index, tx index) of the the last tx from an account.
[StateOfAccounts] also stores whether an account is delegated: but this is not enough.
[state] may not be the state after the N-K block: it may be a later block in the intermediate stages of the proof.
delegatedAfterNminusK is the set of addresses which have ever been delegated since the N-K block: they will
be treated as delegated even if they got undelegated after that but before [state].


N-K -......- State - intermediateTxsSinceState - tx

delegatedAfterNminus is the txs delegated in ......
*)
Definition isAllowedToEmpty (delegatedAfterNminusK: list evm.address)
  (state : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr)  (tx: TxWithHdr) : bool :=
  let delegated := (addrDelegated state (sender tx))
                   || (bool_decide (sender tx ∈ delegatedAfterNminusK))
                   || existsb (fun txx => (txDelegatesAddr (sender tx) txx)) intermediateTxsSinceState
  in
  let existsSameSenderTxInWindow := (existsTxWithinK state tx) || (existsb (fun txx => bool_decide (sender txx = sender tx)) intermediateTxsSinceState) in
  (negb delegated) && (negb existsSameSenderTxInWindow).

(* duplicate instance. the upstream one picks 1 *)
#[global] Instance inhacc: Inhabited N := populate 0.

(* latestState may be ahread of N-K block in the intermediate stages of the proof *)
Definition maxTotalReserveDippableDebit (delegatedAfterNminusK: list evm.address) (latestState : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr) tx : (N*bool) :=
  if isAllowedToEmpty delegatedAfterNminusK latestState intermediateTxsSinceState tx   then (maxTxFee tx + value tx, true)
  else (maxTxFee tx, false).

    
      
Definition updateKey  {T} `{c: Countable T} {V} {inhv: Inhabited V} (m: gmap T V) (a: T) (f: V -> V) : gmap T V :=
  <[ a :=  f (m !!! a) ]> m.

Lemma updateKeyLkp3  {T} `{c: Countable T} {V} {inhv: Inhabited V} (m: gmap T V) (a b: T) (f: V -> V) :
  (updateKey m a f) !!! b = if (bool_decide (a=b)) then (f (m !!! a)) else m !!! b.
Proof using.
  unfold lookup_total.
  unfold map_lookup_total.
  unfold default.
  unfold updateKey.
  autorewrite with syntactic;[| exact inhabitant].
  case_bool_decide; auto.
Qed.

Lemma updateKeyLkp  {T} `{c: Countable T} {V} {inhv: Inhabited V} (m: gmap T V) (a: T) (f: V -> V) :
  updateKey m a f !! a = Some (f (m !!! a)).
Proof using.
  unfold updateKey.
  autorewrite with syntactic; [| exact inhabitant].
  case_bool_decide; try congruence.
Qed.


(*
Fixpoint maxTotalReserveDippableDebitLold (knownBlocks: gmap N Block) (latestKnownState : StateOfAccounts) (postStateAccountedSuffix rest: list TxWithHdr) (a: evm.address) : N:=
   match rest with
  | [] => 0
   | h::tl =>
      (maxTotalReserveDippableDebitLold knownBlocks latestKnownState (postStateAccountedSuffix++[h]) tl a)
      + (if bool_decide (sender h = a)
         then (maxTotalReserveDippableDebit knownBlocks latestKnownState postStateAccountedSuffix h)
         else 0)
   end.
 *)

Definition updateTots (upd: N*bool) (old: (N*option N)) : N*option N :=
  let '(fees, allowedToEmpty) := upd in
  if allowedToEmpty then
    (fst old, Some fees)
  else (fst old+fees, snd old).

Fixpoint maxTotalReserveDippableDebitL (delegatedAfterNminusK: list evm.address) (latestState : StateOfAccounts) (postStateAccountedSuffix rest: list TxWithHdr) : gmap evm.address (N*option N) :=
  match rest with
  | [] => ∅
  | h::tl =>
      let r := maxTotalReserveDippableDebitL (delegatedAfterNminusK ++ addrsDelegatedByTx h) latestState (postStateAccountedSuffix++[h]) tl in
      updateKey r (sender h) (updateTots
                                (maxTotalReserveDippableDebit delegatedAfterNminusK latestState postStateAccountedSuffix h))
  end.

(*
Definition consensusAcceptableTxGold (knownBlocks: gmap N Block) (latestKnownState : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr) (candidate : TxWithHdr) : bool :=
  if isAllowedToEmpty knownBlocks latestKnownState intermediateTxsSinceState candidate
  then bool_decide (maxTxFee candidate <= balanceOfAc latestKnownState (sender candidate))
  else
    bool_decide (maxTotalReserveDippableDebitLold knownBlocks latestKnownState [] intermediateTxsSinceState (sender candidate)
                 <= balanceOfAc latestKnownState (sender candidate)).
*)

Definition consensusAcceptableTxs (delegatedAfterNminusKBeforeLatestState: list evm.address) (latestState : StateOfAccounts) (postStateSuffix: list TxWithHdr) : Prop :=
  let totDebits := maxTotalReserveDippableDebitL delegatedAfterNminusKBeforeLatestState latestState [] postStateSuffix in
  forall ac,
    let '(nonEmptyingDebits, emptyingDebits) := totDebits !!! ac in
    match emptyingDebits with
    | None => nonEmptyingDebits <= (ReserveBal `min` (balanceOfAc latestState ac))
    | Some emptyingDebit =>
        emptyingDebit <= balanceOfAc latestState ac  /\
          nonEmptyingDebits <= (ReserveBal `min` (balanceOfAc latestState ac - emptyingDebit))
    end.

(*
Definition consensusAcceptableTx  (stateNminusK : StateOfAccounts) (candidate : TxWithHdr) : bool :=
  let NminusK := (txBlockNum candidate - K) in
  let intermediate := (intermediateTxs knownBlocks NminusK candidate) in 
  consensusAcceptableTxG knownBlocks stateNminusK intermediate candidate.
*)
Definition consensusAcceptableBlock (knownBlocks: gmap N Block) (stateNminusK : StateOfAccounts) (blockIndex : N) : Prop :=
  let extension := (flat_map transactions (blocksInRange knownBlocks (blockIndex - K) K)) in
  consensusAcceptableTxs [] stateNminusK  extension.

(*
Definition consensusAcceptableBlocks (knownBlocks: gmap N Block) (knownStates: gmap N StateOfAccounts)
  (proposedChainExtension: list Block) : bool :=
  forallb (fun b => consensusAcceptableBlock knownBlocks (knownStates !!! (number (header b) - K)) b) proposedChainExtension.
*)

Definition allAccounts: list evm.address. Proof. Admitted. (* define it opaquely with Qed: never unfold *)

Definition stateAfterTransaction s (t: TxWithHdr) :=
  let '(hdr, (tx, txindex)) := t in 
  let (si, r) := stateAfterTransactionAux hdr s (N.to_nat txindex) tx in
  (applyGasRefundsAndRewards hdr si r, r).

Definition DippedTooMuchIntoReserve (t: TxWithHdr): TransactionResult. Proof. Admitted.

Definition addrConsideredDelegated  (state: evm.GlobalState) (tx : TxWithHdr) : bool :=
  (addrDelegated state (sender tx))
                   || (bool_decide (sender tx ∈ addrsDelegatedByTx tx))
                   || existsDelegatingTxWithinK state tx.
Definition isAllowedToEmptyExec
  (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  (negb (addrConsideredDelegated state tx)) && (negb (existsTxWithinK state tx)).

Definition execTxAfterValidationV2  (s: evm.GlobalState) (t: TxWithHdr)
  : (evm.GlobalState * TransactionResult) :=
  let (si, r) := stateAfterTransaction s t in
  let balCheck (a: evm.address) :=
    let erb:N := ReserveBal `min` (balanceOfAc s a) in
    bool_decide (erb  - (if bool_decide (sender t =a ) then maxTxFee t else 0) <= balanceOfAc si a) in
  let allBalCheck := (forallb balCheck allAccounts) in
  if (isAllowedToEmptyExec s t || allBalCheck)
  then (si, r)
  else (updateBalanceOfAc s (sender t) (fun oldBal => oldBal - maxTxFee t),  DippedTooMuchIntoReserve t) (* revert tx *).

Definition validateTx (preTxState: StateOfAccounts) (t: TxWithHdr): bool :=
   bool_decide (maxTxFee t  <= balanceOfAc preTxState (sender t))%N.

Definition stateAfterTransactionV2 (s: StateOfAccounts) (t: TxWithHdr): option (StateOfAccounts * TransactionResult) :=
  if (negb (validateTx s t)) (* if this fails. the execution of the entire block aborts *)
  then None
  else Some (execTxAfterValidationV2  s t).

Fixpoint stateAfterTransactionsV2  (s: StateOfAccounts) (ts: list TxWithHdr): option (StateOfAccounts * list TransactionResult) :=
  match ts with
  | [] => Some (s, [])
  | t::tls =>
      match stateAfterTransactionV2 s t with
      | Some (si, r)=>
          match stateAfterTransactionsV2 si tls with
          | Some (sf, lr)=> Some (sf, r::lr)
          | None => None
          end
      | None => None
      end
  end.

(*
Lemma isEmptyingEq (knownBlocks: gmap N Block) (s1 s2 : StateOfAccounts) n tx :
  (forall a, addrDelegated s1 a = addrDelegated s2 a)
  -> isAllowedToEmpty s1 n tx =  isAllowedToEmpty knownBlocks s2 n tx.
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
  -> maxTotalReserveDippableDebitLold knownBlocks s1 accountedSuffix unaccountedSuffix (sender candidate)
     = maxTotalReserveDippableDebitLold knownBlocks s2 accountedSuffix unaccountedSuffix (sender candidate).
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
  -> consensusAcceptableTxGold knownBlocks s1 intermediate candidate = true
  -> consensusAcceptableTxGold knownBlocks s2 intermediate candidate = true.
Proof.
  intros Hb Hd Hc.
  unfold consensusAcceptableTxGold in *.
  specialize (Hb (sender candidate)).
  rewrite -> isEmptyingEq with (s2:=s1) by auto.
  case_match; rewrite -> bool_decide_eq_true in *; try lia;[].
  rewrite -> maxTotalReserveDippableDebitLeq with (s2:=s1) by auto.
  lia.
Qed.
Print Assumptions consensusAcceptableTxGmono.
*)

Hint Rewrite -> bool_decide_eq_true : iff.
Require Import monad.proofs.bigauto.
(*
Lemma updateKeyLkp2  {T} `{c: Countable T} (m: gmap T N) (a: T) (f: N -> N) :
  lookupN (updateKey m a f) a =  (f (lookupN m a)).
Proof using.
  unfold lookupN.
  rewrite updateKeyLkp.
  reflexivity.
Qed.
*)

Open Scope N_scope.


Lemma execLcore knownBlocks tx s:
  let '(sf, r) :=  execTxAfterValidationV2 s tx in
  (forall ac, (ac <> sender tx) ->
             ReserveBal `min` (balanceOfAc s ac) <= (balanceOfAc sf ac))
  /\
  (if isAllowedToEmpty knownBlocks s [] tx
  then True
  else ReserveBal `min` (balanceOfAc s (sender tx)) - maxTxFee tx <= (balanceOfAc sf (sender tx)))
  /\
  (forall ac, addrDelegated sf ac <-> addrDelegated s ac || bool_decide (ac ∈ (addrsDelegatedByTx tx)))
  /\
  (forall ac, ac <> sender tx
                             
              -> if (addrDelegated sf ac)
                 then True
                 else balanceOfAc s ac <= balanceOfAc sf ac).
Proof using.
Admitted.

Hint Rewrite Z.min_l  using lia: syntactic.      
Hint Rewrite Z.min_r  using lia: syntactic.      
Hint Rewrite N.min_l  using lia: syntactic.      
Hint Rewrite N.min_r  using lia: syntactic.      

Lemma debitLeq dOverrides acc extension s sf tx rest: (maxTotalReserveDippableDebitL dOverrides sf rest extension) !!! acc = (maxTotalReserveDippableDebitL dOverrides s (tx::rest) extension) !!! acc.
Proof using.
  revert dOverrides.
  induction extension; auto;[].
  intros.
  simpl.
Abort.

Lemma ite_fequiv {T} (t1 t2 e1 e2:T) (b1 b2: bool) :
  b1=b2 -> t1=t2 -> e1=e2 -> (if b1 then t1 else e1) = if b2 then t2 else e2.
Proof using.
  intros. subst. reflexivity.
Qed.

Lemma debitLeq dOverrides extension s sf tx rest:
  (maxTotalReserveDippableDebitL dOverrides sf rest extension)
  = (maxTotalReserveDippableDebitL dOverrides s (tx::rest) extension).
Proof using.
  revert dOverrides.
  revert rest.
  induction extension; auto;[].
  intros.
  simpl.
  rewrite IHextension.
  f_equiv.
  f_equiv.
  unfold maxTotalReserveDippableDebit.
  apply ite_fequiv; try reflexivity.
  unfold isAllowedToEmpty.
  simpl. f_equiv.
Admitted. (* seems easy *)

#[global] Instance inhadd: Inhabited evm.address := populate word160.word160_default.
Lemma moveForallIn {T} {inh:Inhabited T} P (Q: T -> Prop):
  (forall x, P /\ Q x)  -> P /\ forall x, Q x.
Proof using.
  intros Hp.
  firstorder.
Qed.
  Hint Rewrite bool_decide_spec: iff.

Lemma execL dOverrides tx extension s:
  consensusAcceptableTxs dOverrides s
    (tx::extension)
  -> consensusAcceptableTxs (dOverrides ++ (addrsDelegatedByTx tx)) (fst (execTxAfterValidationV2  s tx)) extension.
Proof using.
  pose proof (execLcore dOverrides tx s) as Hcore.
  remember (execTxAfterValidationV2 s tx) as ss.
  destruct ss as [sf  res].
  intros Hc.
  unfold consensusAcceptableTxs in *.
  simpl in *.
  intros ac.
  specialize (Hc ac).
  forward_reason.
  rewrite updateKeyLkp3 in Hc.
  assert (forall acc, (maxTotalReserveDippableDebitL (dOverrides ++ addrsDelegatedByTx tx) sf [] extension) !!! acc = (maxTotalReserveDippableDebitL (dOverrides ++ addrsDelegatedByTx tx) s [tx] extension) !!! acc
         ) as Hass.
  { intros. rewrite -> debitLeq with (s:=s) (tx:=tx). reflexivity.}
  specialize (Hass ac).
  autorewrite with iff.
  case_bool_decide; simpl in *;  try lia.
  2:{ (* non-sender account *)
    specialize (Hcorel ac ltac:(auto)).
    specialize (Hcorerrr ac ltac:(auto)).
    rewrite Hass.
    clear Hass.
    remember (addrDelegated sf ac) as dg.
    destruct dg.
    2:{ (* ac is not delegated *)
       revert Hc.
       rwHypsP.
       utils.case_match_concl.
       destruct o; try lia.
    }
    {
      remember (maxTotalReserveDippableDebitL (dOverrides ++ addrsDelegatedByTx tx) s [tx] extension !!! ac) as rd.
      destruct rd as [nonEmptyingDebits emptyingDebits].
      simpl in *.
      (* ac is delegated => isEmptying false for the ENTIRE extension, even if some tx in it undelegates: *)
      assert (emptyingDebits = None) as Heq by admit.
      revert Hc.
      rwHypsP.
      intros.
      lia.
    }
  }
  { (* sender's account *)
    subst.
    rewrite Hass.
    clear Hass.
    unfold maxTotalReserveDippableDebit in Hc.
    remember (isAllowedToEmpty dOverrides s [] tx) as ae.
    remember (maxTotalReserveDippableDebitL (dOverrides ++ addrsDelegatedByTx tx) s [tx] extension !!! (sender tx)) as rd.
    destruct rd as [nonEmptyingDebits emptyingDebits].
    (* later transactions from the same sender cannot be emptying, assuming the extension spans K or fewer blocks *)
    assert (emptyingDebits = None) as Heq by admit.
    rwHypsP.
    destruct ae; simpl in *; try lia;[|].
    {
      (* meaning sender tx is not delegated, so this tx can only decrement the balance by ( maxTxFee tx + value tx) *)
      assert (balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - ( maxTxFee tx + value tx)) as Hle by admit.
      revert Hc.
      rwHypsP.
      intros.
      simpl in *.
      lia.
    }
    
    {
      revert Hc.
      rwHypsP.
      lia.
    }
  }
  
Admitted.


Lemma execValidate dOverrides tx extension s:
  consensusAcceptableTxs dOverrides s
    (tx::extension)
  -> validateTx s tx = true.
Proof using.
  intros Hc.
  unfold consensusAcceptableTxs in *.
  specialize (Hc (sender tx)).
  simpl in *.
  unfold maxTotalReserveDippableDebit in Hc. (* rename [ maxTotalReserveDippableDebit] to reserveBal decrement *)
  simpl.
  unfold updateTots in Hc.
  simpl.
  autorewrite with syntactic in Hc.
  rewrite updateKeyLkp3 in Hc.
  resolveDecide ltac:(congruence).
  unfold validateTx.
  autorewrite with iff.
  destruct (isAllowedToEmpty dOverrides s [] tx); simpl in *; try lia;[].
  case_match; try lia.
Qed.
  

Lemma inductiveStep (knownBlocks: gmap N Block) (latestState : StateOfAccounts) (intermediateHd: TxWithHdr) (intermediateTl: list TxWithHdr) :
  consensusAcceptableTxG knownBlocks latestState (intermediateHd::intermediateTl)
  -> match stateAfterTransactionV2 knownBlocks latestState intermediateHd with
     | None =>  False
     | Some (si, tr) =>
         consensusAcceptableTxG knownBlocks si intermediateTl
     end.
Proof.
  intros Hc.
  pose proof  (Hc (sender intermediateHd)) as Hcs.
  simpl in Hcs.
  rewrite updateKeyLkp2 in Hcs.
  unfold stateAfterTransactionV2.
  unfold validateTx.
  unfold maxTotalReserveDippableDebit in Hcs.
  case_bool_decide; simpl in *; try lia;[].
  unfold consensusAcceptableTxG.
  pose proof (execL knownBlocks intermediateHd intermediateTl latestState) as Hp.
  remember (execTxAfterValidationV2 knownBlocks latestState intermediateHd) as ss.
  destruct ss as [si  res].
  simpl in *.
  apply Hp.
  assumption.
Qed.
  
  
  
  unfold execTxAfterValidationV2.
  remember (stateAfterTransaction latestState intermediateHd) as ss.
  simpl.
  match goal with
    [|- context[ ?l || ?r ]] =>
      remember (l || r) as lr
  end.
  destruct lr.
  { (* no revert *)
    unfold consensusAcceptableTxG.
    intros ac.
    pose proof (Hc ac) as Hca.
    simpl in Hca.
    max
    
    up
  

      
  
  updateKey
  case_match.
  2:{ (*candidate not allowed to empty *)
    unfold stateAfterTransactionV2.
    simpl in Hc.
    autorewrite with iff in Hc.
    miscPure.forward_reason.
    case_bool_decide.
    { (* sender intermediateHd = sender candidate *)
      unfold maxTotalReserveDippableDebit in Hc.
      unfold validateTx.
      rwHypsP.
      case_bool_decide; simpl in *; try lia;[].
      unfold execTxAfterValidationV2.
      remember (stateAfterTransaction latestState intermediateHd) as ss.
      destruct ss as [si  res].
      simpl in *.
      match goal with
        [|- context[ ?l || ?r ]] =>
          remember (l || r) as lr
      end.
      destruct lr.
      { (* no revert *)
        unfold consensusAcceptableTxG.
        
        
       
                       
      remember (isAllowedToEmptyLatestState knownBlocks latestState intermediateHd) as allow.
      destruct allow; simpl in *.
      {
        unfold consensusAcceptableTxG.
        orient_rwHyps.
        assert (isAllowedToEmpty knownBlocks si intermediateTl candidate = false)as Heq.
        {
          revert Heqallow Heqss H.
          intros.
          unfold isAllowedToEmpty in *.
          unfold isAllowedToEmptyLatestState in *.
          revert Heqallow.
          orient_rwHyps.
          intros.
          Locate btauto.
          Btauto.btauto.
        Forward.rwHyps.
        Locate rwHyps.

        unfold isAllowedToEmptyLatestState in *.
        unfold isAllowedToEmpty in *.
        
      case_match.
      {
        
      remember_destruct
      simpl.
      Lemma allowedEmptyEq:
    isAllowedToEmptyLatestState knownBlocks latestState intermediateHd 
        isAllowedToEmpty knownBlocks latestState (intermediateHd :: intermediateTl) candidate
    rewrite 
      
  {
    unfold stateAfterTransactionV2.
    
    

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

