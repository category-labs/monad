(* proofs about reserve balances:
- consensus guarnatees when it sends a block for executions
- what consensus assumes execution guarantees
- how those guarantees ensure execution will never run into a chase when an account has insufficient balance to pay gas fees
 *)
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.misc.
Require Import bluerock.hw_models.utils.
(*
Require Import bluerock.auto.rwdb.
Require Import bluerock.auto.miscPure.
*)
Require Import monad.proofs.bigauto.
Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.

Require Import bluerock.auto.cpp.tactics4.
Open Scope N_scope.

Definition addrDelegated  (s: evm.GlobalState) (a : evm.address) : bool. Proof. Admitted.

Definition TxWithHdr : Type := BlockHeader * (Transaction * N).

(* only gas fees. does not include value transfers *)
Definition maxTxFee (t: TxWithHdr) : N. Proof. Admitted.

Definition staticReserveBal : N. Proof. Admitted.


Definition sender (t: TxWithHdr): evm.address := sender (fst (snd t)).
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value (fst (snd t))).

Definition K : N. Proof. Admitted.

Definition addrsDelUndelByTx  (tx: TxWithHdr) : list evm.address. Proof. Admitted.

Definition txDelUndelAddr (addr: evm.address) (tx: TxWithHdr) : bool :=
  bool_decide (addr ∈ addrsDelUndelByTx tx).


Opaque txDelUndelAddr.

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

(*
Definition intermediateTxs (knownBlocks: gmap N Block) (stateBlockIndex: N) (tx: TxWithHdr) :=
  let txBlock := knownBlocks !!! (txBlockNum tx) in
  let prevTxsInSameBlock := (firstn (N.to_nat (txIndexInBlock tx)) (transactions txBlock)) in
   prevTxsInSameBlock ++ (flat_map transactions (blocksInRange knownBlocks (txBlockNum tx - K) (K-1))).

Definition emptyingCheckRange (knownBlocks: gmap N Block) (tx: TxWithHdr) :=
  let txBlock := knownBlocks !!! (txBlockNum tx) in
  let prevTxsInSameBlock := (firstn (N.to_nat (txIndexInBlock tx)) (transactions txBlock)) in
  ((flat_map transactions (blocksInRange knownBlocks (txBlockNum tx - K) (K-1)))
                                                                 ++  prevTxsInSameBlock).
*)
Definition indicesOfTx (tx: TxWithHdr): Indices := {| block_index := txBlockNum tx; tx_index := snd (snd tx) |}.

Definition indLe (l r: Indices):= block_index l  <= block_index r /\ tx_index l <= tx_index r.
Definition indexWithinK (proj: AccountM -> option N) (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  let startIndex :=  txBlockNum tx -K  in
  match option_bind _ _ proj (state !! (sender tx))  with
  | Some lastSameSenderTx =>
      bool_decide (startIndex <= lastSameSenderTx /\  lastSameSenderTx <= txBlockNum tx)
  | None => false
  end.

Definition existsTxWithinK (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  indexWithinK lastTxInBlockIndex state tx.

Definition existsDelUndelTxWithinK (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  indexWithinK  lastDelUndelInBlockIndex state tx.

(*
[StateOfAccounts] already stores the [Indices] (block index, tx index) of the the last tx from an account.
[StateOfAccounts] also stores whether an account is delegated: but this is not enough. it now also stores the block index of the last delegation requuest for each account.

[state] may not be the state after the N-K block: it may be a later block in the intermediate stages of the proof.
 *)

(*
S : n-k
t n-k+1
*)

(* external assumption: tx::intermediateTxsSinceState does not span more than K blocks *)
Definition isAllowedToEmpty
  (state : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr)  (tx: TxWithHdr) : bool :=
  let delegated := (addrDelegated state (sender tx))
                   || existsDelUndelTxWithinK state tx
                   || bool_decide  ((sender tx) ∈ flat_map addrsDelUndelByTx (tx::intermediateTxsSinceState))
  in
  let existsSameSenderTxInWindow :=
    (existsTxWithinK state tx)
    || bool_decide ((sender tx) ∈ map sender intermediateTxsSinceState) in
  (negb delegated) && (negb existsSameSenderTxInWindow).

(* duplicate instance. the upstream one picks 1 *)
#[global] Instance inhacc: Inhabited N := populate 0.


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

(*
Lemma updateKeyLkp4  {T} `{c: Countable T} {V} {inhv: Inhabited V} (m: gmap T V) (a b: T) (f: V -> V) :
  (updateKey m a f) !! b = if (bool_decide (a=b)) then option_map f  (m !! a) else m !! b.
Proof using.
  unfold updateKey.
  autorewrite with syntactic;[| exact inhabitant].
  case_bool_decide; auto.
  reflexivity.
Qed.
 *)

(*
Lemma updateKeyLkp  {T} `{c: Countable T} {V} {inhv: Inhabited V} (m: gmap T V) (a: T) (f: V -> V) :
  updateKey m a f !! a = Some (f (m !!! a)).
Proof using.
  unfold updateKey.
  autorewrite with syntactic; [| exact inhabitant].
  reflexivity.
Qed.

 *)

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
Definition updateTots (upd: N*bool) (old: (N*option (N*N))) : N*option (N*N) :=
  let '(fees, allowedToEmpty) := upd in
  if allowedToEmpty then
    (fst old, Some fees)
  else (fst old+fees, snd old).
 *)


(* weakening to 1 tx *)

Definition updateTotals (latestState : StateOfAccounts) (intermediates: list TxWithHdr) next (old: (N*option (N*N)))
  : N*option (N*N) :=
  if isAllowedToEmpty latestState intermediates next
  then (old.1, Some (maxTxFee next,  value next))
  else (old.1 + maxTxFee next, old.2).

Fixpoint maxTotalReserveDippableDebitL (latestState : StateOfAccounts) (postStateAccountedSuffix rest: list TxWithHdr)
  : gmap evm.address (N*option (N*N)) :=
  match rest with
  | [] => ∅
  | h::tl =>
      let r : gmap evm.address (N*option (N*N))
        := maxTotalReserveDippableDebitL latestState (postStateAccountedSuffix++[h]) tl in
      updateKey r (sender h) (updateTotals latestState postStateAccountedSuffix h)
  end.

(* this is a somewhat non-constructive assumption. we need that no contract ever deployed at any address in this set. We must keep this set abstract. Also, because the addresses of new contracts is prododuced by keccak,
we need to keep the keccak function abstract and not make contradicting assumptions, e.g. that keccak is surjective. perhaps we can morally treat the implenentation as something that emits a 0 whenever the actual output is in allEOAsWithPrivateKeyThatWillEvenBeGenerated *)
Definition allEOAsWithPrivateKeyThatWillEvenBeGenerated: list evm.address. Proof. Admitted.


Lemma maxTotalReserveDippableDebitLPos  (latestState : StateOfAccounts) (postStateAccountedSuffix rest: list TxWithHdr) addr:
  addr  ∉ (map sender rest)
  -> ((maxTotalReserveDippableDebitL latestState postStateAccountedSuffix rest) !!! addr) = (0, None).
Proof using.
  revert postStateAccountedSuffix.
  induction rest; auto.
  intros.
  simpl in *.
  rewrite updateKeyLkp3.
  rewrite bool_decide_false;[ | set_solver].
  apply IHrest. set_solver.
Qed.

(*
Lemma foo a l s r:
  maxTotalReserveDippableDebitL l s (a::r) = ∅.
Proof using.
  simpl.
  unfold maxTotalReserveDippableDebit.
  unfold updateTots.
*)

(*
Definition consensusAcceptableTxGold (knownBlocks: gmap N Block) (latestKnownState : StateOfAccounts) (intermediateTxsSinceState: list TxWithHdr) (candidate : TxWithHdr) : bool :=
  if isAllowedToEmpty knownBlocks latestKnownState intermediateTxsSinceState candidate
  then bool_decide (maxTxFee candidate <= balanceOfAc latestKnownState (sender candidate))
  else
    bool_decide (maxTotalReserveDippableDebitLold knownBlocks latestKnownState [] intermediateTxsSinceState (sender candidate)
                 <= balanceOfAc latestKnownState (sender candidate)).
*)

Definition consensusAcceptableTxs (latestState : StateOfAccounts) (postStateSuffix: list TxWithHdr) : Prop :=
  let totDebits := maxTotalReserveDippableDebitL latestState [] postStateSuffix in
  forall ac, (* currently, smart contracts cannot empty beyond reserve. to fix, we can add an isEOA hypothesis but it is tricky to define that precisely in a moving state *)
    let '(nonEmptyingDebits, emptyingDebits) := totDebits !!! ac in
    match emptyingDebits with
    | None => nonEmptyingDebits <= (ReserveBal `min` (balanceOfAc latestState ac))
    | Some (emptyingFee, emptyingValue) =>
          emptyingFee <= balanceOfAc latestState ac  /\
          nonEmptyingDebits <= (ReserveBal `min` (balanceOfAc latestState ac - (emptyingValue+emptyingFee)))
    end.

Definition consensusAcceptableTxsNoMinus (latestState : StateOfAccounts) (postStateSuffix: list TxWithHdr) : Prop :=
  let totDebits := maxTotalReserveDippableDebitL latestState [] postStateSuffix in
  forall ac, (* currently, smart contracts cannot empty beyond reserve. to fix, we can add an isEOA hypothesis but it is tricky to define that precisely in a moving state *)
    let '(nonEmptyingDebits, emptyingDebits) := totDebits !!! ac in
    match emptyingDebits with
    | None => nonEmptyingDebits <= (ReserveBal `min` (balanceOfAc latestState ac))
    | Some (emptyingFee, emptyingValue) =>
        let willRevert := bool_decide (balanceOfAc latestState ac < emptyingValue+emptyingFee) in
          emptyingFee <= balanceOfAc latestState ac 
          /\ nonEmptyingDebits <= ReserveBal
          /\ nonEmptyingDebits + (emptyingFee + if willRevert then 0 else emptyingValue)
             <= (balanceOfAc latestState ac)
    end.


Lemma catxEquiv (latestState : StateOfAccounts) (postStateSuffix: list TxWithHdr):
  consensusAcceptableTxs latestState postStateSuffix
  -> consensusAcceptableTxsNoMinus latestState postStateSuffix.
Proof using.
  unfold consensusAcceptableTxsNoMinus.
  intros Hp ac.
  specialize (Hp ac).
  case_match.
  destruct o; auto.
  destruct p as [emptyingFee emptyingValue]; auto.
  forward_reason.
  split_and; try lia.
  forward_reason.
  case_bool_decide; try
  lia.
Qed.


Lemma catxEquiv2 (latestState : StateOfAccounts) (postStateSuffix: list TxWithHdr):
  consensusAcceptableTxsNoMinus latestState postStateSuffix
  -> consensusAcceptableTxs latestState postStateSuffix.
Proof using.
  unfold consensusAcceptableTxsNoMinus ,consensusAcceptableTxs.
  intros Hp ac.
  specialize (Hp ac).
  case_match.
  destruct o; auto.
  destruct p as [emptyingFee emptyingValue]; auto.
  forward_reason.
  split_and; try lia.
  rewrite N.min_glb_iff.
  forward_reason.
  case_bool_decide; try
                      lia.
  split_and; try lia.
  (* not provable: consensusAcceptableTxs is too strong, unnecessarily *)
Abort.

(*
Definition consensusAcceptableTx  (stateNminusK : StateOfAccounts) (candidate : TxWithHdr) : bool :=
  let NminusK := (txBlockNum candidate - K) in
  let intermediate := (intermediateTxs knownBlocks NminusK candidate) in
  consensusAcceptableTxG knownBlocks stateNminusK intermediate candidate.
*)
Definition consensusAcceptableBlock (knownBlocks: gmap N Block) (stateNminusK : StateOfAccounts) (blockIndex : N) : Prop :=
  let extension := (flat_map transactions (blocksInRange knownBlocks (blockIndex - K) K)) in
  consensusAcceptableTxs stateNminusK  extension.

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
                   || (bool_decide (sender tx ∈ addrsDelUndelByTx tx))
                   || existsDelUndelTxWithinK state tx.
Definition isAllowedToEmptyExec
  (state : StateOfAccounts)  (tx: TxWithHdr) : bool :=
  isAllowedToEmpty state [] tx.

Definition execValidatedTx  (s: evm.GlobalState) (t: TxWithHdr)
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

Definition execTx (s: StateOfAccounts) (t: TxWithHdr): option (StateOfAccounts * TransactionResult) :=
  if (negb (validateTx s t)) (* if this fails. the execution of the entire block aborts *)
  then None
  else Some (execValidatedTx  s t).

Fixpoint execTxs  (s: StateOfAccounts) (ts: list TxWithHdr): option (StateOfAccounts * list TransactionResult) :=
  match ts with
  | [] => Some (s, [])
  | t::tls =>
      match execTx s t with
      | Some (si, r)=>
          match execTxs si tls with
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
(*
Lemma updateKeyLkp2  {T} `{c: Countable T} (m: gmap T N) (a: T) (f: N -> N) :
  lookupN (updateKey m a f) a =  (f (lookupN m a)).
Proof using.
  unfold lookupN.
  rewrite updateKeyLkp.
  reflexivity.
Qed.
*)

Definition hasCode (s: StateOfAccounts) (addr: evm.address): bool. Proof. Admitted.

(** execution assumptions *)
Lemma execTxOtherBalanceLB tx s:
  let sf :=  (execValidatedTx s tx).1 in
  (forall ac,
      (ac <> sender tx)
       -> if (hasCode s ac)
          then True
          else ReserveBal `min` (balanceOfAc s ac) <= (balanceOfAc sf ac)).
Proof. Admitted.

(* TODO: do the more liberal check and then weaken the then case to inequality *)
Lemma execTxSenderBal tx s:
  let sf :=  (execValidatedTx s tx).1 in
  (if isAllowedToEmpty s [] tx
  then balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - ( maxTxFee tx + value tx)
  else ReserveBal `min` (balanceOfAc s (sender tx)) - maxTxFee tx <= (balanceOfAc sf (sender tx))).
Proof. Admitted.

Lemma execTxDelegationUpd tx s:
  let sf :=  (execValidatedTx s tx).1 in
  (forall ac, addrDelegated sf ac  -> addrDelegated s ac || bool_decide (ac ∈ (addrsDelUndelByTx tx))).
Proof. Admitted.

Lemma execTxCannotDebitNonDelegatedNonContractAccounts tx s:
  let sf :=  (execValidatedTx s tx).1 in
  (forall ac, ac <> sender tx
              -> if (addrDelegated sf ac || hasCode sf ac)
                 then True
                 else balanceOfAc s ac <= balanceOfAc sf ac).
Proof using. Admitted.

Lemma lastTxInBlockIndexUpd s txlast:
  option_bind _ _ lastTxInBlockIndex ((execValidatedTx s txlast).1 !! sender txlast)
  = Some (txBlockNum txlast).
Proof using. Admitted.

Lemma otherTxLstSenderLkp s addr txlast :
  addr <> sender txlast
  ->
    option_bind _ _ lastTxInBlockIndex ((execValidatedTx s txlast).1 !! addr)
    = option_bind _ _ lastTxInBlockIndex (s !! addr).
Proof. Admitted.


Lemma delgUndelgUpdTx txlast s addr:
  addr ∈  addrsDelUndelByTx txlast
  -> option_bind _ _ lastDelUndelInBlockIndex ((execValidatedTx s txlast).1 !! addr) = Some (txBlockNum txlast).
Proof using. Admitted.

Lemma otherDelUndelLkp s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    option_bind _ _ lastDelUndelInBlockIndex ((execValidatedTx s txlast).1 !! addr)
    = option_bind _ _ lastDelUndelInBlockIndex (s !! addr).
Proof. Admitted.

Lemma otherDelUndelDelegationStatusUnchanged s addr txlast :
  addr ∉ addrsDelUndelByTx txlast
  ->
    addrDelegated (execValidatedTx s txlast).1 addr
    = addrDelegated s addr.
Proof using. Admitted.

Hint Rewrite Z.min_l  using lia: syntactic.
Hint Rewrite Z.min_r  using lia: syntactic.
Hint Rewrite N.min_l  using lia: syntactic.
Hint Rewrite N.min_r  using lia: syntactic.


Lemma ite_fequiv {T} (t1 t2 e1 e2:T) (b1 b2: bool) :
  b1=b2 -> t1=t2 -> e1=e2 -> (if b1 then t1 else e1) = if b2 then t2 else e2.
Proof using.
  intros. subst. reflexivity.
Qed.

(* technically, the lemma is unprobable, however, we can prove a Proper lemma about the context *)
Lemma gmapEquiv {T} `{c: Countable T} {V} {inhv: Inhabited V} (m1 m2: gmap T V) :
  (forall a, m1 !!! a = m2 !!! a) -> m1 =m2.
Proof. Admitted.

Hint Rewrite @elem_of_cons: syntactic.

Set Nested Proofs Allowed.


Lemma isAllowedToEmpty2 s txlast rest txnext:
  let sf :=  fst (execValidatedTx s txlast) in 
  txBlockNum txnext - K ≤ txBlockNum txlast ≤ txBlockNum txnext
  -> isAllowedToEmpty sf rest txnext = isAllowedToEmpty s (txlast :: rest) txnext.
Proof using.
  intros ? Hr.
  unfold isAllowedToEmpty.
  simpl.
  autorewrite with syntactic.
  destruct (decide (sender txnext = sender txlast)).
  {
    assert ((bool_decide (sender txnext ∈ sender txlast :: map sender rest)) = true) as Hf.
    {
      rewrite bool_decide_true; auto.
      set_solver.
    }

    rewrite Hf.
    autorewrite with syntactic.
    match goal with
    |  |-  _ && ?r = false =>
         assert (r=false) as Hrf
    end;
    [|  rewrite Hrf; autorewrite with syntactic; reflexivity].
    unfold existsTxWithinK.
    unfold indexWithinK.
    rwHypsP.
    rewrite lastTxInBlockIndexUpd.
    rewrite bool_decide_true;[reflexivity|].
    split_and !; try lia.
  }
  {
    f_equiv.
    2:{
      f_equiv.
      f_equiv.
      2:{
        apply bool_decide_ext.
        autorewrite with syntactic.
        tauto.
      }
      {
        unfold existsTxWithinK.
        unfold indexWithinK.
        subst sf.
        rewrite otherTxLstSenderLkp; auto.
      }
    }
    {
      destruct (decide (sender txnext ∈ addrsDelUndelByTx txlast)).
      {
        symmetry.
          Hint Rewrite @elem_of_app: iff.
        rewrite bool_decide_true;
          [ | autorewrite with iff; tauto].
        autorewrite with syntactic; simpl.
        unfold existsDelUndelTxWithinK.
        unfold indexWithinK.
        rewrite delgUndelgUpdTx; auto;[].
        resolveDecide lia.
        autorewrite with syntactic.
        reflexivity.
      }
      {
        f_equiv.
        f_equiv;[
            |apply bool_decide_ext;
             autorewrite with iff; tauto].
        unfold existsDelUndelTxWithinK.
        unfold indexWithinK.
        rewrite otherDelUndelLkp; auto.
        f_equiv.
      
        apply otherDelUndelDelegationStatusUnchanged; auto.
      }

    }
  }
Qed.

Lemma forallCons {T} (P : T -> Prop) (l: list T) (h:T):
  (forall t, t ∈ (h::l) -> P t)
  -> (P h  /\ forall t, t ∈ l -> P t).
Proof using.
  intros Hp.
  pose proof (Hp h) as Hd.
  autorewrite with iff in *.
  split.
  - apply Hd. left. reflexivity.
  - intros. apply Hp. autorewrite with iff. right. assumption.
Qed.
  
  
Lemma debitLeq extension s tx rest:
  let sf :=  fst (execValidatedTx s tx) in 
  (forall txext, txext ∈ extension ->  txBlockNum txext - K ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (maxTotalReserveDippableDebitL  sf rest extension)
  = (maxTotalReserveDippableDebitL  s (tx::rest) extension).
Proof using.
  hnf.
  revert rest.
  induction extension; auto;[].
  intros ? Hr.
  apply forallCons in Hr.
  forward_reason.
  simpl.
  rewrite IHextension; try assumption;[].
  apply gmapEquiv.
  intros ad.
  repeat rewrite updateKeyLkp3.
  case_bool_decide; auto;[].
  unfold updateTotals.
  simpl.
  apply ite_fequiv; try reflexivity.
  apply isAllowedToEmpty2.
  split; try lia.
Qed.

#[global] Instance inhadd: Inhabited evm.address := populate word160.word160_default.
Lemma moveForallIn {T} {inh:Inhabited T} P (Q: T -> Prop):
  (forall x, P /\ Q x)  -> P /\ forall x, Q x.
Proof using.
  intros Hp.
  firstorder.
Qed.
Hint Rewrite bool_decide_spec: iff.

Hint Resolve list_subseteq_app_r : listset.
Hint Resolve list_subseteq_app_l : listset.

Lemma debLsnd rest extension ac s tx:
  (addrDelegated s ac || bool_decide (ac ∈ (addrsDelUndelByTx tx)))
  -> snd (maxTotalReserveDippableDebitL s (tx::rest) extension !!! ac) = None.
Proof using.
  intros Hyp.
  revert rest.
  induction extension; auto;[].
  intros.
  simpl.
  unfold updateTotals.
  rewrite updateKeyLkp3.
  rewrite bool_decide_decide.
  case_decide_inner; simpl in *; subst; eauto with listset;[].
  unfold updateTotals, updateKey.
  simpl.
  assert (isAllowedToEmpty s (tx :: rest) a = false) as Heq;
    [| rwHypsP;  simpl; eauto with listset; fail].
  unfold isAllowedToEmpty.
  destruct (addrDelegated s (sender a)); auto;[].
  simpl in *.
  rewrite bool_decide_true; try Btauto.btauto.
  set_solver.
Qed.

Lemma debLsnd2 rest extension s tx:
  snd (maxTotalReserveDippableDebitL s (tx::rest) extension !!! (sender tx)) = None.
Proof using.
  revert rest.
  induction extension; auto;[].
  intros.
  simpl.
  unfold updateTotals.
  rewrite updateKeyLkp3.
  rewrite bool_decide_decide.
  case_decide_inner; simpl in *; subst; eauto with listset;[].
  unfold updateTotals, updateKey.
  simpl.
  assert (isAllowedToEmpty s (tx :: rest) a = false) as Heq;
    [| rwHypsP;  simpl; eauto with listset; fail].
  unfold isAllowedToEmpty.
  simpl.
  rewrite andb_comm.
  rewrite bool_decide_true; try Btauto.btauto.
  set_solver.
Qed.

Lemma isAllowedToEmptyEquiv tx s:
  isAllowedToEmptyExec s tx = isAllowedToEmpty s [] tx.
Proof using.
  reflexivity.
Qed.

Definition txCannotCreateContractAtEOAAddrWithPrivateKey tx (eoasWithPrivateKey: list evm.address) :=
  forall s, let sf := (fst (execValidatedTx  s tx)) in
            forall addr,  addr ∈ eoasWithPrivateKey -> hasCode s addr = false -> hasCode sf addr = false.
  
Lemma execL tx extension s:
  (forall txext, txext ∈ extension ->  txBlockNum txext - K ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> hasCode s ac = false)
  -> consensusAcceptableTxs s (tx::extension)
  -> consensusAcceptableTxs (fst (execValidatedTx  s tx)) extension.
Proof using.
  intros Hext Heoac Hsc.
  set (sf:=(execValidatedTx s tx).1).
  intros Hc.
  unfold consensusAcceptableTxs in *.
  simpl in *.
  intros ac.
  specialize (Hc ac).
  forward_reason.
  rewrite updateKeyLkp3 in Hc.
  assert (forall acc, (maxTotalReserveDippableDebitL sf [] extension) !!! acc = (maxTotalReserveDippableDebitL s [tx] extension) !!! acc
         ) as Hass.
  { intros. rewrite -> debitLeq with (s:=s) (tx:=tx); auto. }
  specialize (Hass ac).
  autorewrite with iff.
  
  case_bool_decide; simpl in *;  try lia.
  2:{ (* non-sender account *)
    destruct (decide (ac ∈ map sender extension)) as [Hd| Hd];
    [| rewrite maxTotalReserveDippableDebitLPos; auto; fail].
    pose proof (execTxOtherBalanceLB tx s) as Hot.
    pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s) as Hdeb.
    simpl in *.
    specialize (Hot ac ltac:(auto)).
    specialize (Hdeb ac ltac:(auto)).
    rewrite Hass.
    clear Hass.
    fold sf in Hdeb.
    rewrite Hsc in Hot;[| set_solver].
    pose proof (Hsc ac ltac:(set_solver)).
    specialize (Heoac tx ltac:(set_solver) s ac ltac:(set_solver) ltac:(assumption)).
    fold sf in Heoac.
    rewrite Heoac in Hdeb.
    autorewrite with syntactic in *.
    remember (addrDelegated sf ac) as dg.
    destruct dg.
    2:{ (* ac is not delegated *)
       revert Hc.
       rwHypsP.
       utils.case_match_concl.
       autorewrite with syntactic in *.
       destruct o; subst sf; try lia.
       rename n into nonEmptyingFees.
       destruct p as (emptyingFee, emptyingVal); try lia.
    }
    {
      pose proof (debLsnd [] extension ac s tx) as Hsnd.
      remember (maxTotalReserveDippableDebitL s [tx] extension !!! ac) as rd.
      destruct rd as [nonEmptyingDebits emptyingDebits].
      pose proof (execTxDelegationUpd tx s) as Hdel. 
      simpl in Hdel. fold sf in Hdel.
      specialize (Hdel ac).
      simpl in *.
      repeat rewrite -> bool.Is_true_eq in *.
      orient_eqs.
      apply Hdel in Heqdg.
      specialize (Hsnd ltac:(auto)).
      revert Hc.
      rwHypsP.
      intros.
      subst sf.
      lia.
    }
  }
  { (* sender's account *)
    subst.
    rewrite Hass.
    clear Hass.
    unfold updateTotals in Hc.
    remember (isAllowedToEmpty s [] tx) as ae.
    pose proof (debLsnd2 [] extension s tx) as Hsnd.
    remember (maxTotalReserveDippableDebitL s [tx] extension !!! (sender tx)) as rd.
    destruct rd as [nonEmptyingDebits emptyingDebits].
    (* later transactions from the same sender cannot be emptying, assuming the extension spans K or fewer blocks *)
    simpl in *.
    rwHypsP.
    pose proof (execTxSenderBal tx s) as Hsender.
    simpl in Hsender. fold sf in Hsender.
    destruct ae; simpl in *; try lia;[|].
    {
      revert Hsender.
      orient_rwHyps.
      intros.
      revert Hc.
      rwHypsP.
      intros.
      simpl in *.
      lia.
    }

    {
      revert Hc.
      revert Hsender.
      orient_rwHyps.
      lia.
    }
  }
Qed.

(* TODO: delegation strictness: why needed:
in execution checks: treat recently undelegated accounts as delegated
 *)

Lemma execValidate tx extension s:
  consensusAcceptableTxs s (tx::extension)
  -> validateTx s tx = true.
Proof using.
  intros Hc.
  unfold consensusAcceptableTxs in *.
  specialize (Hc (sender tx)).
  simpl in *.
  unfold updateTotals in Hc. (* rename [ maxTotalReserveDippableDebit] to reserveBal decrement *)
  simpl.
  autorewrite with syntactic in Hc.
  rewrite updateKeyLkp3 in Hc.
  resolveDecide ltac:(congruence).
  unfold validateTx.
  autorewrite with iff.
  destruct (isAllowedToEmpty s [] tx); simpl in *; try lia.
  forward_reason.
  case_match; try lia.
  destruct p; try lia.
Qed.


Lemma inductiveStep  (latestState : StateOfAccounts) (tx: TxWithHdr) (extension: list TxWithHdr) :
  (forall txext, txext ∈ extension ->  txBlockNum txext - K ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> hasCode latestState ac = false)
 ->  consensusAcceptableTxs latestState (tx::extension)
  -> match execTx latestState tx with
     | None =>  False
     | Some (si, tr) =>
         consensusAcceptableTxs si extension
     end.
Proof.
  intros Hext Heoac Hsc Hc.
  unfold execTx.
  intros.
  rewrite -> (execValidate tx extension) by assumption.
  simpl.
  apply execL in Hc; auto.
  case_match; auto.
Qed.


(*
Lemma fullBlockStep  (latestState : StateOfAccounts) hb1 (block1: list TxWithHdr) (block2: list TxWithHdr) :
  (forall txext, txext ∈ block1++block2 ->  txBlockNum txext - K ≤ txBlockNum hb1 ≤ txBlockNum txext)
    ->
  consensusAcceptableTxs latestState ((hb1::block1)++block2)
  -> match execTxs latestState (hb1::block1) with
     | None =>  False
     | Some (si, _) =>
         consensusAcceptableTxs si block2
     end.
Proof.
  intros Hrange Hacc.
  simpl.
  eapply inductiveStep in Hacc; [|exact Hrange].
  destruct (execTx latestState hb1) as [(si, tr)|]; try contradiction;[].
  assumption.
  induction block1 as [|hb2 block1 IH] in latestState, Hrange, Hacc |- *; auto.
  {
  }
  {
    
    
  change  ((hb1 :: block1) ++ block2) with (hb1::(block1++block2)) in Hacc.
  eapply inductiveStep in Hacc; [|exact Hrange].
  simpl.
  destruct (execTx latestState hb1) as [(si, tr)|]; try contradiction;[].
  specialize (IH si).
  lapply IH.
  2:{
    destruct block1; auto.
    intros.
    pose proof (Hrange t ltac:(set_solver)).
    pose proof (Hrange txext ltac:(set_solver)).
    assert (txBlockNum t>= K) by admit.
    assert (txBlockNum txext>= K) by admit.
    Search hb1.
 *)

Set Printing Coercions.
Fixpoint blockNumsInRange (ltx: list TxWithHdr) : Prop :=
  match ltx with
  | [] => True
  | htx::ttx =>
      (forall txext, txext ∈ ttx ->  txBlockNum txext - K ≤ txBlockNum htx ≤ txBlockNum txext)
      /\ blockNumsInRange ttx
  end.
    
Fixpoint blockNumsInRange2 (ltx: list TxWithHdr) : Prop :=
  match ltx with
  | [] => True
  | htx::ttx =>
      (forall txext, txext ∈ ttx ->  txBlockNum txext ≤ txBlockNum htx + K  /\ txBlockNum htx ≤ txBlockNum txext)
      /\ blockNumsInRange ttx
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


Lemma  txCannotCreateContractAtEOAAddrWithPrivateKeyMono tx l1 l2:
  l1 ⊆ l2
  -> txCannotCreateContractAtEOAAddrWithPrivateKey tx l2
  -> txCannotCreateContractAtEOAAddrWithPrivateKey tx l1.
Proof using.
  unfold txCannotCreateContractAtEOAAddrWithPrivateKey.
  intros Hs Hp.
  intros.
  apply Hp; auto.
Qed.

Lemma  txCannotCreateContractAtEOAAddrWithPrivateKeyTrimHead tx h l:
  txCannotCreateContractAtEOAAddrWithPrivateKey tx (h::l)
  -> txCannotCreateContractAtEOAAddrWithPrivateKey tx l.
Proof using.
  apply txCannotCreateContractAtEOAAddrWithPrivateKeyMono.
  set_solver.
Qed.

Lemma fullBlockStep  (latestState : StateOfAccounts) (block1: list TxWithHdr) (block2: list TxWithHdr) :
  blockNumsInRange (block1++block2)
  -> consensusAcceptableTxs latestState (block1++block2)
  -> (forall txext, txext ∈ (block1++block2) ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (block1++block2)))
  -> (forall ac, ac ∈ (map sender (block1++block2)) -> hasCode latestState ac = false)
  -> match execTxs latestState block1 with
     | None =>  False
     | Some (si, _) =>
         consensusAcceptableTxs si block2
         /\ blockNumsInRange block2
     end.
Proof.
  intros Hrange Hacc.
  induction block1 as [|hb1 block1 IH] in latestState, Hrange, Hacc |- *; simpl in *; auto.
  intros Heoa Hsc.
  change  ((hb1 :: block1) ++ block2) with (hb1::(block1++block2)) in Hacc.
  forward_reason.
  eapply inductiveStep in Hacc;  auto. 
  destruct (execTx latestState hb1) as [(si, tr)|]; try contradiction;[].
  pose proof (fun txext p => txCannotCreateContractAtEOAAddrWithPrivateKeyTrimHead _ _ _
                               (Heoa txext (elem_of_list_further _ _ _ p))).
  specialize (fun txext p => Hsc txext (elem_of_list_further _ _ _ p)).
  specialize (IH si ltac:(auto) ltac:(auto) ltac:(auto)).
  lapply IH.
  2:{
    unfold txCannotCreateContractAtEOAAddrWithPrivateKey in Heoa.
  destruct (execTxs si block1) as [|]; try auto.
  2:{
  destruct p as [si2 ?].
  assumption.
Qed.


Definition concatL {T} (l: list (list T)) := flat_map id l.
Definition consensusAcceptableBlocks (lastConsensedState: StateOfAccounts) (proposedBlocks: list (list TxWithHdr)) :=
  consensusAcceptableTxs lastConsensedState (concatL proposedBlocks).

Lemma acceptableNil lastConsensedState:
  consensusAcceptableTxs lastConsensedState [].
Proof using.
  unfold consensusAcceptableTxs.
  intros.
  simpl.
  unfold lookup_total.
  unfold map_lookup_total. simpl.
  unfold default. simpl.
  autorewrite with syntactic.
  rewrite lookup_empty.
  lia.
Qed.

Lemma fullBlockStep2  (latestState : StateOfAccounts) (block1: list TxWithHdr) (block2: list TxWithHdr) :
  consensusAcceptableBlocks latestState [block1;block2]
  -> match execTxs latestState block1 with
     | None =>  False
     | Some (si, tr) =>
         consensusAcceptableBlocks si [block2]
     end.
Proof. Admitted.


Section use.
  Variable b0: list TxWithHdr.
  Variable sb0 : StateOfAccounts. (* state after b0 *)

  Hypothesis nextBlockPicker:
    forall (lastConsensedState: StateOfAccounts) (proposedBlocks: list (list TxWithHdr)),
      lengthN proposedBlocks < K
      -> consensusAcceptableBlocks lastConsensedState proposedBlocks
      -> exists nextBlock, consensusAcceptableBlocks lastConsensedState (proposedBlocks++[nextBlock]).


  Lemma operation  : (K=2) -> False.
    intros.
    revert nextBlockPicker.
    rwHypsP.
    intros.
    pose proof (nextBlockPicker sb0 [] ltac:(reflexivity) (acceptableNil _)) as b1.
    destruct b1 as [b1 b1ok].
    simpl in b1ok.
    pose proof (nextBlockPicker sb0 [b1] ltac:(reflexivity) b1ok) as b2.
    destruct b2 as [b2 b2ok].
    evar (sb1: StateOfAccounts).
(*
ad definition consensusAcceptableBlocks that conse
    (consensusAcceptableBlocks sb0 [b1; b2]) ->
    (consensusAcceptableBlocks sb1 [b2])

    apply fullBlockStep2 in b2ok.
    case_match; auto.
    destruct p as [sb1 ?].
    pose proof (nextBlockPicker sb1 [b2] ltac:(reflexivity) b2ok) as b3.
    destruct b3 as [b3 b3ok].
    apply fullBlockStep2 in b3ok.
    case_match; auto.
    destruct p as [sb2 ?].
    pose proof (nextBlockPicker sb2 [b3] ltac:(reflexivity) b3ok) as b4.
*)
 Abort.
End use.
