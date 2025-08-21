(* proofs about reserve balances:
- consensus guarnatees when it sends a block for executions
- what consensus assumes execution guarantees
- how those guarantees ensure execution will never run into a chase when an account has insufficient balance to pay gas fees
 *)


Require Import monad.proofs.bigauto.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.evmmisc.
Require Import monad.proofs.misc.
Require Import bluerock.hw_models.utils.
Hint Rewrite orb_true_iff andb_true_iff: iff.
(*
Require Import bluerock.auto.rwdb.
Require Import bluerock.auto.miscPure.
*)
Require Import monad.proofs.bigauto.
Require Import Lens.Lens.
Import LensNotations.
Open Scope lens_scope.
Set Default Goal Selector "!".
Tactic Notation "rdestruct" open_constr(c) "as" intropattern(I) :=
  (let ff := fresh "rd" in remember c as ff; destruct ff as I).

Tactic Notation "rdestruct" open_constr(c) :=
  (let ff := fresh "rd" in remember c as ff; destruct ff).

Require Import bluerock.auto.cpp.tactics4.
Open Scope N_scope.
Definition StateOfAccounts : Type := EvmAddr -> AccountM.
Definition addrDelegated  (s: StateOfAccounts) (a : EvmAddr) : bool :=
  match delegatedTo (s a) with
  | [] => false
  | _ => true
  end.

(* new fiends since ~2018 when the evm semantics library we depend on was developed *)
Record TxExtra :=
  {
    dels: list EvmAddr;
    undels: list EvmAddr;

    (* the fields above should ultimately come from EVM semantics and not here. the fields below are monad specific *)
    reserveBalUpdate: option N (* updates the reserve balance of the sender if Some. in that case, the tx does not do anything else, e.g. smart contract invocation or transer *)
  }.
    
  
Definition TxWithHdr : Type := (BlockHeader * TxExtra) * (Transaction).

(* only gas fees. does not include value transfers *)
Definition maxTxFee (t: TxWithHdr) : N :=
  ((w256_to_N (block.tr_gas_price t.2)) * (w256_to_N (block.tr_gas_limit t.2))).

Opaque maxTxFee.

Definition DefaultReserveBal: N. Proof. exact 100. Qed. (* no proof can depend on it being 100, because it is saved with Qed *)


Definition sender (t: TxWithHdr): EvmAddr := tsender t.2.
Definition value (t: TxWithHdr): N := w256_to_N (block.tr_value t.2).

Definition K : N. Proof. exact 2. Qed. (* no proof can depend on it being 2 *)

Definition addrsDelUndelByTx  (tx: TxWithHdr) : list EvmAddr := (dels tx.1.2 ++undels tx.1.2).

Definition txDelUndelAddr (addr: EvmAddr) (tx: TxWithHdr) : bool :=
  bool_decide (addr ∈ addrsDelUndelByTx tx).


Definition txBlockNum (t: TxWithHdr) : N := number t.1.1.

Definition reserveBalUpdateOfTx (t: TxWithHdr) : option N :=
  reserveBalUpdate t.1.2.

Record ExtraAcState :=
  {

    (* in impl, the meaning of None can be changed to just mean there was none in the last 2K *)
    lastDelUndelInBlockIndex : option N; (* last block index where this address was delegated or undelegated  *)
    lastTxInBlockIndex : option N; (* last block index where this address sent a tx *)
    configuredReserveBal: N (* this must go to the state in db/blockchain *)
  }.

#[only(lens)] derive ExtraAcState.
#[global] Instance inhabitedeacs : Inhabited ExtraAcState := populate (Build_ExtraAcState None None 0).
  

Definition ExtraAcStates := (EvmAddr -> ExtraAcState).

(*
Definition indLe (l r: Indices):= block_index l  <= block_index r /\ tx_index l <= tx_index r. *)
Definition indexWithinK (proj: ExtraAcState -> option N) (state : ExtraAcStates)  (tx: TxWithHdr) : bool :=
  let startIndex :=  txBlockNum tx -K  in
  match proj (state (sender tx))  with
  | Some index =>
      bool_decide (startIndex <= index <= txBlockNum tx)
  | None => false
  end.

Definition AugmentedState : Type := StateOfAccounts * ExtraAcStates.
Definition existsTxWithinK (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  indexWithinK lastTxInBlockIndex (snd state) tx.

Definition existsDelUndelTxWithinK (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  indexWithinK  lastDelUndelInBlockIndex (snd state) tx.

(* external assumption: tx::intermediateTxsSinceState does not span more than K blocks *)
Definition isAllowedToEmpty
  (state : AugmentedState) (intermediateTxsSinceState: list TxWithHdr)  (tx: TxWithHdr) : bool :=
  let delegated := (addrDelegated (fst state) (sender tx))
                   || existsDelUndelTxWithinK state tx
                   || bool_decide  ((sender tx) ∈ flat_map addrsDelUndelByTx (tx::intermediateTxsSinceState))
  in
  let existsSameSenderTxInWindow :=
    (existsTxWithinK state tx)
    || bool_decide ((sender tx) ∈ map sender intermediateTxsSinceState) in
  (negb delegated) && (negb existsSameSenderTxInWindow).


(* TODO: make it a notation and get rid of calls to updateKeyLkp3 *)
Definition updateKey  {T} `{c: EqDecision T} {V}  (oldmap: T -> V) (updKey: T) (f: V -> V) : T -> V :=
  fun k => if (bool_decide (k=updKey)) then f (oldmap updKey) else oldmap k.

(* TODO: 
Disable Notation "!!!".*)
Lemma updateKeyLkp3  {T} `{c: EqDecision T} {V} (m: T -> V) (a b: T) (f: V -> V) :
  (updateKey m a f) !!! b = if (bool_decide (b=a)) then (f (m !!! a)) else m !!! b.
Proof using.
  reflexivity.
Qed.


Definition EffReserveBals := EvmAddr -> Z.

(*
Definition mapKeys {K V:Type} `{Countable K} (g: gmap K V) : list K := map fst (map_to_list g).
*)

Definition configuredReserveBalOfAddr (s: ExtraAcStates) addr := configuredReserveBal (s addr).
                      
Open Scope Z_scope.

Definition balanceOfAc (s: StateOfAccounts) (a: EvmAddr) : N :=
  balance (s a).

Definition updateBalanceOfAc (s: StateOfAccounts) (addr: EvmAddr) (upd: N -> N) : StateOfAccounts :=
  updateKey s addr (fun old => old &: _balance %= upd).

Definition initialEffReserveBals (s: AugmentedState) : EffReserveBals :=
  fun addr =>  (balanceOfAc s.1 addr `min` configuredReserveBalOfAddr s.2 addr).

(* TODO: rename it to remainingErb *)
Definition remainingEffReserveBals (preIntermediatesState : AugmentedState) (preTxResBalances: EffReserveBals) (intermediates: list TxWithHdr) (next: TxWithHdr)
  : EffReserveBals :=
  let s := preIntermediatesState in
  let addr := sender next in
  match reserveBalUpdateOfTx next with
  | Some newRb => (* is there a way to make it liberal ?*)
      updateKey preTxResBalances addr (fun prevErb => (prevErb - maxTxFee next) `min` newRb)
  | None  => (* regular tx *)
      if isAllowedToEmpty s intermediates next
      then
        let sbal := balanceOfAc s.1 addr in
        let newBal:N := (sbal - maxTxFee next - value next)%N in (* this subtraction is done in N: capped at 0*)
        if bool_decide (maxTxFee next <= sbal)
        then updateKey preTxResBalances addr (fun prevErb => newBal `min` (configuredReserveBalOfAddr s.2 addr)) 
        else updateKey preTxResBalances addr (fun _ => -1) (* -ve =>  this tx cannot be accepted *)
          
      else (updateKey preTxResBalances addr (fun prevErb => (prevErb - maxTxFee next)%Z)) (* -ve =>  this tx cannot be accepted *)
  end.
  

Fixpoint remainingEffReserveBalsL (latestState : AugmentedState) (preRestResBalances: EffReserveBals) (postStateAccountedSuffix rest: list TxWithHdr)
  : EffReserveBals:=
  match rest with
  | [] => preRestResBalances
  | hrest::tlrest =>
      let remainingReserves :=
        remainingEffReserveBals latestState preRestResBalances postStateAccountedSuffix hrest in
      remainingEffReserveBalsL latestState remainingReserves (postStateAccountedSuffix++[hrest]) tlrest
  end.

Definition consensusAcceptableTxs (latestState : AugmentedState) (postStateSuffix: list TxWithHdr) : Prop :=
  forall addr,  addr ∈ map sender postStateSuffix ->
   0<= (remainingEffReserveBalsL latestState (initialEffReserveBals latestState) [] postStateSuffix) !!! addr.

Definition balanceOfAcA (s: AugmentedState) (ac: EvmAddr) := balanceOfAc (fst s) ac.


Definition addrConsideredDelegated  (state: AugmentedState) (tx : TxWithHdr) : bool :=
  (addrDelegated (fst state) (sender tx))
                   || (bool_decide (sender tx ∈ addrsDelUndelByTx tx))
                   || existsDelUndelTxWithinK state tx.
Definition isAllowedToEmptyExec
  (state : AugmentedState)  (tx: TxWithHdr) : bool :=
  isAllowedToEmpty state [] tx.

Print block.block_account.

Definition hasCode (s: StateOfAccounts) (addr: EvmAddr): bool:=
  block.block_account_hascode (coreAc (s addr)).

Opaque hasCode.
                                         

(* TODO: rename to uodate ExtraState *)

(*
Definition upsertKeys {T V} `{c: Countable T} (m: gmap T V) (items: list (T*V)) :=
  foldr (uncurry insert) m items.
*)

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



(*
  Alice sends money to adds2 in some contract.
  Alice is EOA.
  Alice sends tx foo to a smart contract address addr.
  addr execution creates a deployes code at addr2, and calls it and the call empties addr2.
  


*)

Hint Rewrite @balanceOfUpd: syntactic.
Open Scope N_scope.

Axiom evmExecTxCore : StateOfAccounts -> TxWithHdr -> StateOfAccounts * (list EvmAddr) (* the list contains all the changed accounts *).
Axiom revertTx : StateOfAccounts -> TxWithHdr -> StateOfAccounts.

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
         then if isAllowedToEmptyExec s t then true else bool_decide ((erb  - maxTxFee t) <= balanceOfAc si a)
         else bool_decide (erb <= balanceOfAc si a) in
     let allBalCheck : bool := (forallb balCheck changedAccounts) in (* in impl, only do for updates *)
     if (allBalCheck)
     then (si, updateExtraState s.2 t)
     else (revertTx s.1 t, updateExtraState s.2 t)
  end
.

Definition validateTx (preTxState: StateOfAccounts) (t: TxWithHdr): bool :=
   bool_decide (maxTxFee t  <= balanceOfAc preTxState (sender t))%N.

Definition execTx (s: AugmentedState) (t: TxWithHdr): option (AugmentedState) :=
  if (negb (validateTx (fst s) t)) (* if this fails. the execution of the entire block aborts *)
  then None
  else Some (execValidatedTx  s t).

Fixpoint execTxs  (s: AugmentedState) (ts: list TxWithHdr): option AugmentedState :=
  match ts with
  | [] => Some s
  | t::tls =>
      match execTx s t with
      | Some si => execTxs si tls
      | None => None
      end
  end.


Hint Rewrite -> bool_decide_eq_true : iff.

Ltac rememberForallb :=
    match goal with
    [H:= context[forallb ?a ?b] |- _] => remember (forallb a b) as fb
    |[H: context[forallb ?a ?b] |- _] => remember (forallb a b) as fb
    | [|- context[forallb ?a ?b]] => remember (forallb a b) as fb
    end.


(** *core execution assumptions *)

Lemma balanceOfRevert s tx ac:
  reserveBalUpdateOfTx tx = None ->
  balanceOfAc (revertTx s tx) ac =
    if bool_decide (ac= sender tx)
    then balanceOfAc s ac - maxTxFee tx
    else balanceOfAc s ac.
Proof using. Admitted.


Lemma revertTxDelegationUpdCore tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (revertTx s tx) in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && bool_decide (ac ∉ (undels tx.1.2)))
                || bool_decide (ac ∈ (dels tx.1.2))).
Proof.
Admitted.

Lemma execTxDelegationUpdCore tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (forall ac, addrDelegated sf ac  =
                (addrDelegated s ac && bool_decide (ac ∉ (undels tx.1.2)))
                || bool_decide (ac ∈ (dels tx.1.2))).
Proof.
Admitted.

Lemma execTxSenderBalCoreEquiv tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  addrDelegated s (sender tx) = false 
   ->  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - (maxTxFee tx).
Proof. Admitted.

Lemma execTxSenderBalCore tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (if addrDelegated s (sender tx) (* sender cannot have code *)
   then True
   else balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAc sf (sender tx) =  balanceOfAc s (sender tx) - (maxTxFee tx)).
Proof. Admitted.

Lemma execTxCannotDebitNonDelegatedNonContractAccountsCore tx s:
  reserveBalUpdateOfTx tx = None ->
  let sf :=  (evmExecTxCore s tx).1 in
  (forall ac, ac <> sender tx
              -> if (addrDelegated sf ac || hasCode sf ac)
                 then True
                 else balanceOfAc s ac <= balanceOfAc sf ac).
Proof using. Admitted.


Lemma changedAccountSetSound tx s:
  reserveBalUpdateOfTx tx = None ->
  let (sf, changedAccounts) :=  (evmExecTxCore s tx) in
  (forall ac, ac ∉ changedAccounts -> sf ac = s ac).
Proof using. Admitted.


(* end core exec assumptions *)

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
  rewrite execTxDelegationUpdCore;[| assumption].
  repeat rewrite Is_true_true.
  intros Hp.
  autorewrite with iff in Hp.
  destruct Hp; forward_reason; rwHypsP; auto;[].
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
  rewrite revertTxDelegationUpdCore;[| assumption].
  repeat rewrite Is_true_true.
  intros Hp.
  autorewrite with iff in Hp.
  destruct Hp; forward_reason; rwHypsP; auto;[].
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

Lemma forallb_spec {T}  (f: T->bool) l:
  forallb f l = true <-> (forall x, x ∈ l -> f x = true).
Proof.
  rewrite forallb_forall.
  split; intros ? ?; (rewrite elem_of_list_In ||  rewrite <- elem_of_list_In); auto.
Qed.

Lemma execTxOtherBalanceLB tx s:
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
      rewrite balanceOfRevert;[| auto; fail].
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
  let ReserveBal := configuredReserveBalOfAddr s.2 (sender tx) in
  let sf :=  (execValidatedTx s tx) in
  hasCode sf.1 (sender tx) = false->
  (if isAllowedToEmpty s [] tx
   then balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx)
        \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
  else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx))).
Proof.
  intros ? ? Hsc.
  subst ReserveBal.
  pose proof (execTxSenderBalCore tx s.1) as Hc.
  simpl in Hc.
  unfold isAllowedToEmpty.
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
  unfold isAllowedToEmptyExec. unfold isAllowedToEmpty.
  intros.
  unfold balanceOfAcA in *.
  destruct (addrDelegated s.1 (sender tx)); simpl in *.
  {
    rememberForallb.
    unfold balanceOfAcA in *.
    destruct fb; try lia.
    2:{
      simpl in *. rewrite balanceOfRevert;[| auto; fail].
      resolveDecide congruence. lia.
    }
    symmetry in Heqfb.
    rewrite  forallb_spec in Heqfb.
    destruct (decide (sender tx ∈ changed));
      [| unfold balanceOfAc; simpl; rewrite Hsnd; auto; lia].
    specialize (Heqfb (sender tx) ltac:(auto)).
    resolveDecide congruence.
    simpl in *.
    rewrite -> Hsc in Heqfb.
    case_bool_decide; try lia.
  }
  {
    autorewrite with syntactic in *.
    rememberForallb.
    destruct (~~ (existsDelUndelTxWithinK s tx || bool_decide (sender tx ∈ addrsDelUndelByTx tx)) && ~~ existsTxWithinK s tx);
      simpl in *.
    {
      destruct fb; simpl in *; try lia.
      rewrite balanceOfRevert;[| auto; fail].
      resolveDecide congruence.
      lia.
    }
    {
      destruct fb; destruct Hc; simpl in *; orient_rwHyps; simpl in *;
        try (rewrite balanceOfRevert;[| auto; fail]);
        try resolveDecide congruence;
        try lia;[].
      rewrite  forallb_spec in Heqfb.
      destruct (decide (sender tx ∈ changed)).
      {
        specialize (Heqfb (sender tx) ltac:(auto)).
        rewrite Hsc in Heqfb.
        resolveDecide congruence.
        simpl in *.
        case_bool_decide; try lia.
      }
      {
        unfold balanceOfAc in *.
        rewrite Hsnd in H; try assumption.
        lia.
      }
      
    }

  }
Qed.

Lemma pairEta {A B R} (p:A*B) (f: A -> B -> R):
  (let '(a,b) := p in f a b) = f (fst p) (snd p).
Proof using. destruct p; auto. Qed.

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
    rewrite balanceOfRevert;[| auto; fail].
    resolveDecide congruence.
    lia.
  }
Qed.

Lemma execBalLb ac s tx:
  let sf :=  (execValidatedTx s tx) in
  let ReserveBal := configuredReserveBalOfAddr s.2 ac in
  if (bool_decide (ac=sender tx)) then 
    hasCode sf.1 (sender tx) = false->
    (if isAllowedToEmpty s [] tx
     then balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - ( maxTxFee tx + value tx)
          \/  balanceOfAcA sf (sender tx) =  balanceOfAcA s (sender tx) - (maxTxFee tx)
     else ReserveBal `min` (balanceOfAcA s (sender tx)) - maxTxFee tx <= (balanceOfAcA sf (sender tx)))
  else
    if (hasCode sf.1 ac)
    then True
    else (if addrDelegated (fst sf) ac then ReserveBal `min` (balanceOfAcA s ac) else balanceOfAcA s ac)
         <= (balanceOfAcA sf ac).
Proof using.
  simpl.
  case_bool_decide; subst; [apply execTxSenderBal|].
  pose proof (execTxOtherBalanceLB tx s ac ltac:(auto)).
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
    rewrite revertTxDelegationUpdCore;[| auto; fail].
    unfold addrsDelUndelByTx in *.
    (*
    resdec ltac:(set_solver). *)
    rewrite bool_decide_true;[| set_solver].
    rewrite bool_decide_false;[|set_solver].
    autorewrite with syntactic.
    reflexivity.
  }
  {
    pose proof (execTxDelegationUpdCore txlast s.1 ltac:(auto) addr) as Hd.
    revert Hd. rwHypsP.
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

Hint Rewrite Z.min_l  using lia: syntactic.
Hint Rewrite Z.min_r  using lia: syntactic.
Hint Rewrite N.min_l  using lia: syntactic.
Hint Rewrite N.min_r  using lia: syntactic.


Lemma ite_fequiv {T} (t1 t2 e1 e2:T) (b1 b2: bool) :
  b1=b2 -> t1=t2 -> e1=e2 -> (if b1 then t1 else e1) = if b2 then t2 else e2.
Proof using.
  intros. subst. reflexivity.
Qed.

Hint Rewrite @elem_of_cons: syntactic.

Set Nested Proofs Allowed.


Lemma isAllowedToEmpty2 s txlast rest txnext:
  let sf :=  execValidatedTx s txlast in 
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
  

Lemma moveForallIn {T} {inh:Inhabited T} P (Q: T -> Prop):
  (forall x, P /\ Q x)  -> P /\ forall x, Q x.
Proof using.
  intros Hp.
  firstorder.
Qed.
Hint Rewrite bool_decide_spec: iff.

Hint Resolve list_subseteq_app_r : listset.
Hint Resolve list_subseteq_app_l : listset.

Definition txCannotCreateContractAtEOAAddrWithPrivateKey tx (eoasWithPrivateKey: list EvmAddr) :=
  forall s, let sf := (execValidatedTx  s tx) in
            forall addr,  addr ∈ eoasWithPrivateKey -> hasCode s.1 addr = false -> hasCode sf.1 addr = false.

Lemma hasCodeFalsePresExec l s tx:
  (forall txext, txext ∈ (tx::l) ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (tx::l)))
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
Lemma initResBal s addr:
  (initialEffReserveBals s) !!! addr =
    balanceOfAcA s addr `min` configuredReserveBalOfAddr s.2 addr.
Proof.
  reflexivity.
Qed.


Definition rbLe (eoas: list EvmAddr) (rb1 rb2: EffReserveBals) :=
  forall addr, addr ∈ eoas -> rb1 !!! addr <= rb2 !!! addr.

Hint Rewrite @updateKeyLkp3 : syntactic.
Lemma mono eoas s rb1 rb2 inter tx:
  rbLe eoas rb1 rb2
  -> rbLe eoas (remainingEffReserveBals s rb1 inter tx)
       (remainingEffReserveBals s rb2 inter tx).
Proof using.
  intros Hrb addr Hin.
  unfold remainingEffReserveBals.
  pose proof (Hrb addr Hin).
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  {case_bool_decide; subst; try lia. }
  case_match_concl;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  2:{ case_bool_decide; subst; try lia. }
  case_bool_decide;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  2:{ case_bool_decide; subst; try lia. }
  case_bool_decide;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *; try lia.
Qed.
  
Lemma monoL eoas s rb1 rb2 inter extension:
  map sender extension ⊆ eoas
  -> rbLe eoas rb1 rb2
  -> rbLe eoas (remainingEffReserveBalsL s rb1 inter extension)
          (remainingEffReserveBalsL s rb2 inter extension).
Proof using.
  revert rb1 rb2 inter.
  induction extension; auto;[].
  unfold rbLe in *.
  intros ? ? ? Hs Hrb addr Hin. simpl in *.
  simpl.
  apply IHextension;[set_solver | | set_solver].
  apply mono.
  assumption.
Qed.

Lemma isAllowedToEmptyImpl s tx inter a:
  isAllowedToEmpty s (tx::inter) a = true
  -> sender tx <> sender a
     /\ addrDelegated (execValidatedTx s tx).1 (sender a) = false.
Proof using.
  intros  Hae.
  unfold isAllowedToEmpty in *.
  simpl in *.
  destruct (decide (sender a = sender tx)).
  {
    assert (bool_decide (sender a ∈ sender tx :: map sender inter)= true) as Heq.
    { rewrite bool_decide_true; set_solver. }
    rewrite Heq in Hae.
    autorewrite with syntactic in Hae.
    congruence.
  }
  split_and; auto.
  rewrite <- not_true_iff_false.
  intros Hc.
  pose proof (execTxDelegationUpd tx s) as Hdel.
  simpl in Hdel.
  specialize (Hdel (sender a)).
  repeat rewrite Is_true_true in Hdel.
  specialize (Hdel Hc).
  apply orb_prop in Hdel.
  destruct Hdel as [Hdel | Hdel].
  {
    rewrite Hdel in Hae.
    simpl.
    autorewrite with syntactic in Hae.
    congruence.
  }
  {
    rewrite bool_decide_eq_true in Hdel.
    case_bool_decide; try set_solver.
    autorewrite with syntactic in Hae.
    congruence.
  }
Qed.
  

Lemma emptyBalanceUb s tx inter a:
  hasCode (execValidatedTx s tx).1 (sender a) = false
  -> isAllowedToEmpty s (tx :: inter) a = true
  -> balanceOfAc s.1 (sender a) ≤ balanceOfAc (execValidatedTx s tx).1 (sender a).
Proof.
  intros Hsc Hae.
  pose proof (execTxCannotDebitNonDelegatedNonContractAccounts tx s (sender a)) as Hs.
  simpl in Hs.
  pose proof (isAllowedToEmptyImpl _ _ _  _ Hae).
  forward_reason.
  rewrite Hr in Hs.
  simpl in *.
  rewrite Hsc in Hs.
  unfold balanceOfAcA in *.
  simpl in *.
  lia.
Qed.

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

Lemma configuredReserveBalOfAddrSame2 s tx inter a:
  isAllowedToEmpty s (tx :: inter) a = true
  -> (configuredReserveBalOfAddr (execValidatedTx s tx).2 (sender a)
      =
        configuredReserveBalOfAddr s.2 (sender a)).
Proof using.
  intros Hae.
  apply configuredReserveBalOfAddrSame.
  apply isAllowedToEmptyImpl in Hae.
  tauto.
Qed.
  
Lemma monoL2 eoas s rb1 rb2 inter extension tx:
  (map sender extension) ⊆ eoas
  -> rbLe eoas rb1 rb2
  -> (forall txext, txext ∈ extension ->  txBlockNum txext - K ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (∀ ac : EvmAddr, ac ∈ map sender (tx :: extension) → hasCode (execValidatedTx s tx).1 ac = false)
  -> rbLe eoas (remainingEffReserveBalsL s rb1 (tx::inter) extension)
          (remainingEffReserveBalsL (execValidatedTx s tx) rb2 inter extension).
Proof using.
  revert rb1 rb2 inter.
  induction extension; auto;[].
  unfold rbLe in *.
  intros ? ? ? Hsub Hrb Hrange Hsc addr Hin.
  simpl.
  apply forallCons in Hrange.
  simpl in Hsc.
  forward_reason.
  apply IHextension; auto;[set_solver| |].
  2:{ intros. apply Hsc. set_solver. }
  clear Hin. clear addr.
  intros addr Hin.
  simpl.
  unfold remainingEffReserveBals.
  pose proof (Hrb addr Hin).
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  { case_bool_decide; subst; try lia. }
  rewrite isAllowedToEmpty2;[| lia].
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  2:{ case_bool_decide; subst; try lia. }
  specialize (Hsc (sender a) ltac:(set_solver)).
  pose proof (emptyBalanceUb _ _ _ _ Hsc Heqb) as Hle.
  case_bool_decide.
  {
    rewrite bool_decide_true; [|lia].
    repeat rewrite updateKeyLkp3;
      fold EffReserveBals in *.
    case_bool_decide; try lia.
    pose proof (configuredReserveBalOfAddrSame2 _ _ _ _ Heqb) as Hlle.
    rewrite Hlle.
    lia.
  }
  case_bool_decide; 
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *;
    case_bool_decide; try lia.
Qed.
    
    
Hint Rewrite initResBal configuredReserveBalOfAddrSpec: syntactic.
Ltac solver := simpl in *; autorewrite with syntactic in *; simpl in *; resolveDecide congruence; resolveDecide lia; resolveDecide tauto.
Ltac case_bool_decide_concl:=
  match goal with
  | |- context [@bool_decide ?P ?dec] =>
    destruct_decide (@bool_decide_reflect P dec) as Hd
  end.

Definition rbLeA (rb1 rb2: EffReserveBals) :=
  forall addr, rb1 !!! addr <= rb2 !!! addr.

Lemma exec1 tx extension s :
  let sf := (execValidatedTx s tx) in 
  (∀ ac : EvmAddr, ac ∈ sender tx :: map sender extension → hasCode (execValidatedTx s tx).1 ac = false)
  -> (∀ addr : EvmAddr,
    addr ∈ sender tx :: map sender extension
    → remainingEffReserveBals s (initialEffReserveBals s) [] tx !!! addr ≤ initialEffReserveBals sf !!! addr).
Proof using.
  intros ? Hscf.
  intros ? Hin.
  unfold remainingEffReserveBals.
  case_match.
  { (* this tx updates the reserve balance *)
    rename n into nrb.
    rewrite updateKeyLkp3.
    unfold sf.
    repeat rewrite initResBal.
    rewrite configuredReserveBalOfAddrSpec.
    unfold execValidatedTx.
    rwHypsP.
    simpl.
    simpl.
    unfold balanceOfAcA in *.
    rewrite balanceOfUpd.
    unfold rbAfterTx.
    rwHypsP.
    case_bool_decide;
      resolveDecide congruence; simpl in *; try lia.
  }
  pose proof (execBalLb addr s tx) as Hlb.
  simpl in Hlb. fold sf in Hlb.
  rewrite Hscf in Hlb;[|set_solver].
  rewrite Hscf in Hlb;[|set_solver].
  case_match_concl.
  { (* isAllowedToEmpty *)
    match goal with
    | H: isAllowedToEmpty _ _ _ = _ |- _ => rename H into Hae
    end.
    subst sf.
    autorewrite with syntactic in *.
    case_bool_decide_concl.
    2:{ (* a separate proof can actually prove that this case is impossible. because this tx was actually accepted : can prove that remaingEffReserveBals can only decrease the input *)
      rewrite updateKeyLkp3.
      autorewrite with syntactic.
      unfold balanceOfAcA, rbAfterTx in *.
      rwHypsP.
      case_bool_decide; resolveDecide congruence; try lia.
      case_match; try lia.
    }
    {
      rewrite updateKeyLkp3.
      autorewrite with syntactic.
      unfold balanceOfAcA, rbAfterTx in *.
      rwHypsP.
      case_bool_decide; resolveDecide congruence; try lia;
        [| case_match; lia].
      specialize (Hlb ltac:(auto)).
      subst.
      destruct Hlb; subst; try lia.
    }
  }
  rewrite updateKeyLkp3.
  subst sf.
  autorewrite with syntactic in *.
  unfold balanceOfAcA, rbAfterTx in *.
  rwHypsP.
  case_bool_decide; subst; resolveDecide congruence; try lia.
  case_match; lia.
Qed.
  

Lemma execL tx extension s:
  (forall txext, txext ∈ extension ->  txBlockNum txext - K ≤ txBlockNum tx ≤ txBlockNum txext) (* relaxing it : not imp *)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (tx::extension)))
  -> (forall ac, ac ∈ (map sender (tx::extension)) -> hasCode s.1 ac = false)
  -> consensusAcceptableTxs s (tx::extension)
  -> consensusAcceptableTxs (execValidatedTx  s tx) extension.
Proof using.
  intros Hext Heoac Hsc.
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
  etransitivity.
  { apply Hc. }
  pose proof (monoL2 (map sender (tx::extension))) as Hm.
  unfold rbLe in Hm.
  apply Hm; auto; simpl in *; [ set_solver | | set_solver].
  clear Hm.
  clear Hc. clear Hin. clear ac.
  hnf.
  clear Hsc.
  clear Hext.
  apply exec1. assumption.
Qed.

  
(* TODO: delegation strictness: why needed:
in execution checks: treat recently undelegated accounts as delegated
 *)

Lemma decreasingRemTxSender s irb proc tx a:
  remainingEffReserveBals s irb (tx :: proc) a !!! sender tx ≤ irb !!! sender tx.
Proof using.
  unfold remainingEffReserveBals.
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  { case_bool_decide; rwHypsP; try lia. }
  case_match_concl; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  2:{ case_bool_decide; rwHypsP; try lia. }
  apply isAllowedToEmptyImpl in Heqb.
  forward_reason.
  case_bool_decide; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *.
  2:{ case_bool_decide; rwHypsP; try lia.  }
  case_bool_decide; auto;
    repeat rewrite updateKeyLkp3;
    fold EffReserveBals in *; try lia.
Qed.
  
  
Lemma decreasingRemL s irb proc next tx:
  (remainingEffReserveBalsL s irb (tx::proc) next) !!! (sender tx) <=  (irb !!! (sender tx)).
Proof using.
  revert proc irb.
  induction next; unfold rbLeA in *; simpl; [lia|].
  intros.
  pose proof (IHnext (proc++[a]) (remainingEffReserveBals s irb (tx::proc) a)).
  etransitivity;[apply H|].
  apply decreasingRemTxSender.
Qed.


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
  match type of Hc with
    context[ remainingEffReserveBalsL _ ?irb _ _ ]
    => assert (0<= irb !!! (sender tx)) as Hr
  end.
  {
    etransitivity;[ apply Hc|].
    apply decreasingRemL.
  }
  clear Hc.
  unfold remainingEffReserveBals in Hr.
  case_match; auto;
    repeat rewrite updateKeyLkp3 in Hr;
    autorewrite with syntactic in Hr;
    fold EffReserveBals balanceOfAcA in *; unfold balanceOfAcA in *; simpl in *; try lia;[].
  case_match; auto;
    repeat rewrite updateKeyLkp3 in Hr;
    autorewrite with syntactic in Hr;
    fold EffReserveBals balanceOfAcA in *; unfold balanceOfAcA in *; simpl in *; try lia;[].
  case_match; auto;
    repeat rewrite updateKeyLkp3 in Hr;
    autorewrite with syntactic in Hr;
    fold EffReserveBals balanceOfAcA in *; unfold balanceOfAcA in *; simpl in *; try lia;[].
  autorewrite with iff in *.
  lia.
Qed.


Lemma inductiveStep  (latestState : AugmentedState) (tx: TxWithHdr) (extension: list TxWithHdr) :
  (forall txext, txext ∈ extension ->  txBlockNum txext - K ≤ txBlockNum tx ≤ txBlockNum txext)
  -> (forall txext, txext ∈ tx::extension ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (tx::extension)))
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
  apply execL in Hc; auto.
Qed.

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

Lemma fullBlockStep  (latestState : AugmentedState) (block1: list TxWithHdr) (block2: list TxWithHdr) :
  blockNumsInRange (block1++block2)
  -> consensusAcceptableTxs latestState (block1++block2)
  -> (forall txext, txext ∈ (block1++block2) ->  txCannotCreateContractAtEOAAddrWithPrivateKey txext (map sender (block1++block2)))
  -> (forall ac, ac ∈ (map sender (block1++block2)) -> hasCode latestState.1 ac = false)
  -> match execTxs latestState block1 with
     | None =>  False
     | Some si =>
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
  unfold execTx in *.
  destruct (validateTx latestState.1 hb1); simpl in *; try contradiction;[].
  pose proof (hasCodeFalsePresExec _ _ _ Heoa Hsc) as Hsci.
  remember (execValidatedTx latestState hb1) as si.
  simpl in *.
  pose proof (fun txext p => txCannotCreateContractAtEOAAddrWithPrivateKeyTrimHead _ _ _
                               (Heoa txext (elem_of_list_further _ _ _ p))).
  specialize (IH si ltac:(auto) ltac:(auto) ltac:(auto)).
  lapply IH.
  2:{
    intros.
    apply Hsci. set_solver.
  }
  intros.
  destruct (execTxs si block1) as [|]; try auto.
Qed.

Print Assumptions fullBlockStep.
(*
Axioms:
revertTxDelegationUpdCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := revertTx s tx) (ac : EvmAddr),
        addrDelegated sf ac =
        addrDelegated s ac && bool_decide (ac ∉ undels tx.1.2) || bool_decide (ac ∈ dels tx.1.2)
revertTx : StateOfAccounts → TxWithHdr → StateOfAccounts
execTxSenderBalCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → let sf := (evmExecTxCore s tx).1 in
      if addrDelegated s (sender tx)
      then True
      else
       balanceOfAc sf (sender tx) = (balanceOfAc s (sender tx) - (maxTxFee tx + value tx))%N
       ∨ balanceOfAc sf (sender tx) = (balanceOfAc s (sender tx) - maxTxFee tx)%N
execTxDelegationUpdCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := (evmExecTxCore s tx).1) (ac : EvmAddr),
        addrDelegated sf ac =
        addrDelegated s ac && bool_decide (ac ∉ undels tx.1.2) || bool_decide (ac ∈ dels tx.1.2)
execTxCannotDebitNonDelegatedNonContractAccountsCore :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → ∀ (sf := (evmExecTxCore s tx).1) (ac : EvmAddr),
        ac ≠ sender tx
        → if addrDelegated sf ac || hasCode sf ac
          then True
          else (balanceOfAc s ac ≤ balanceOfAc sf ac)%N
evmExecTxCore : StateOfAccounts → TxWithHdr → StateOfAccounts * list EvmAddr
changedAccountSetSound :
  ∀ (tx : TxWithHdr) (s : StateOfAccounts),
    reserveBalUpdateOfTx tx = None
    → let (sf, changedAccounts) := evmExecTxCore s tx in
      ∀ ac : EvmAddr, ac ∉ changedAccounts → sf ac = s ac
balanceOfRevert :
  ∀ (s : StateOfAccounts) (tx : TxWithHdr) (ac : EvmAddr),
    reserveBalUpdateOfTx tx = None
    → balanceOfAc (revertTx s tx) ac =
      (if bool_decide (ac = sender tx)
       then (balanceOfAc s ac - maxTxFee tx)%N
       else balanceOfAc s ac)

 *)


Lemma acceptableNil lastConsensedState:
  consensusAcceptableTxs lastConsensedState [].
Proof using.
  unfold consensusAcceptableTxs.
  intros.
  simpl.
  rewrite initResBal.
  lia.
Qed.
