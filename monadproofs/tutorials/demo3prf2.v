(* font +- : C-x C -, then - or + many times,
                | release all here*) 

Require Import monad.tutorials.demo3.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.proofs.misc.
Require Import monad.tutorials.demomisc.
Require Import monad.tutorials.atomic_specs.
Require Import monad.tutorials.demoprf.
Require Import monad.proofs.stsg.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Import Verbose.
Import linearity.
Require Import monad.tutorials.demo3prf.
Ltac slauto := misc.slauto1.
Opaque atomicR.
Opaque Nat.modulo.
Existing Instance learn_atomic_val_UNSAFE.


(* TODO: delete? *)
Opaque coPset_difference.

(* Agnostic to how many producers/consumers there are *)
Module QueueModel.
Import sts.
Notation capacity := 255.
Record State :=
  {
    produced: list Z;
    numConsumed: N; (* <= length produced *)
  }.
(* we wanted to assert
  numConsumedLb <= numConsumed

  because the state is only updated in a certain way.
  formally enforce that.
  step defines the state can step.
 *)

Definition full (s: State) : Prop :=
  lengthZ (produced s) - numConsumed s = capacity.

Definition empty (s: State) : Prop :=
  lengthZ (produced s) = numConsumed s.

Inductive Token := Producer | Consumer.

Inductive step : State -> Token -> State -> Prop :=
| produce: forall (newItem:Z) (prev: State),
    (¬ full prev) -> step
                       prev
                       Producer (* only producer can do this *)
                       {| produced := (produced prev) ++ [newItem];
                         numConsumed := numConsumed prev |}
| consume: forall (prev: State),
    (¬ empty prev) -> step
                        prev
                        Consumer (* only consumer can do this *)
                        {| produced := produced prev;
                          numConsumed := 1+ numConsumed prev |}.
  
Definition spsc : stsT :=
  @stsg.Sts State Token
    (fun tokens_owned init_state final_state =>
       ∃ role, role ∈ tokens_owned /\  step init_state role final_state).


End QueueModel.
Notation sts_auth := (@sts_auth QueueModel.spsc).
Notation sts_frag := (@sts_frag QueueModel.spsc).

Import QueueModel.
Lemma closed_if (S: sts.states spsc) (mytoks: sts.tokens spsc):
  (∀ s1 s2 otherTok, otherTok ∉ mytoks → s1 ∈ S → step s1 otherTok s2 ->  s2 ∈ S)
  -> sts.closed S mytoks.
Proof.
  clear.
  intros Hp.
  apply closed_iff.
  intros.
  hnf in H1.
  forward_reason.
  hnf in H1l.
  forward_reason.
  specialize (Hp s1 s2 role ltac:(set_solver) ltac:(set_solver) ltac:(auto)).
  auto.
Qed.

Ltac solveClosed:=
  apply closed_if;
  intros ? ? ? Hdis Hin Hstep;
  rewrite -> elem_of_PropSet in *;
  forward_reason;
  inverts Hstep; simpl in *; autorewrite with syntactic in *; simpl in *;
  try split_and !; eauto with list; try lia; try set_solver +.


Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo3.module ⊧ CU}.
  Context {hsssb: fracG bool _}.
  Context `{sss: !stsG (QueueModel.spsc)}.


Locate "|-->".
Check @own.
Print cmra. (** Commutative Monoid Resource Algebra *)
Check @logicalR.
Check frac.fracR.
(** Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning
Monoids and Invariants are all you need.
*)
(** iris.pdf, section 3.2, then 3.7 *)

(*
State: Type
stepRel: State -> State -> Prop

State: Type
Token: Type 
stepRel: State -> Token ->  State -> Prop
[QueueModel.step]
[step]
*)


Import sts.
Import QueueModel.
Print sts.car. (* After [step] *)
  
(* in prev cinv:
   (inConsumeLoc cid |--> logicalR (1/2) inConsume)
   (producedListLoc cid |--> logicalR (1/2) producedL)

Record State :=
  {
    produced: list Z;
    numConsumed: N; (* <= length produced *)
  }.

now, single ghost loc (g) stores both:

 *)
Example e0auth (g:gname) (s: State) (toks: tokens spsc): mpred :=
  g |--> sts_auth s toks. (* says: current state of g is s and ownership of toks *)

Example e0frag (g:gname) (S: propset State) (toks: tokens spsc): mpred :=
  g |--> sts_frag S toks. (* says: current state of g is ∈ S and ownership of toks *)

Example e1 (g:gname) : mpred :=
  g |--> sts_auth {| produced := [4]; numConsumed:= 0 |} ∅.

Check logicalR_update. (* arbitrary update allowed *)

Corollary update_lloc_1step (g:gname) (s sf: State) (toks: tokens spsc) tok:
  step s tok sf -> tok ∈ toks ->
    g |--> sts_auth s  toks |-- |==>
    g |--> sts_auth sf toks.
Proof using.
  intros.
  apply update_lloc.
  eapply rtc_l;[| apply rtc_refl].
  hnf. eexists _; split; [| reflexivity].
  hnf. eexists _.
  eauto.
Qed.

Example update_lloc2 (g:gname) :
    g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  {[ Producer ]} |-- |==>
    g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  {[ Producer ]}.
Proof using.
  apply update_lloc_1step with (tok:=Producer);[| set_solver].
  apply: produce. unfold full. simpl. lia.
Qed.

Example update_lloc_unprovable (g:gname) :
    g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  {[ Consumer ]} |-- |==>
    g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  {[ Consumer ]}.
Proof using.
  eapply update_lloc_1step.
  2: reflexivity.
Abort.

Example update_lloc_unprovable (g:gname) :
   g |--> sts_auth {| produced:= [9]; numConsumed :=0 |}  ⊤ |-- |==>
   g |--> sts_auth {| produced:= [];  numConsumed :=0 |}  ⊤.
Abort.
  
(* stable is formalized as closed *)
Lemma closedb lp nc : closed {[ s : state spsc | lp <= lengthN (produced s) /\ nc<= numConsumed s ]} ∅.
Proof using.
  apply closed_if.
  intros ? ? ? Hdis Hin Hstep.
  rewrite -> elem_of_PropSet in *.
  inverts Hstep; simpl; try lia.
  autorewrite with syntactic.
  lia.
Qed.


(** example of frag: *)
Example gen_frag_out_of_thin_air1 toks g:
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks) |--
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks)
  ** (g |--> sts_frag {[ s | [9;8] `prefix_of` (produced s) /\ 1<= numConsumed s ]} ∅).
Proof using.
  iIntrosDestructs.
  hideRhs.
  assert (toks ≡ ∅  ∪ toks) as Heq by (set_solver +).
  rewrite Heq.
  rewrite <- sts_op_auth_fragg; [ | try set_solver + | | ].
  {
    unhideAllFromWork.
    rewrite own_op.
    go.
    eagerUnifyU.
    go.
  }
  {
    rewrite -> elem_of_PropSet in *.
    simpl. split; reflexivity.
  }
  simpl...
  solveClosed.
Qed.

Example gen_frag_out_of_thin_air toks g:
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks) |--
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} toks)
  ** (g |--> sts_frag {[ s | 2 <= lengthN (produced s) /\ 1<= numConsumed s ]} ∅).
Proof using.
  iIntrosDestructs.
  hideRhs.
  assert (toks ≡ ∅  ∪ toks) as Heq by (set_solver +).
  rewrite Heq.
  rewrite <- sts_op_auth_fragg; [ | try set_solver + | | ].
  {
    unhideAllFromWork.
    rewrite own_op.
    go.
    eagerUnifyU.
    go.
  }
  {
    rewrite -> elem_of_PropSet in *.
    simpl. split; reflexivity.
  }
  simpl...
  solveClosed.
Qed.

Example dupl_tokenfree_frag g:
  let m:=
    (g |--> sts_frag {[ s | [9;8] `prefix_of` (produced s)
                            /\ 1<= numConsumed s ]} ∅) in
  m |-- m ** m.
Proof using.
  simpl.
  rewrite frag_frag_combine2.
  go.
  iPureIntro.
  solveClosed.
Qed.

(* general form:*)
Check auth_frag_together.
(* -> opening inv, <- closing inv  *)
Check auth_frag_together2.

Example  unstable_prod1:
  stable (sts_frag
            {[s: state spsc | produced s =[] ]}
            {[Consumer]}
    )
  -> False.
Proof.
  clear.
  intros Hc.
  hnf in Hc.
  apply proj1 in Hc.
  rewrite <- closed_iff in Hc.
  setoid_rewrite elem_of_PropSet in Hc.
  (* conterexample: *)
  specialize (Hc
                {| produced :=[]; numConsumed := 0 |}
                {| produced :=[2]; numConsumed := 0 |}
                {[Producer ]}
                ltac:(set_solver)
                ltac:(auto)
             ).
  lapply Hc.
  { set_solver. }
  {
    hnf.
    exists {[Producer ]}.
    split; try set_solver.
    hnf.
    exists Producer.
    split; try set_solver.
    apply (produce 2).
    unfold full. simpl in *. lia.
  }
Qed.

Example closed2: closed {[ s : state spsc | produced s =  [9;8] ]} {[ Producer ]}.
Proof using.
  clear.
  solveClosed.
  set_solver.
Qed.
  
Example gen_frag3 g:
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} {[ Producer ]}) |--
  (g |--> sts_auth {| produced:= [9;8]; numConsumed :=1 |} ∅)
  ** (g |--> sts_frag {[ s | produced s =  [9;8] ]} {[ Producer ]})
  ** (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 1<= numConsumed s ]} ∅).
Proof using.
  rewrite -> gen_frag_out_of_thin_air at 1.
  go.
  rewrite auth_frag_together2.
  go.
  rewrite -> elem_of_PropSet. simpl.
  iPureIntro.
  split; auto.
  apply closed2.
Qed.


Open Scope bi_scope.
Example consumer_open_cinv g s:
  (g |--> sts_auth s ∅)
  ∗ (g |--> sts_frag {[ s | numConsumed s  =  1%N ]} {[ Consumer ]})
  ∗ (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 1<= numConsumed s ]} ∅)
  ⊢
    (g |--> sts_auth s {[ Consumer ]})
    ∗ [| numConsumed s = 1%N /\ 2<= lengthN (produced s)|].
Proof using.
  rewrite frag_frag_combine.
  go.
  iStopProof.
  rewrite auth_frag_together.
  repeat rewrite right_id.
  repeat rewrite elem_of_intersection.
  repeat rewrite -> elem_of_PropSet. simpl.
  go.
Qed.
(* the consumer can now guarantee success as now it knows there is atleast 1 consumed element *)  

(* update during the store to head in consumer, before closing inv *)
Example consumer_upd g s (learned: numConsumed s = 1%N /\ 2<= length (produced s)):
  (g |--> sts_auth
            s
            {[ Consumer ]}) |-- |==>
  (g |--> sts_auth
            {| produced := produced s; numConsumed := 2 |}
            {[ Consumer ]}).
Proof using.
  intros.
  apply update_lloc_1step with (tok := Consumer);[|set_solver].
  destruct s; simpl in *.
  forward_reason.
  subst.
  constructor.
  unfold empty.
  unfold lengthN.
  simpl.
  lia.
Qed.

Example gen_frag4 g p (learned: 2<= lengthN p):
(g |--> sts_auth {| produced := p; numConsumed := 2 |} {[ Consumer ]})  |--
(g |--> sts_auth {| produced := p; numConsumed := 2 |} ∅)
  ** (g |--> sts_frag {[ s | numConsumed s =  2%N ]} {[ Consumer ]})
  ** (g |--> sts_frag {[ s | 2<= lengthN (produced s) /\ 2 <= numConsumed s ]} ∅).
Proof using.
  clear MODd.
  rewrite assoc.
  rewrite auth_frag_together2.
  rewrite -> auth_frag_together_dupl2 at 1.
  {
    go.
    eagerUnifyC.
    rewrite -> elem_of_PropSet. simpl.
    iPureIntro.
    split; auto.
    apply closed_if.
    intros.
    rewrite -> elem_of_PropSet in *. simpl in *.
    inverts H1; auto; set_solver.
  }
  {
    rewrite -> elem_of_PropSet. simpl.
    lia.
  }
  {
    apply closedb.
  }
Qed.

  Record spscid :=
    {
      invId : gname;
      stsLoc: gname;
      inProduceLoc: gname;
      inConsumeLoc: gname;
    }.

  (*
Definition SPSCInv2 (cid: spscid) (P: Z -> mpred) : Rep :=
  Exists (producedL: list Z) (numConsumed: N) (inProduce inConsume: bool),
    let numProduced : N  := lengthN producedL in
    let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
    let numProducedAll: Z := (numProduced + boolZ inProduce) in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable - boolZ inProduce) in
    let currItems := dropN (Z.to_N numConsumedAll) producedL in
    pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
       (* actual capacity is 1 less than bufsize (the size of the array) because we need to distinguish empty and full *)
    ** [| numConsumedAll <= numProduced /\ numProducedAll - numConsumed <= bufsize - 1 |]
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
    ** pureR (producedListLoc cid |--> logicalR (1/2) producedL)
    ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "SPSCQueue::buffer_".[ "int" ! bufsize ] |-> validR .
    *)

  (* TODO: move to top and use everywhere *)
  Notation "[0 ,.., n ]" := (seqN 0 (Z.to_N n)).
  Example simplList {T} (P: Z-> T-> mpred) (a b c: T):
    ([∗ list] i ↦ v ∈ [a;b;c], P i v)%I |-- P 0 a ** P 1 b ** P 2 c.
  Proof. go. Qed.
  
Definition SPSCInv (cid: spscid) (P: Z -> mpred) : Rep :=
  Exists (s: State) (inProduce inConsume: bool),
    let producedL := produced s in
    let numConsumed := numConsumed s in
    let numProduced : N  := lengthN producedL in
    let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
    let numProducedAll: Z := (numProduced + boolZ inProduce) in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable - boolZ inProduce) in
    let currItems := dropN (Z.to_N numConsumedAll) producedL in
    pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
    ** [| numConsumedAll <= numProduced /\ numProducedAll - numConsumed <= bufsize - 1 |]
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
    ** pureR (stsLoc cid |--> sts_auth s ∅) (* no tokens *) 
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
      ([∗ list] i↦ item ∈ currItems, pureR (P item)
          ** _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` bufsize)]
              |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i ↦ _ ∈ [0,..,numFreeSlotsInCinv],
         _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` bufsize ]
            |-> anyR "int" 1).

(*
Definition ProducerR (cid: spscid) (P: Z -> mpred) (produced: list Z): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
    ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
    ** pureR (producedListLoc cid |--> logicalR (1/2) produced).
    *)

Definition ProducerR (cid: spscid) (P: Z -> mpred) (producedL: list Z): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
  ∗ pureR (inProduceLoc cid |--> logicalR (1/2) false)
  ∗ pureR (stsLoc cid |--> sts_frag {[s | produced s = producedL]} {[ Producer ]})
  ∗ structR "SPSCQueue" (1/2).

Definition ConsumerR (cid: spscid) (P: Z -> mpred) (nmConsumed:N): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
  ∗ pureR (inConsumeLoc cid |--> logicalR (1/2) false)
  ∗ pureR (stsLoc cid |--> sts_frag {[s | nmConsumed = numConsumed s]} {[Consumer]})
  ∗ structR "SPSCQueue" (1/2).

cpp.spec "SPSCQueue::consume(int&)" as consumests with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (nConsumed: N) }
    this |-> ConsumerR lpp P nConsumed
  \pre{numProducedLb: N}
    stsLoc lpp |--> sts_frag {[ s | numProducedLb <= lengthZ (produced s)]} ∅

  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \post{retb:bool} [Vbool retb]
    [| if decide (nConsumed < numProducedLb) then retb =true else Logic.True |] **
    if retb
    then this |-> ConsumerR lpp P (1+nConsumed)
         ** Exists consumev:Z, valuep |-> primR "int" 1 consumev ** P consumev
    else valuep |-> anyR "int" 1
         ** this |-> ConsumerR lpp P nConsumed).

cpp.spec "SPSCQueue::produce(int)" as producests with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \pre{(lpp: spscid) (P: Z -> mpred) (produced: list Z)}
            this |-> ProducerR lpp P produced
  \pre{numConsumedLb: N}
    stsLoc lpp |--> sts_frag {[ s | numConsumedLb <= numConsumed s ]} ∅
  \pre [| Timeless1 P |]
  \pre P value
  \post{retb:bool} [Vbool retb]
    [| if decide (lengthN produced < numConsumedLb + capacity) then retb =true else Logic.True |] **
    if retb
    then this |-> ProducerR lpp P (produced++[value])
    else this |-> ProducerR lpp P produced ** P value ).

Definition combineAuthFragFwd:= [FWD->](@auth_frag_together2).
Hint Resolve combineAuthFragFwd: br_opacity.
Hint Rewrite @elem_of_PropSet: iff.



Lemma auth_close_inv_producer (g: gname) s:
  (g |--> sts_auth s {[Producer]})
    |-- ((g |--> sts_frag {[ sf | produced sf = produced s]} {[ Producer ]})
           ** (g |--> sts_frag {[ sf | numConsumed s <= numConsumed sf]} ∅))
        ** (g |--> sts_auth s ∅) .
Proof using.
  clear.
  go.
  bwdRev auth_frag_together2.
  bwdRev auth_frag_together.
  rewrite left_id. go.
  iPureIntro.
  split_and !; try lia; try auto; try set_solver;
    solveClosed.
  set_solver.
Qed.

Definition close_invstsg_C := [CANCEL] auth_close_inv_producer. 
Hint Resolve close_invstsg_C: br_opacity.

(* TODO move up *)
Lemma spsc_mod_iff1 (s:State) bl bc:
  let len := lengthN (produced s) in
  (numConsumed s + boolZ bc <= len /\ len + boolZ bl  - numConsumed s <= bufsize - 1) ->
  len = Z.to_N (Z.of_N (numConsumed s) + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N (numConsumed s) `mod` 256.
Proof using.
  intros.
  eapply spsc_mod_iff1; eauto.
Qed.
Lemma spsc_mod_iff2 (s:State) bl bc:
  let len := lengthZ (produced s) in
  (numConsumed s + boolZ bc <= len /\ len + boolZ bl  - numConsumed s <= bufsize - 1) ->
  len = (Z.of_N (numConsumed s) + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N (numConsumed s) `mod` 256.
Proof using.
  simpl.
  intros.
  pose proof (spsc_mod_iff1 s bl bc H) as Hx.
  simpl in Hx.
  lia.
Qed.


(* TODO: upstream *)
Arguments cinvq {_} {_} {_} {_} {_} {_} {_}.

Set Default Goal Selector "!".

Lemma forget_empty_frag (g: gname) S:
  (g |--> sts_frag S ∅) |-- (emp:mpred).
Proof using Sigma. apply lose_resources. Qed.

Lemma produceqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- producests.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  misc.slauto.
  unfold ProducerR. go.
  unfold SPSCInv. go.
  go.
  callAtomicCommitCinv.
  go.
  rewrite -> elem_of_PropSet in *.
  normalize_ptrs. go.
  subst.
  ren_hyp slh State.
  simpl in *.
  pose proof (spsc_mod_iff2 slh false inConsume ltac:(simpl; lia)). simpl in *.
  destruct (decide (lengthZ (produced slh) = (numConsumed slh + (bufsize-1)))).
  {
    closeCinvqs.
    go.
    ego. normalize_ptrs.
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    rewrite -> elem_of_PropSet in *.
    closeCinvqs.
    go.
    iModIntro.
    closedN.
    name_locals.
    unhideAllFromWork.
    repeat rewrite -> forget_empty_frag.
    repeat  match goal with
            | H: State |- _ => destruct H
            end; simpl in *; forward_reason; subst; simpl in *.
    misc.slauto.
    case_decide; auto;    try Arith.arith_solve.
  }
  {
    go.
    wapply (logicalR_update (inProduceLoc lpp) true). eagerUnifyU. go.
    closeCinvqs.
    go. normalize_ptrs.
    go.
    IPM.perm_left ltac:(fun L n =>
      match L with
      | context [seqN 0 ?l] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [seqN 0 ?r] => assert (l=1+r)%N as Heq
                                               by Arith.arith_solve
               end
               )
      end).
    rewrite Heq.
    rewrite N.add_1_l.
    rewrite seqN_S_start.
    go.
    closed.norm closed.numeric_types.
    rewrite <- (seqN_shift 0).
    work.
    rewrite big_opL_map.
    icancel (cancel_at this).
    {
      do 7 (f_equiv; intros; hnf).
      lia.
    }
    Arguments cinvq {_} {_} {_} {_} {_} {_} {_}.
    go...
    autorewrite with syntactic.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    rewrite -> elem_of_PropSet in *.
    closeCinvqs.
    go.
    ego.
    iModIntro.
      repeat  match goal with
            | H: State |- _ => destruct H
              end; simpl in *; forward_reason; subst; simpl in *.
    misc.slauto.
    callAtomicCommitCinv.
    go.
    rewrite -> elem_of_PropSet in *.
    go.
    wapply (logicalR_update (inProduceLoc lpp) false). eagerUnifyU. go.
    wapply (update_lloc_1step);[ | | eagerUnifyU];
        [reflexivity | apply (produce value) ; unfold full; Arith.arith_solve|].
    go.
    closeCinvqs.
    go.
    misc.slauto.
    simpl.
    ren_hyp stAtStore State.
    destruct stAtStore as  [producedL numConsumedAtStore].
    simpl in *.
    rename numConsumed0 into numConsumedHeadAtLoad.
    go.
    autorewrite with syntactic.
    rewrite big_opL_app. go.
    assert (Z.to_N(numConsumedAtStore + boolZ inConsume) - lengthN producedL = 0)%N as Hle by
      (destruct inConsume; simpl; try (Arith.arith_solve; fail)).
    rewrite Hle.
    simpl.
    go.
    normalize_ptrs.
    go.
    go.
    autorewrite with syntactic.
    rewrite length_dropN.
    autorewrite with syntactic.
    assert ((numConsumedAtStore + boolZ inConsume + (length producedL -
                                                       N.to_nat (Z.to_N (numConsumedAtStore + boolZ inConsume)))%nat) = lengthZ producedL) as Hew by ( unfold lengthN in *; simpl in *;destruct inConsume; try Arith.arith_solve).
    rewrite Hew. go.

    icancel (cancel_at this);[
        (repeat (try f_equiv; intros; hnf; try lia)) |].
    go.
    iModIntro.
    go.
    rewrite forget_empty_frag.
    case_decide; auto.
  }
Qed.

Lemma auth_close_inv_consumer (g: gname) s:
  (g |--> sts_auth s {[Consumer]})
    |-- ((g |--> sts_frag {[ sf | numConsumed s = numConsumed sf]} {[ Consumer ]})
           ** (g |--> sts_frag {[ sf | lengthZ (produced s) <= lengthZ (produced sf)]} ∅))
        ** (g |--> sts_auth s ∅) .
Proof using.
  clear.
  go.
  bwdRev auth_frag_together2.
  bwdRev auth_frag_together.
  rewrite left_id. go.
  iPureIntro.
  split_and !; try lia; try auto; try set_solver;
    solveClosed. set_solver.
Qed.

Ltac destructStates :=
    repeat  match goal with
            | H: State |- _ => destruct H
      end; simpl in *; forward_reason; subst; simpl in *.

Definition close_invstsgc_C := [CANCEL] auth_close_inv_consumer. 
Hint Resolve close_invstsgc_C: br_opacity.

Ltac callAtomicCommitCinv := misc.callAtomicCommitCinv;  try rewrite -> elem_of_PropSet in *.


Remove Hints combineAuthFragFwd: br_opacity.
Lemma consumeqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- consumests.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  misc.slauto.
  unfold ConsumerR. go.
  unfold SPSCInv. go.
  callAtomicCommitCinv.
  renValAtLoc (stsLoc _) into sAtLoad.
  Search sAtLoad.
  (* 2 frags *)
  Hint Resolve combineAuthFragFwd: br_opacity.
  go.
  rewrite -> elem_of_PropSet in *.
  Search sAtLoad.
  (* the main use of frag is to constrain the auth *)
  (* token gets deposited in auth, we get 2 facts *)
  ren_hyp slh State.
  normalize_ptrs. go.
   destruct (decide (lengthZ (produced slh) = (numConsumed slh))).
  { (* queue is empty: exact same proof as before  *)
    closeCinvqs.
    go.
    ego...
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    name_locals.
    destructStates. simpl in *.
    repeat rewrite -> forget_empty_frag.
    misc.slauto... (* cannot fail if lb *)
    case_decide; auto.
    apply False_rect.
    revert H0.
    fold (not (numConsumed0 < numProducedLb)).
    apply Zge_not_lt.
    nia. (* too many variables: each time we open invariant *)
  }
  {
    (*
Remove Hints close_invstsgc_C: br_opacity.
Hint Resolve close_invstsgc_C: br_opacity.
*)
    go.
    wapply (logicalR_update (inConsumeLoc lpp) true). eagerUnifyU. go.
    closeCinvqs.
    go. normalize_ptrs.
    go.
    autorewrite with syntactic.
    rewrite Z2N.inj_add; try nia.
    simpl.
    autorewrite with syntactic.
    simpl in *.
    destructStates.
    rename numConsumed0 into numConsumed.
    assert (numConsumed + 1 <= lengthN produced0) by lia.
    rewrite (dropNaddle 0); try nia.
    simpl. go.
    icancel (cancel_at this).
    {
      repeat (f_equiv; intros; hnf; try lia).
    }
    go...
    progress autorewrite with syntactic.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    misc.slauto.
    wp_if.
    1:{ intros. apply False_rect.
        apply n.
        apply modulo.zmod_inj in p; try nia.
        destruct inProduce; simpl in *; try nia.
    }
    misc.slauto.
    destructStates.
    callAtomicCommitCinv.
    go.
    ren_hyp stAtStore State.
    destruct stAtStore as  [numConsumed producedAtStore]. simpl in *.
    wapply (logicalR_update (inConsumeLoc lpp) false). eagerUnifyU. go.
    wapply (update_lloc_1step);[ | | eagerUnifyU];
      [reflexivity | apply (consume) ; unfold empty; try Arith.arith_solve|].
    go.
    closeCinvqs.
    go.
    misc.slauto1.
    simpl.
    normalize_ptrs.
    match goal with
      [ |- context[((Z.to_N (Z.of_N ?v + 1)))]] =>
        replace ((Z.to_N (Z.of_N v + 1))) with (1 + v)%N by lia
    end.
    repeat rewrite _at_big_sepL.
    icancel (@big_sepL_mono).
    {
      repeat (f_equiv; intros; hnf; try lia).
    }
    go.
    IPM.perm_left ltac:(fun L n =>
      match L with
      | context [seqN 0 ?l] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [seqN 0 ?r] => assert (l+1=r)%N as Heq by lia
               end
               )
      end).
    rewrite <- Heq.
    simpl.
    go.
    autorewrite with syntactic.
    rewrite seqN_app.
    go.
    rewrite big_opL_app. go.
    unfold seqN. simpl.
    unfold fmap.
    simpl.
    unfold lengthN in *.
    autorewrite with syntactic.
    repeat rewrite forget_empty_frag.
    IPM.perm_left_spatial ltac:(fun L n =>
      match L with
      | context [.["int"! ?li]] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [_ .["int"! ?ri] |-> anyR _ _] => assert (li=ri) as Heqq
               end
               )
      end);
      [| repeat rewrite <- Heqq; misc.slauto1; iModIntro; case_decide; go].
    apply add_mod_lhsc; try lia.
    f_equiv.
    lia.
  }
 Qed.

Record mpmcid :=
  {
    lockId : gname;
    stateLoc: gname; 
  }.

(* state ∃ quantified, just like cinv, no need for inProduce, inConsume:
  cinv holds always.
  lockcontent assertions need not hold between lock and unlock *)
Definition MPMCLockContent (cid: mpmcid) (P: Z -> mpred) : Rep :=
  Exists (s: State),
    let producedL := produced s in
    let numConsumed := numConsumed s in
    let numProduced : N  := lengthN producedL in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable) in
    let currItems := dropN (Z.to_N numConsumed) producedL in
    [| numConsumed <= numProduced /\ numProduced - numConsumed <= bufsize - 1 |]
    ** pureR (stateLoc cid  |--> sts_auth s ⊤) (* all tokens in lock *)
    ** _field "SPSCQueue::head_" |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_" |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
        pureR (P item)
        ** _field "SPSCQueue::buffer_".["int" ! ((numConsumed + i) `mod` bufsize)]
                                         |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),
           _field "SPSCQueue::buffer_".["int" ! (numProduced + i) `mod` bufsize ]
                                         |-> anyR "int" 1).

Require Import monad.tutorials.demo2prf.

(* no separate producerR or consumerR because they have the same limited knowledge/rights *)
Definition mpmcR (cid: mpmcid) (q:Qp) (P: Z -> mpred): Rep := as_Rep( fun (this:ptr) =>
  this ,, _field "MPMCQueue::lock"
      |-> LockR q (lockId cid) (this |-> MPMCLockContent cid P))
  ** structR "MPMCQueue" q.


(* like blockchain: all the specs says that my transaction was recorded in the history *)
cpp.spec "MPMCQueue::produce(int)" as mpmcproduce with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcR lpp q P
  \pre{producedPrefix: list Z}
    stateLoc lpp |--> sts_frag {[ s | producedPrefix `prefix_of` (produced s) ]} ∅
  \pre [| Timeless1 P |]
  \pre P value
  \post{retb:bool} [Vbool retb]
    if retb
    then Exists (newItems: list Z),
      (stateLoc lpp |--> sts_frag
         {[ s | producedPrefix++newItems++[value] `prefix_of` (produced s) ]} ∅)
    else emp).

cpp.spec "MPMCQueue::consume(int&)" as mpmcconsume with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcR lpp q P
  \pre{numConsumedLb: N}
    stateLoc lpp |--> sts_frag {[ s | numConsumedLb <= numConsumed s]} ∅
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \post{retb:bool} [Vbool retb]
    if retb
    then (Exists consumev:Z, valuep |-> primR "int" 1 consumev ** P consumev)
         ** (stateLoc lpp |--> sts_frag {[ s | 1+numConsumedLb <= numConsumed s]} ∅)
    else valuep |-> anyR "int" 1).

(* the above spec is ok for clients who use produce/consume in a maximallyy concurrent way and
   follow no additional discipline.

  what if a client wants to use it sequentially? postcond too weak !
    even if we have [mpmcR lpp 1 P], and push just after the constructor, the postcondition does not guarantee success


  next spec: grants the flexibility:
  - can allow multiple threads to call produce/consume concurrently
  - yet, if the client chooses to not race, they get stronger postconditions
  - almost anything in between

Logical atomic triples
 *)
Context {hsssst: fracG State _}.

(** back to logicalR from sts_auth, client chooses the protocol  *)
Definition MPMCLockContentLa (cid: mpmcid) (P: Z -> mpred) : Rep :=
  Exists (s: State),
    let producedL := produced s in
    let numConsumed := numConsumed s in
    let numProduced : N  := lengthN producedL in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable) in
    let currItems := dropN (Z.to_N numConsumed) producedL in
    [| numConsumed <= numProduced /\ numProduced - numConsumed <= bufsize - 1 |]
    ** pureR (stateLoc cid  |--> logicalR (1/2) s)
    ** _field "MPMCQueue::head_" |-> primR uint 1 (numConsumed `mod` bufsize)
    ** _field "MPMCQueue::tail_" |-> primR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
    ([∗ list] i↦  item ∈ currItems,
      pureR (P item) **
      _field "MPMCQueue::buffer_".["int" ! ((numConsumed + i) `mod` bufsize)] |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
    ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),  _field "MPMCQueue::buffer_".["int" ! (numProduced + i) `mod` bufsize ] |-> anyR "int" 1)
    ** _field "MPMCQueue::buffer_".[ "int" ! bufsize ] |-> validR.

Definition mpmcRla (cid: mpmcid) (q:Qp) (P: Z -> mpred): Rep :=
  as_Rep( fun (this:ptr) =>
  this |-> _field "MPMCQueue::lock" |-> LockR q (lockId cid) (this |-> MPMCLockContentLa cid P))
  ** structR "MPMCQueue" q.

Definition produceFinalState (s: State) (newItem: Z): State :=
  if decide (full s)
  then s
  else {| produced := (produced s) ++ [newItem];
         numConsumed := numConsumed s |}.

cpp.spec "MPMCQueue::produce(int)" as mpmcproduceseq with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcRla lpp q P
  \pre{s: State}
    stateLoc lpp |--> logicalR (1/2) s
  \pre [| Timeless1 P |]
  \pre P value
  \post [Vbool (negb (bool_decide (full s)))]
     (if decide (full s) then P value else emp)
     ** (stateLoc lpp |--> logicalR (1/2) (produceFinalState s value))).

(** SL: what is in the current state.
   extensional:
     the reasoning principle for physically atomic updates
     is made available for logical locations

   Quiz: what special reasoning does a physically atomic op allow?
 *)
cpp.spec "MPMCQueue::produce(int)" as mpmcproducela with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcRla lpp q P
  \pre{Q: State->mpred}
    AC << ∀ s : State, (stateLoc lpp |--> logicalR (1/2) s)>> @ ⊤, ∅
       << (stateLoc lpp |--> logicalR (1/2) (produceFinalState s value)),
           COMM Q s >>
  \pre [| Timeless1 P |]
  \pre P value
  \post{sJustBeforeCommit} [Vbool (negb (bool_decide (full sJustBeforeCommit)))]
     Q sJustBeforeCommit **
     if decide (full sJustBeforeCommit) then P value else emp ).


Opaque LockR.
Lemma producelaprf: denoteModule module
                  ** lock_spec
                  ** unlock_spec
                  |-- mpmcproducela.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  unfold mpmcRla.
  unfold MPMCLockContentLa.
  misc.slauto.
  useAC.
  progress go.
  ghost.
  go.
  wapply (logicalR_update (stateLoc lpp) (produceFinalState x value)). eagerUnifyU. go.
  ghost.
  use_wand.
  go.
  resume_use_wand.
  ghost.
  iModIntro.
  pose proof (spsc_mod_iff (lengthN (produced x)) (numConsumed x)  ltac:(lia)).
  wp_if.
  { (* full *)
    assert (full x) as Hf by admit.
    unfold produceFinalState.
    destruct (decide (full x)); try tauto.
    misc.slauto.
    iModIntro.
    go.
    iExists x. go.
    rewrite bool_decide_decide.
    destruct (decide (full x)); try tauto.
    simpl.
    go.
  }
  {
    go.
    iModIntro.
    assert (not (full x)) as Hf by admit.
    destruct x as [producedL numConsumed]. simpl in *.

    assert (Z.to_N (256 - (lengthZ producedL - numConsumed)) = (1 + Z.to_N (256 - (lengthZ producedL - numConsumed) - 1))%N) as Heq by lia.
    rewrite Heq.
    slauto.
    rewrite N.add_1_l.
    rewrite seqN_S_start.
    go.
    closedN.
    rewrite <- (seqN_shift 0).
    work.
    rewrite big_opL_map.
    normalize_ptrs.
    slauto.
    unfold produceFinalState.
    simpl.
    resolveDecide tauto.
    slauto.
    autorewrite with syntactic.
    (*
    match goal with
      [ |- context[((Z.to_N (Z.of_N ?v + 1)))]] =>
        replace ((Z.to_N (Z.of_N v + 1))) with (1 + v)%N by lia
    end. *)
    repeat rewrite _at_big_sepL.
    IPM.perm_left ltac:(fun L n =>
      match L with
      | context [seqN 0 ?l] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [seqN 0 ?r] => assert (l=r)%N as Heqw by lia
               end
               )
      end).
    rewrite <- Heqw.
    icancel (@big_sepL_mono).
    {
      repeat (f_equiv; intros; hnf; try lia).
    }
    go.
    simpl.
    autorewrite with syntactic.
    rewrite big_opL_app.
    unfold seqN. simpl.
    unfold fmap.
    simpl.
    go.
    assert ((numConsumed - lengthN producedL) = 0)%N as Hle by lia.
    rewrite Hle.
    simpl.
    go.
    normalize_ptrs.
    go.
    autorewrite with syntactic.
    rewrite length_dropN.
    
    IPM.perm_left_spatial ltac:(fun L n =>
      match L with
      | context [.["int"! ?li]] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [_ .["int"! ?ri] |-> _] => assert (li=ri) as Heqq
               end
               )
      end).
    {
      f_equiv.
      unfold lengthN in *.
      lia.
    }
    rewrite <- Heqq.
    go.
    ego.
    eagerUnifyU. go.
    rewrite bool_decide_decide.
    resolveDecide tauto.
    simpl. go.
  }
  Admitted.

cpp.spec "MPMCQueue::produce(int)" as mpmcproduceseqorig with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(lpp: mpmcid) (P: Z -> mpred) (q:Qp)}
    this |-> mpmcRla lpp q P
  \pre{s: State}
    stateLoc lpp |--> logicalR (1/2) s
  \pre [| Timeless1 P |]
  \pre P value
  \post [Vbool (negb (bool_decide (empty s)))]
     (stateLoc lpp |--> logicalR (1/2) (produceFinalState s value))).

Lemma derv: mpmcproducela  |--   mpmcproduceseq.
Proof using.
  clear MODd.
  unfold mpmcproducela,  mpmcproduceseq.
  unfold specify.
  apply _at_mono.
  apply cpp_specR_mono.
  unfold mpmcRla.
  go. ego.
  callAtomicCommitCinv.
  go.
  ghost.
  iModIntro.
  go.
Qed.

Record balancedId :=
  {
    mpid : mpmcid;
    unmatchedProduceCounter: bool -> gname;
    binvId: gname;
  }.

Arguments cinvq {_} {_} {_} {_}.
Context {hsssln: fracG N _}.

Definition BalancedProtocol (bid: balancedId) : mpred :=
  cinv (binvId bid) (1/2) (Exists (ss: State) (unmatchedProduceCounts: bool -> N),
    (stateLoc (mpid bid) |--> logicalR (1/2) ss)
  ** ([∗list] tid ∈ [true; false],
        unmatchedProduceCounter bid tid
        |--> logicalR (1/2) (unmatchedProduceCounts tid))
  ** [| forall tid, unmatchedProduceCounts tid <= capacity/2|]
  ** [| lengthZ (produced ss) - numConsumed ss
        = (unmatchedProduceCounts true) + (unmatchedProduceCounts false) |]
    ).

cpp.spec "MPMCQueue::produce(int)" as mpmcproduceprot with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \prepost{(bid: balancedId) (P: Z -> mpred) (q:Qp)}
     this |-> mpmcRla (mpid bid) q P
  \prepost BalancedProtocol bid
  \pre{(tid: bool) (unmatchedProduceCount:N)}
    (unmatchedProduceCounter bid tid  |--> logicalR (1/2) unmatchedProduceCount)
  \pre [| unmatchedProduceCount < capacity/2 |]
  \pre [| Timeless1 P |]
  \pre P value
  \post [Vbool true]
  (unmatchedProduceCounter bid tid  |--> logicalR (1/2) (1+unmatchedProduceCount)%N)).

Lemma derv2: mpmcproducela  |-- mpmcproduceprot.
Proof using.
  clear MODd.
  unfold mpmcproducela, mpmcproduceprot.
  unfold specify.
  apply _at_mono.
  apply cpp_specR_mono.
  unfold BalancedProtocol, mpmcRla.
  go. ego.
  callAtomicCommitCinv.
  go.
  pose proof (_H_1 true).
  pose proof (_H_1 false).
  destruct tid; go;
    [wapply (logicalR_update
               (unmatchedProduceCounter bid true)
               (1+unmatchedProduceCounts true)%N)
    | wapply (logicalR_update
                (unmatchedProduceCounter bid false)
                (1+unmatchedProduceCounts false)%N)];
    eagerUnifyU; go;
    closeCinvqs;
    go;
    evar (bt: N);
    evar (bf: N);
    iExists (fun b:bool => if b then bt else bf);
    go; 
    unfold bf, bt; go;
    closedN.
  {
    provePure.
    {
      intros. destruct tid; auto; try lia.
    }
    go.
    unfold produceFinalState.
    simpl.
    unfold full in *.
    case_decide;[Arith.arith_solve|].
    misc.slauto1.
    iModIntro.
    go.
  }
  {
    provePure.
    {
      intros. destruct tid; auto; try lia.
    }
    go.
    unfold produceFinalState.
    simpl.
    unfold full in *.
    case_decide;[Arith.arith_solve|].
    misc.slauto1.
    iModIntro.
    go.
  }
Qed.

(*
steps:
- connect c++ state to logical loc state
- all results of c++ functions must be described in terms of logical state
- write a sequential spec
- convert to AC spec by moving pre/post to appropriate boxes and adding Q
*)

End with_Sigma.
(*

broad goals:
- how specs make it precise what kind of concurrency is allowed
- set expectations for concurrent spec
- rich vocabulary for writing concurrent specs 
*)
