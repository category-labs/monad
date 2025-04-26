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
Notation stable := valid. 
Import linearity.
Ltac slauto := misc.slauto1.
(*
  (slautot ltac:(autorewrite with syntactic; try solveRefereceTo)); try iPureIntro. *)
Hint Rewrite @lengthN_app @lengthN_one: syntactic.
Hint Rewrite @dropN_app: syntactic.
Notation bufsize := 256.
Opaque atomicR.
Opaque Nat.modulo.
Existing Instance learn_atomic_val_UNSAFE.


(* TODO: delete? *)
Opaque coPset_difference.

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo3.module ⊧ CU}.
  Context {hsssb: fracG bool _}.
  Context {hssslz: fracG (list Z) _}.
  Context {hsssln: fracG N _}.
  
(* roles of logical locations:
 - track info not in c++ variables, e.g. progress towards an op (typicall more abstract that program counter)
 - expose a higher-level state to the client
 - enforce complex protocols.
   *)
  Record spscid :=
    {
      invId : gname;
      producedListLoc: gname;
      numConsumedLoc: gname;
      inProduceLoc: gname;
      inConsumeLoc: gname;
    }.

  Definition boolZ (b: bool) : Z := if b then 1 else 0.
  
Definition SPSCInv (cid: spscid) (P: Z -> mpred) : Rep :=
  Exists (producedL: list Z) (numConsumed: N) (inProduce inConsume: bool),
    let numProduced : N  := lengthN producedL in
    let numConsumedAll: Z := (numConsumed + boolZ inConsume) in
    let numProducedAll: Z := (numProduced + boolZ inProduce) in
    let numConsumable : Z := (lengthN producedL - numConsumed) in
    let numFreeSlotsInCinv: Z := (bufsize- numConsumable - boolZ inProduce) in
    let currItems := dropN (Z.to_N numConsumedAll) producedL in
    pureR (inProduceLoc cid |--> logicalR (1/2) inProduce)
    ** [| numConsumedAll <= numProduced
          /\ numProducedAll - numConsumed <= bufsize - 1 |]
    ** pureR (inConsumeLoc cid |--> logicalR (1/2) inConsume)
    ** pureR (producedListLoc cid |--> logicalR (1/2) producedL)
    ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
    ** _field "SPSCQueue::head_"
        |-> atomicR uint 1 (numConsumed `mod` bufsize)
    ** _field "SPSCQueue::tail_"
        |-> atomicR uint 1 (numProduced `mod` bufsize)
    **
    (* ownership of active cells *)
      ([∗ list] i↦  item ∈ currItems,
        pureR (P item)
        ** _field "SPSCQueue::buffer_".["int" ! ((numConsumedAll + i) `mod` bufsize)]
           |-> primR "int"  1 (Vint item))
    (* ownership of inactive cells *)
     ** ([∗ list] i↦  _ ∈ (seqN 0 (Z.to_N numFreeSlotsInCinv)),
        _field "SPSCQueue::buffer_".["int" ! (numProducedAll + i) `mod` bufsize ]
        |-> anyR "int" 1)
.
 
Definition ProducerR (cid: spscid) (P: Z -> mpred) (produced: list Z): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
  ** pureR (inProduceLoc cid |--> logicalR (1/2) false)
  ** pureR (producedListLoc cid |--> logicalR (1/2) produced)
  ** structR "SPSCQueue" (1/2).

Definition ConsumerR (cid: spscid) (P: Z -> mpred) (numConsumed:N): Rep :=
  cinvr (invId cid) (1/2) (SPSCInv cid P)
  ** pureR (inConsumeLoc cid |--> logicalR (1/2) false)
  ** pureR (numConsumedLoc cid |--> logicalR (1/2) numConsumed)
  ** structR "SPSCQueue" (1/2).


(** e.g. P := fun v:Z => packetArrP.["Packet" ! v] |-> PacketR 1 nwPacket *) 
cpp.spec "SPSCQueue::produce(int)" as produceqw with (fun (this:ptr)=>
  \arg{value} "value" (Vint value)
  \pre{(lpp: spscid) (produced: list Z) (P: Z -> mpred)}
    this |-> ProducerR lpp P produced
  \pre [| Timeless1 P |]
  \pre P value
  \post{retb:bool} [Vbool retb]
     if retb
     then this |-> ProducerR lpp P (produced++[value])
     else this |-> ProducerR lpp P produced ** P value).

cpp.spec "SPSCQueue::consume(int&)" as consumeqw with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) }
    this |-> ConsumerR lpp P numConsumed
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \post{retb:bool} [Vbool retb]
    if retb
    then this |-> ConsumerR lpp P (1+numConsumed)
         ** Exists consumev:Z,
              valuep |-> primR "int" 1 consumev
                ** P consumev
    else valuep |-> anyR "int" 1
         ** this |-> ConsumerR lpp P numConsumed).


Lemma spsc_mod_iff (len numConsumed:N):
  (numConsumed <= len /\ len - numConsumed <= bufsize - 1) ->
  len = Z.to_N (Z.of_N numConsumed + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256.
Proof using.
  clear.
  intros.
  split; intros Hyp.
  - subst. autorewrite with syntactic. Arith.arith_solve.
  - apply (add_mod_both_sides 255) in Hyp; try lia.
    replace (len `mod` 256 + 1 + 255) with (len `mod` 256 + 256) in Hyp by lia.
    revert Hyp.
    mod_simpl_aux faster_lia.
    intros Hyp.
    apply modulo.zmod_inj in Hyp; try nia.
Qed.

Lemma spsc_mod_iff1 (len numConsumed:N) bl bc:
  (numConsumed + boolZ bc <= len /\ len + boolZ bl  - numConsumed <= bufsize - 1) ->
  len = Z.to_N (Z.of_N numConsumed + 255)
  <-> (len `mod` 256 + 1) `mod` 256 = Z.of_N numConsumed `mod` 256.
Proof using.
  intros.
  apply spsc_mod_iff.
  destruct bc, bl;  simpl in *; try nia.
Qed.

(*
Hint Resolve ownhalf_combineF : br_opacity.
Hint Resolve ownhalf_splitC : br_opacity.
Ltac renValAtLoc' loc name:=
  IPM.perm_left ltac:( fun L _ =>
    match L with
    | loc |--> logicalR _ ?v =>
        rename v into name
    end).
Tactic Notation "renValAtLoc" open_constr(loc) "into" ident(name) :=
  renValAtLoc' loc name.
 *)

Remove Hints ownhalf_combineF: br_opacity.
Hint Resolve UNSAFE_read_prim_cancel: br_opacity.

Lemma produceqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- produceqw.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  go.
  unfold ProducerR. go.
  unfold SPSCInv. go.
  callAtomicCommitCinv.
  renValAtLoc (inProduceLoc _) into inProduceAtLoadHead...
  (* inProduceAtLoadHead must be false because of \pre, imp: mentioned in array cell ownership *)
  Hint Resolve ownhalf_combineF: br_opacity.
  go... (* substituted by false everywhere, 0 *)
  ren_hyp producedL (list Z).
  ren_hyp numConsumed N.
  normalize_ptrs. go.
  pose proof (spsc_mod_iff1 (lengthN producedL) numConsumed false inConsume ltac:(auto)).
  (* now we already know whether queue is full *)
  destruct (decide (lengthZ producedL
                    = (numConsumed + (bufsize-1))))...
  { (* overflow . TODO: move the load of tail up so that both cases can share more proof *)
    closeCinvqs.
    go.
    ego. normalize_ptrs.
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    name_locals.
    go.
  }
  { (* not full. STABLE. consumer can only make it less full *)
    go... (* need to close cinv after head.load() *)
    wapply (logicalR_update (inProduceLoc lpp) true)...
    eagerUnifyU. go...
    closeCinvqs.
    go... (* because inProduce is true, invariant now needs to contain one less cell *)
    (* next time we open invariant, e.g. for tail.store(), we know inProduce was true,  *)
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
    go.
    autorewrite with syntactic...
    (* the civ is now fully closed.
       ownership of the atomics are full back in the cinv
       but we got buf[HEAD], to write to *)
    iModIntro.
    go.
    (* tail.load() *)
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    ego.
    iModIntro.
    go.
    (* wrote to the cell *)
    
    (* tail.store ((1+oldTail))%cap *)
    callAtomicCommitCinv.
    renValAtLoc (producedListLoc _) into producedL.
    
    go... (* physical loc (tail) updated. update logical locs and close inv *)
    wapply (logicalR_update
              (inProduceLoc lpp)
              false).
    eagerUnifyU. go.
    wapply (logicalR_update
              (producedListLoc lpp)
              (producedL++[value])).
    eagerUnifyU. go.
    closeCinvqs.
    go.
    autorewrite with syntactic.
    go.
    simpl.
    match goal with
      H: (Z.of_N ?n + boolZ inConsume <= _)%Z |- _ => rename n into numConsumedAtStore
    end.
(*    rename numConsumed into numConsumedHeadAtLoad. *)
    go.
    autorewrite with syntactic.
    rewrite big_opL_app. go.
    assert (Z.to_N(numConsumedAtStore + boolZ inConsume) - lengthN producedL = 0)%N as Hle.
    {
      destruct inConsume; simpl; try (Arith.arith_solve; fail).
    }
    rewrite -> Hle.
    simpl.
    go.
    normalize_ptrs.
    go.
    go.
    autorewrite with syntactic.
    rewrite length_dropN.
    autorewrite with syntactic.
    assert ((numConsumedAtStore + boolZ inConsume +
               (length producedL -
                  N.to_nat (Z.to_N (numConsumedAtStore + boolZ inConsume)))%nat) = lengthZ producedL) as Hew by ( unfold lengthN in *; simpl in *;destruct inConsume; try Arith.arith_solve).
    rewrite Hew. go.
    icancel (cancel_at this);[
        (repeat (try f_equiv; intros; hnf; try lia)) |].
    go.
    iModIntro.
    go.
  }
Qed.

Set Default Goal Selector "!".
Lemma consumeqprf: denoteModule module
                  ** uint_store_spec
                  ** uint_load_spec
                  |-- consumeqw.
Proof using MODd with (fold cQpc; normalize_ptrs).
  verify_spec'.
  go.
  unfold ConsumerR. go.
  unfold SPSCInv. go.
  callAtomicCommitCinv.
  ren_hyp producedL (list Z).
  ren_hyp numConsumed N.
  progress normalize_ptrs. go.
  destruct (decide (lengthZ producedL = (numConsumed))).
  { (* queue is empty: exact same proof as before  *)
    closeCinvqs.
    go.
    ego. normalize_ptrs.
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    name_locals.
    go.
  }
  {
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
    assert (numConsumed + 1 <= lengthN producedL) by lia.
    rewrite (dropNaddle 0); try nia.
    simpl. go.
    icancel (cancel_at this).
    {
      repeat (f_equiv; intros; hnf; try lia).
    }
    go. normalize_ptrs.
    progress autorewrite with syntactic.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go.
    wp_if.
    1:{ intros. apply False_rect.
        apply n.
        apply modulo.zmod_inj in p; try nia.
        destruct _v_1; simpl in *; try nia.
    }
    go.
    callAtomicCommitCinv.
    go.
    wapply (logicalR_update (inConsumeLoc lpp) false). eagerUnifyU. go.
    wapply (logicalR_update (numConsumedLoc lpp) (1+_v_4)%N). eagerUnifyC. go.
    closeCinvqs.
    go.
    misc.slauto1.
    replace ((Z.to_N (Z.of_N _v_4 + 1))) with (1 + _v_4)%N by lia.
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
    {
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
    IPM.perm_left_spatial ltac:(fun L n =>
      match L with
      | context [.["int"! ?li]] => 
          IPM.perm_right ltac:(fun R n =>
               match R with
               | context [_ .["int"! ?ri] |-> anyR _ _] => assert (li=ri) as Heqq
               end
               )
      end);
      [| repeat rewrite <- Heqq; misc.slauto1; iModIntro; go].
       apply add_mod_lhsc; try lia.
       f_equiv.
       lia.
    }
  }
 Qed.

cpp.spec "SPSCQueue::consume(int&)" as consumeqw2 with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) }
    this |-> ConsumerR lpp P numConsumed
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  \pre{numProducedCurrent:N} emp
  \post{retb} [Vbool retb]
    [| if decide (numConsumed < numProducedCurrent)
       then retb =true else Logic.True |]
    ** if retb
       then this |-> ConsumerR lpp P (1+numConsumed)
            ** Exists consumev:Z, valuep |-> primR "int" 1 consumev ** P consumev
       else valuep |-> anyR "int" 1
            ** this |-> ConsumerR lpp P numConsumed).

cpp.spec "SPSCQueue::consume(int&)" as consumeq3 with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) } this |-> ConsumerR lpp P numConsumed
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  (* despite ∃, the value remains constant during the call unless the callee chooses to change it *)
  \pre{numProducedLb:N} emp (* numProducedLb <= number of items produced so far *)
  \post{retb} [Vbool retb]
    [| if decide (numConsumed < numProducedLb) then retb =true else Logic.True |]
    ** if retb
       then this |-> ConsumerR lpp P (1+numConsumed)
            ** Exists consumev:Z, valuep |-> primR "int" 1 consumev ** P consumev
       else valuep |-> anyR "int" 1
            ** this |-> ConsumerR lpp P numConsumed).

cpp.spec "SPSCQueue::consume(int&)" as consumeq2 with (fun (this:ptr)=>
  \arg{valuep} "value" (Vptr valuep)
  \pre{(lpp: spscid) (P: Z -> mpred) (numConsumed: N) }
    this |-> ConsumerR lpp P numConsumed
  \pre [| Timeless1 P |]
  \pre valuep |-> anyR "int" 1
  (* despite ∃, producedL constant during the call unless the callee chooses to change it *)
  \pre{numProducedLb:N} ∃ (producedL: list Z),
          (producedListLoc lpp |--> logicalR (1/4) producedL)
          ** [| numProducedLb < length producedL  |]
  \post{retb} [Vbool retb]
    [| if decide (numConsumed < numProducedLb) then retb =true else Logic.True |] **
    if retb
    then this |-> ConsumerR lpp P (1+numConsumed)
         ** Exists consumev:Z, valuep |-> primR "int" 1 consumev ** P consumev
    else valuep |-> anyR "int" 1
         ** this |-> ConsumerR lpp P numConsumed).


(** need a way for threads to make "stable" assumption about the possible values owned by other threads:

  current producedL = [1,2,3] : stable for producer, not for consumer 
  [1,2,3] is a prefix of current producedL  : stable for everyone
 *)
(** ownership of ghost locations can be custom-defined: CMRA (commutative monoid resource algebra)
 *)

End with_Sigma.

