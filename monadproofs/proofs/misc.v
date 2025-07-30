Require Import QArith.
Require Import bluerock.auto.cpp.proof.

Require Import monad.proofs.stsg.
Require Import stdpp.gmap.
Require Import bluerock.auto.cpp.tactics4.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Lemma lose_resources `{cpp_logic} (P:mpred): P |-- emp.
Proof using.
  go.
Qed.
Notation logicalR := (to_frac_ag).
#[global] Hint Rewrite @repeat_length: syntactic.
#[global] Hint Rewrite @length_cons: syntactic.
#[global] Hint Rewrite @firstn_0: syntactic.
#[global] Hint Rewrite @lengthN_app: syntactic.
#[global] Hint Rewrite length_seq: syntactic.
#[global] Hint Rewrite Z2N.id using lia: syntactic.
#[global] Hint Rewrite @inj_iff using (typeclasses eauto): iff.
#[global] Hint Rewrite negb_if: syntactic.
#[global] Hint Rewrite bool_decide_eq_true_2 using (auto; fail): syntactic.
#[global] Hint Rewrite bool_decide_eq_false_2 using (auto; fail): syntactic.
#[global] Hint Rewrite @elem_of_cons: iff.
#[global] Hint Rewrite N.sub_diag : syntactic.
#[global] Hint Rewrite seqN_lengthN @lengthN_nil @seqN_S_start: syntactic.
#[global] Hint Rewrite orb_true_r: syntactic.
#[global] Hint Rewrite N_nat_Z: syntactic.
#[global] Hint Rewrite @left_id using (exact _): equiv.
#[global] Hint Rewrite @right_id using (exact _): equiv.
#[global] Hint Rewrite @elem_of_list_difference: iff.
#[global] Hint Rewrite @propset_singleton_equiv: equiv.
#[global] Hint Resolve array_combine_C: br_opacity.
#[global] Hint Rewrite @length_drop: syntactic.

Lemma head_app {T} (l lb: list T) (t:T) :
  head l = Some t -> head (l++lb) = head l.
Proof.
  clear.
  destruct l; simpl;  auto.
  intros. discriminate.
Qed.
    
Lemma skipnaddle {T} (def: T) (l: list T) (a:nat):
  (1+a <= length l) -> skipn a l = (nth a l def)::(skipn (1+a) l).
Proof using.
  intros Hl.
  rewrite <- skipn_skipn.
  rewrite <- tail_drop.
  erewrite -> drop_nth_head; try reflexivity.
  apply nth_error_nth'.
  lia.
Qed.
Lemma dropNaddle {T} (def: T) (l: list T) (i:N):
  (1+i <= lengthN l) -> dropN i l = (nth (N.to_nat i) l def)::(dropN (i+1)%N l).
Proof using.
  unfold dropN.
  intros.
  unfold lengthN in *.
  erewrite skipnaddle by lia.
  do 2 f_equal.
  lia.
Qed.
Lemma big_sepL_monoeq :
∀ {PROP : bi} {A : Type} (Φ Ψ : nat → A → bi_car PROP) (l lb : list A) (p: l=lb),
  (∀ (k : nat) (y : A), l !! k = Some y → Φ k y ⊢ Ψ k y) → ([∗ list] k↦y ∈ lb, Φ k y) ⊢ [∗ list] k↦y ∈ lb, Ψ k y.
Proof using. intros. subst. apply big_sepL_mono. auto. Qed.

Definition xxx:= [CANCEL] @big_sepL_monoeq.
Lemma seqN_app (len1 len2 start : N): seqN start (len1 + len2) = seqN start len1 ++ seqN (start + len1)%N len2.
Proof using.
  unfold seqN.
  repeat rewrite N2Nat.inj_add.
  rewrite seq_app.
  rewrite fmap_app.
  reflexivity.
Qed.
Lemma add_mod_lhsc (a b d:Z) :
  0 < d
  -> (a+d) `mod` d = b `mod` d
  -> (a) `mod` d = (b) `mod` d.
Proof using.
  intros Ha Hb.
  rewrite <- Hb.
  Arith.arith_solve.
Qed.


Lemma add_mod_both_sides (c a b d:Z) :
  0 < d
  -> a `mod` d = b `mod` d
  -> (a+c) `mod` d = (b+c) `mod` d.
Proof using.
  intros Ha Hb.
  rewrite Zplus_mod.
  symmetry.
  rewrite Zplus_mod.
  rewrite Hb.
  reflexivity.
Qed.

Lemma seqN_shift: ∀ start len : N, map N.succ (seqN start len) = seqN (N.succ start) len.
Proof using.
  intros.
  unfold seqN.
  rewrite map_fmap.
  rewrite N2Nat.inj_succ.
  rewrite <- seq_shift.
  rewrite map_fmap.
  repeat rewrite <- list_fmap_compose.
  unfold compose.
  f_equiv.
  hnf. intros. lia.
Qed.

  Ltac wapplyRev lemma:=
    try intros;
  idtac;
  [
    wapply (@bi.equiv_entails_1_2 _ _ _ (lemma)) || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _))
    || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _)) || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _))
    || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _ _)) || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _ _ _))
    || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _ _ _ _)) || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@bi.equiv_entails_1_2 _ _ _ (lemma _ _ _ _ _ _ _ _ _)) ].

Lemma cinvq_alloc `{cpp_logic} (E : coPset) (N : namespace) (P : mpred) :
  WeaklyObjective P → ▷ P |-- |={E}=> ∃ γ : gname, cinvq N γ 1 P.
Proof.
  intros.
  unfold cinvq.
  wapply (cinv_alloc E N P).
  work.
  iModIntro.
  ework.
  eagerUnifyU. go.
Qed.

Definition cQpc := cQp.mk false.
Lemma mut_mut_add: ∀ q1 q2 : Qp, cQp.mut (q1 + q2) = (cQp.mut q1 + cQp.mut q2)%cQp.
Proof. intros. reflexivity. Qed.

  Ltac solveCqpeq :=
    repeat match goal with
        H:Qp |- _ => destruct H; simpl in *
      end;
      unfold cQpc, cQp.scale; simpl in *;
      repeat rewrite <- mut_mut_add;
       f_equal;              
        solveQpeq;
        solveQeq.

Import linearity.
Hint Rewrite @firstn_all: syntactic.
Hint Rewrite Nat.add_0_r Z.add_0_r :syntactic.
Hint Rewrite @drop_all: syntactic.
Hint Rewrite nat_N_Z: syntactic.
Hint Rewrite @offset_ptr_sub_0 using (auto; apply has_size; exact _): syntactic.
Hint Rewrite @skipn_0: syntactic.
Ltac hideP fullyHiddenPostcond :=
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | HiddenPostCondition => hideFromWorkAs L fullyHiddenPostcond
                        end
                     ).
Ltac iExistsTac  foo:=match goal with
                        |- environments.envs_entails _ (Exists (_:?T), _) => iExists ((ltac:(foo)):T)
                      end.
Ltac aggregateRepPieces base :=
  repeat rewrite <- (_at_offsetR base);
  repeat (IPM.perm_left ltac:(fun L n =>
                                lazymatch L with
                                | base |-> _ => iRevert n
                                end
    ));
  repeat rewrite bi.wand_curry;
  repeat rewrite <- _at_sep;
  match goal with
    [ |-environments.envs_entails _ (base |-> ?R -* _)] =>
      iIntrosDestructs;
      iExists R
  end.

Ltac nat2ZNLdup :=
  match goal with
  | H : (?l <= ?r)%nat |- _ =>
      let tac :=
        let Hf := fresh H "_nat2Z" in 
        pose proof (@inj_le _ _ H) as Hf;
        repeat rewrite Nat2Z.inj_div  in Hf;
                                         repeat rewrite Nat2Z.inj_mul  in Hf in

                                             match l with
                                             | context[Nat.div]  => tac 
                                             | context[Nat.mul]  => tac
                                             | _ => match r with 
                                                    | context[Nat.div]  => tac 
                                                    | context[Nat.mul]  => tac
                                                    end
                                             end
  end.

Ltac revertAdr adr :=
  IPM.perm_left ltac:(fun L n=>
                        match L with
                        | adr |-> _ => iRevert n
                        end
                     ) .
Ltac revertAdrs l :=
  match l with
  | ?h::?tl => revertAdr h; revertAdrs constr:(tl)
  | [] => idtac
  end.
Ltac intantiateWand :=
  match goal with
    [ |-environments.envs_entails _ (?R -* _)] =>
      iIntrosDestructs;
      iExists R
  end.

#[local] Open Scope Z_scope.

(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.

Definition storedAtGhostLoc  `{Sigma:cpp_logic} {CU: genv} (q: Q) (g: gname) (n: nat) : mpred.
  Admitted.

Ltac simplPure :=
  simpl in *; autorewrite with syntactic (* equiv *) iff  in *; try rewrite left_id in *; simpl in *.

Lemma trans4 `{Equivalence} a b a' b': R a a' -> R b b' -> R a b -> R a' b'.
Proof. now intros -> ->. Qed.

Tactic Notation "aac_rewriteh" uconstr(L) "in" hyp(H) :=
  (eapply trans4 in H;[| try aac_rewrite L; try reflexivity | try aac_rewrite L; try reflexivity ]).

Ltac slautot rw := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); rw; try (erewrite take_S_r;[| eauto;fail]))
  then slautot rw  else idtac.

Ltac slauto := slautot idtac. (* try rewrite left_id; *)
Ltac slauto1 := (slautot ltac:(autorewrite with syntactic)); try iPureIntro.
Ltac slauto2 := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id)); try iPureIntro.

Lemma pureAsWand (mpred:bi) (P:Prop) (C:mpred) E: P -> environments.envs_entails E ([|P|] -* C) ->  environments.envs_entails E C.
Proof using.
  intros p.
  repeat rewrite to_entails.
  intros Hp.
  go.
  rewrite Hp.
  go.
Qed.
Lemma genWand  (mpred:bi) {T} (ival:T)  W (C:mpred) E :
  environments.envs_entails E ((Exists ival, W ival) -* C) ->  environments.envs_entails E (W ival-* C).
Proof using.
  repeat rewrite to_entails.
  intros Hp.
  go.
  rewrite Hp.
  go.
  iExists _. iStopProof. reflexivity.
Qed.

Ltac genOver ival :=
  repeat match goal with
    | H:context[ival] |- _ => apply (@pureAsWand _ _ _ _ H); clear H
    end;
  repeat IPM.perm_left ltac:(fun L n =>
                               match L with
                               | context[ival] => iRevert n
                               end
                            );
  repeat rewrite bi.wand_curry;
  pattern ival;
  lazymatch goal with
  | |- (fun x => environments.envs_entails _ (@?P x -* _)) _ =>
      apply (@genWand mpredI nat ival P)
  end; clear ival; simpl;
  lazymatch goal with
    |- environments.envs_entails _ (?P -* _) => hideFromWork P
  end;
  iIntros "?"%string.

Ltac wapplyObserve lemma:=
    try intros;
  idtac;
  [
    wapply (@observe_elim _ _ _ (lemma)) || wapply (@observe_elim _ _ _ (lemma _))
    || wapply (@observe_elim _ _ _ (lemma _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _ _))
    || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _ _ _)) || wapply (@observe_elim _ _ _ (lemma _ _ _ _ _ _ _ _ _ _ _))
    ||
    wapply (@observe_2_elim _ _ _ _ (lemma)) || wapply (@observe_2_elim _ _ _ _ (lemma _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _ _))
    || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _)) || wapply (@observe_2_elim _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _ _))
  ].
Section tacLemmas.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)
  
  Lemma observe_elim_rep (Q P : Rep) (p:ptr): Observe Q P → p |-> P ⊢ p|->(P ∗ Q).
  Proof using.
    intros Ho.
    apply _at_mono.
    wapplyObserve Ho.
    go.
  Qed.
  
  Lemma observe_2_elim_rep Q P1 P2 (p:ptr) {O : Observe2 Q P1 P2} : p|->P1 ⊢ p|-> P2 -∗ p|->P1 ∗ p|->P2 ∗ p|->Q.
  Proof.
    iIntros. iStopProof.
    repeat rewrite <- _at_sep.
    apply _at_mono.
    wapplyObserve O.
    go.
  Qed.
End tacLemmas.

Ltac wapplyObserveRep lemma:=
  try intros;
  idtac;
  [
    wapply (@observe_elim_rep _ _ _ _ _ _ (lemma)) || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _))
    || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _)) || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _))
    || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _)) || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _))
    || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _ _)) || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _ _))
    || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _)) || wapply (@observe_elim_rep _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _ _))
    
    || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma)) || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _))
    || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _)) || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _))
    || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _)) || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _))
    || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _ _)) || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _ _ _))
    || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _)) || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _ _))
    || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _)) || wapply (@observe_2_elim_rep _ _ _ _ _ _ _ (lemma _ _ _ _ _ _ _ _ _ _ _))
    
  ].
Opaque coPset_difference.

Section cp.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)
  
  Definition parrayR  {T:Type} ty (Rs : nat -> T -> Rep) (l: list T) : Rep :=
  .[ ty ! length l ] |-> validR ** [| is_Some (size_of _ ty) |] **
  (* ^ both of these are only relevant for empty arrays, otherwise, they are implied by the
     following conjunct *)
     [∗ list] i ↦ li ∈ l, .[ ty ! Z.of_nat i ] |-> (type_ptrR ty ** Rs i li).


  Definition offsetR_only_fwd := ([BWD->] _offsetR_only_provable).
  Hint Resolve offsetR_only_fwd: br_opacity. (* repeat at the end *)
  Lemma parrayR_cons {T:Type} ty (R : nat -> T -> Rep) (x:T) (xs: list T) :
    parrayR ty R (x :: xs) -|- type_ptrR ty ** (.[ ty ! 0 ] |-> (R 0 x)) ** .[ ty ! 1 ] |-> parrayR ty (fun n => R (S n)) xs.
  Proof using.
    unfold parrayR.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    repeat rewrite !_offsetR_sub_0; auto.
    repeat rewrite _offsetR_sep.
    repeat rewrite _offsetR_big_sepL.
    repeat rewrite _offsetR_succ_sub.
    repeat setoid_rewrite  _offsetR_succ_sub.
    simpl.
    repeat rewrite Nat2Z.inj_succ.
    repeat rewrite !_offsetR_sub_0; auto.
    setoid_rewrite Nat2Z.inj_succ.
    iSplit; work.
  Qed.

  Lemma arrDecompose {T} (p:ptr) ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   -|- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
     ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ ty ! k ] |-> R t).
  Proof using.
    rewrite arrayR_eq.
    unfold arrayR_def.
    rewrite arrR_eq.
    unfold arrR_def.
    repeat rewrite length_fmap.
    repeat rewrite big_opL_fmap.
    iSplit; go.
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
      iClear "#".
      iStopProof.
      f_equiv.
      go.
    }
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
       hideLhs.
       rewrite big_sepL_proper; try go.
       2:{ intros. iSplit. 2:{go.  evartacs.maximallyInstantiateLhsEvar. }  go. }
       simpl.
       unhideAllFromWork.
       go.
    }
  Qed.

  Lemma arrLearn (p:ptr) {T} ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   |-- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> arrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite arrDecompose.
    go.
  Qed.

  Lemma arrLearn2 (p:ptr) {T} ltr (R: T -> Rep) (ty:type):
    p |-> arrayR ty R ltr
   |-- valid_ptr p ** (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> arrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite arrDecompose.
    go.
    destruct ltr.
    - go. autorewrite with syntactic. go.
    -  simpl. autorewrite with syntactic. go.
  Qed.

  Lemma parrDecompose {T} (p:ptr) ltr (R: nat -> T -> Rep) (ty:type):
    p |-> parrayR ty R ltr
   -|- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
     ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) ∗
      ([∗ list] k↦t ∈ ltr, p .[ ty ! k ] |-> R k t).
  Proof using.
    unfold parrayR.
    repeat rewrite length_fmap.
    repeat rewrite big_opL_fmap.
    iSplit; go.
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
      iClear "#".
      iStopProof.
      f_equiv.
      go.
    }
    {
      setoid_rewrite _offsetR_sep.
      rewrite big_sepL_sep.
      go.
      repeat rewrite _at_big_sepL.
      setoid_rewrite _at_offsetR.
      go.
       hideLhs.
       rewrite big_sepL_proper; try go.
       2:{ intros. iSplit. 2:{go.  evartacs.maximallyInstantiateLhsEvar. }  go. }
       simpl.
       unhideAllFromWork.
       go.
    }
  Qed.

  Lemma parrLearn (p:ptr) {T} ltr (R: nat -> T -> Rep) (ty:type):
    p |-> parrayR ty R ltr
   |-- (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> parrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite parrDecompose.
    go.
  Qed.

  Lemma generalize_arrayR_loopinv_produce (i : nat) (p:ptr) {X : Type} (R : X → Rep) (ty : type) xs (Heq: i=(length xs)):
    p |-> arrayR ty R xs
    -|- p |-> arrayR ty R (take i xs).
  Proof using.
    intros. subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.
    
  Lemma generalize_parrayR_loopinv_produce (i : nat) (p:ptr) {X : Type} (R : nat -> X → Rep) (ty : type) xs (Heq: i=length xs):
    p |-> parrayR ty R xs
    -|- (p |-> parrayR ty R (take i xs)).
  Proof using.
    intros. subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.

  Lemma arrayR_nils{T} ty (R:T->_) : arrayR ty R [] = (.[ ty ! 0%nat ] |-> validR ∗ [| is_Some (size_of CU ty) |] ∗ emp)%I.
  Proof. rewrite arrayR_eq /arrayR_def arrR_eq /arrR_def. simpl. reflexivity. Qed.
  Lemma unit_snoc_cons (l: list unit) : (l++[()] = ()::l).
  Proof using.
    induction l; auto.
    simpl.
    destruct a.
    rewrite IHl. reflexivity.
  Qed.

  Lemma parrLearn2 (p:ptr) {T} ltr (R: nat -> T -> Rep) (ty:type):
    p |-> parrayR ty R ltr
   |-- valid_ptr p ** (valid_ptr (p .[ ty ! length ltr ])) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (type_ptr ty (p .[ ty ! k ])))) **
   p |-> parrayR ty R ltr.
  Proof using.
    iIntrosDestructs.
    rewrite parrDecompose.
    go.
    destruct ltr.
    - go. autorewrite with syntactic. go.
    -  simpl. autorewrite with syntactic. go.
  Qed.

   Lemma parrLearn2r {T} ltr (R: nat -> T -> Rep) (ty:type):
   parrayR ty R ltr
   |-- validR ** (.[ ty ! length ltr ] |-> validR) ** [| is_Some (size_of CU ty) |] **
   ( □ ([∗ list] k↦_ ∈ ltr, (.[ ty ! k ] |-> type_ptrR ty))) **
   parrayR ty R ltr.
   Proof using.
     apply Rep_entails_at.
     intros.
     rewrite -> parrLearn2 at 1.
     Opaque parrayR.
     go.
     setoid_rewrite _at_big_sepL.
     go.
     setoid_rewrite _at_offsetR.
     setoid_rewrite _at_type_ptrR.
     go.
   Qed.
   Transparent parrayR.
    
  Lemma parrayR_app {X} ty xs ys : forall (R:nat -> X->Rep),
    parrayR ty R (xs ++ ys) -|- parrayR ty R xs ** .[ ty ! length xs ] |-> parrayR ty (fun ii => R (length xs +ii)) ys.
  Proof.
    induction xs => /=.
    { intros.
      intros.
      iSplit.
      {
        go.
        rewrite -> parrLearn2r at 1.
        go.
        change (Z.of_nat 0) with 0%Z.
        repeat rewrite o_sub_0; auto.
        repeat rewrite _offsetR_id.
        go.
        unfold parrayR. go.
        change (Z.of_nat 0) with 0%Z.
        repeat rewrite o_sub_0; auto.
        repeat rewrite _offsetR_id.
        go.
      }

      {
        unfold parrayR.
        go.
        simpl.
        change (Z.of_nat 0) with 0%Z.
        repeat rewrite o_sub_0; auto.
        repeat rewrite _offsetR_id.
        go.
      }
    }
    { intros. repeat rewrite parrayR_cons.
      by rewrite IHxs !_offsetR_sep !_offsetR_succ_sub Nat2Z.inj_succ -!assoc.
    }
  Qed.

  Lemma parrayR_app1 {X} ty xs y : forall (R:nat -> X->Rep),
    parrayR ty R (xs ++ [y]) -|- parrayR ty R xs ** .[ ty ! length xs ] |-> (R (length xs) y ** type_ptrR ty).
  Proof.
    intros.
    apply Rep_equiv_at.
    intros.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    rewrite parrayR_app.
    iSplit; go; unfold parrayR; simpl;
      autorewrite with syntactic;
      repeat rewrite o_sub_0; auto; go.
    normalize_ptrs.
    go.
  Qed.
  
  Lemma parrayR_cell i {X} ty (R:nat -> X->Rep) xs x iZ :
    iZ = Z.of_nat i →	(** Ease [eapply] *)
    xs !! i = Some x →	(** We have an [i]th element *)
    parrayR ty R xs -|-
           parrayR ty R (take i xs) **
           _sub ty iZ |-> type_ptrR ty **
           _sub ty iZ |-> R i x **
           _sub ty (iZ + 1) |-> parrayR ty (fun ii => R (S i+ii)) (drop (S i) xs).
  Proof.
    intros Hi Hl.
    rewrite -{1}(take_drop_middle xs i _ Hl) parrayR_app parrayR_cons !_offsetR_sep.
    f_equiv.
    enough (length (take i xs) = i) as ->.
    { subst. repeat setoid_rewrite _offsetR_sub_sub.
      replace (i+0) with i by lia.
      replace (Z.of_nat i + 0)%Z with (Z.of_nat i) by lia.
      repeat setoid_rewrite Nat.add_succ_r.
      iSplit; go.
    }
    { apply length_take_le.
      apply lookup_lt_Some in Hl. lia. }
  Qed.

  Lemma parrayR_cell2 i {X} ty (R:nat -> X->Rep) xs:
    (Z.of_nat i < Z.of_nat (length xs))%Z ->
          exists x, 
            xs !! i = Some x /\	(** We have an [i]th element *)
    (parrayR ty R xs -|-
           parrayR ty R (take i xs) **
           _sub ty (Z.of_nat i) |-> type_ptrR ty **
           _sub ty (Z.of_nat i) |-> R i x **
           _sub ty ((Z.of_nat i) + 1) |-> parrayR ty (fun ii => R (S i+ii)) (drop (S i) xs)).
  Proof using.
    intros.
    assert (i<length xs) as Hex by lia.
    applyToSomeHyp @lookup_lt_is_Some_2.
    hnf in autogenhyp.
    forward_reason.
    subst.
    eexists; split; eauto.
    apply parrayR_cell; auto.
  Qed.

  Fixpoint isFunctionNamed2 (fname: ident) (n:name): bool :=
    match n with
    | Nglobal  (Nfunction _ i _) => bool_decide (i=fname)
    | Ninst nm _ => isFunctionNamed2 fname nm
    | Nscoped _ (Nfunction _ i _) => bool_decide (i=fname)
    | _ => false
    end.

  Fixpoint containsDep (n:name): bool :=
    match n with
    | Ndependent _ => true
    | Nglobal  (Nfunction _ i _) => false
    | Ninst nm _ => containsDep nm
    | Nscoped nm (Nfunction _ i _) => containsDep nm
    | _ => false
    end.
  
  Definition findBodyOfFnNamed2 module filter :=
    List.filter (fun p => let '(nm, body):=p in filter nm) (NM.elements (symbols module)).

  Definition lookupSymbolByFullName module (n: name) : option sym_info :=
    let el:= NM.find n (symbols module) in
    (option_map (fun x => {| info_name := n; info_type := fst (tu_find.INFO.okind_of_value x) |}) el).

  Definition firstEntryName (l :list (name * ObjValue)) :=
    (List.nth 0 (map fst l) (Nunsupported "impossible")).
  Lemma parrayR_sep {V} ty xs  : forall (A B : nat -> V -> Rep),
    parrayR ty (fun i v => A i v ** B i v) xs -|-
    parrayR ty (fun i v => A i v) xs **
    parrayR ty (fun i v=> B i v) xs.
  Proof.
    elim: xs => [|x xs IH] /=; intros.
    Transparent parrayR.
    - unfold parrayR. simpl. iSplit; go.
    - repeat rewrite parrayR_cons.  simpl.
      rewrite {}IH. repeat rewrite _offsetR_sep.
    all: iSplit; work.
  Qed.

  #[global] Instance parrayR_proper X ty:
    Proper ((pointwise_relation nat (pointwise_relation X (≡))) ==> (=) ==> (≡)) (parrayR ty).
  Proof.
    unfold parrayR.
    intros f g Hf xs y ?. subst. f_equiv.
    f_equiv.
    f_equiv.
    hnf.
    intros. hnf. intros.
    hnf in Hf.
    rewrite Hf.
    reflexivity.
  Qed.

  #[global] Instance parrayR_mono X ty:
    Proper (pointwise_relation nat (pointwise_relation X (⊢)) ==> (=) ==> (⊢)) (parrayR ty).
  Proof.
    unfold parrayR.
    intros f g Hf xs y ?. subst. f_equiv.
    f_equiv.
    f_equiv.
    hnf.
    intros. hnf. intros.
    hnf in Hf.
    rewrite Hf.
    reflexivity.
  Qed.

  #[global] Instance parrayR_flip_mono X ty:
    Proper (pointwise_relation nat (pointwise_relation X (flip (⊢))) ==> (=) ==> flip (⊢)) (parrayR ty).
  Proof. solve_proper. Qed.
  Lemma generalize_arrayR_loopinv (i : nat) (p:ptr) {X : Type} (R : X → Rep) (ty : type) xs (Heq: i=0):
    p |-> arrayR ty R xs
    -|- (p  .[ty ! i]) |-> arrayR ty R (drop i xs).
  Proof using.
    intros.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.
    
  Lemma generalize_parrayR_loopinv (i : nat) (p:ptr) {X : Type} (R : nat -> X → Rep) (ty : type) xs (Heq: i=0):
    p |-> parrayR ty R xs
    -|- (p  .[ty ! i]) |-> parrayR ty (fun ii => R (i+ii)) (drop i xs).
  Proof using.
    intros.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    subst.
    autorewrite with syntactic.
    reflexivity.
  Qed.

  
  Lemma drop_S2: ∀ {A : Type} (l : list A) (n : nat),
      (Z.of_nat n < lengthZ l)%Z→
        exists x,  l !! n = Some x /\ drop n l = x :: drop (S n) l.
  Proof using.
    intros ? ? ? Hl.
    unfold lengthN in Hl.
    assert (n< length l)%nat as Hln by lia.
    erewrite <- nth_error_Some in Hln.
    pose proof (fun x => drop_S l x n).
    rewrite <- lookup_nth_error in Hln.
    destruct (l !! n); try congruence.
    eexists; split; eauto.
  Qed.

  Lemma parrayR_nil {T} (R : nat -> T -> Rep) ty: parrayR ty R [] -|- validR ** [| is_Some (size_of _ ty) |].
  Proof using.
    unfold parrayR. simpl.
    apply: (observe_both (is_Some (size_of _ ty))) => Hsz.
    change (Z.of_nat 0) with 0%Z.
    autorewrite with syntactic.
    rewrite _offsetR_sub_0; try assumption.
    iSplit; work.
  Qed.

  Lemma primr_split (p:ptr) ty (q:Qp) v :
    p|-> primR ty (cQp.mut q) v -|- (p |-> primR ty (cQp.mut q/2) v) ** p |-> primR ty (cQp.mut q/2) v.
  Proof using.
    rewrite -> cfractional_split_half with (R := fun q => primR ty q v).
    2:{ exact _. }
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
    simpl;
      rewrite cQp.scale_mut;
      f_equiv;
    destruct q; simpl in *;
      solveQpeq;
      solveQeq.
  Qed.
  Definition primR_split_C := [CANCEL] primr_split.

    Lemma arrayR_cell2 i {X} ty (R:X->Rep) xs:
    (Z.of_nat i < Z.of_nat (length xs))%Z ->
          exists x, 
            xs !! i = Some x /\	(** We have an [i]th element *)
    (arrayR ty R xs -|-
           arrayR ty R (take i xs) **
           _sub ty (Z.of_nat i) |-> type_ptrR ty **
           _sub ty (Z.of_nat i) |-> R  x **
           _sub ty ((Z.of_nat i) + 1) |-> arrayR ty R (drop (1+i) xs)).
  Proof using.
    intros.
    assert (i<length xs)%nat as Hex by lia.
    applyToSomeHyp @lookup_lt_is_Some_2.
    hnf in autogenhyp.
    forward_reason.
    subst.
    eexists; split; eauto.
    apply arrayR_cell; auto.
  Qed.
      
  Lemma fold_id {A:Type} (f: A->A->A) (c: Commutative (=) f) (asoc: Associative (=) f)
    (start id: A) (lid: LeftId (=) id f) (l: list A):
    fold_left f l start = f (fold_left f l id) start.
  Proof using.
    hnf in lid. revert start.
    induction l; auto;[].
    simpl. rewrite lid.
    intros.
    simpl.
    rewrite IHl.
    symmetry.
    rewrite IHl.
    aac_reflexivity.
  Qed.
  
  Lemma fold_split {A:Type} (f: A->A->A) (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id) (fold_left f (skipn lSplitSize l) id).
  Proof using.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id.
    aac_reflexivity.
  Qed.


  Definition liftf {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b))
    (a: dsig P) (b: dsig P) : dsig P :=
    (dexist (f (`a) (`b)) (fpres _ _ (proj2_dsig a) (proj2_dsig b))).

  #[global] Instance liftfComm {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b))
    (c: Commutative (=) f) : Commutative (=) (liftf f P fpres).
  Proof using.
    hnf.
    intros x y. destruct x, y. simpl in *.
    unfold liftf.
    simpl.
    Search dsig.
    apply dsig_eq.
    simpl.
    auto.
  Qed.
  
  #[global] Instance liftfAssoc {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b))
    (c: Associative (=) f) : Associative (=) (liftf f P fpres).
  Proof using.
    hnf.
    intros x y z. destruct x, y, z. simpl in *.
    unfold liftf.
    simpl.
    apply dsig_eq.
    simpl.
    auto.
  Qed.

    Lemma fold_left_proj1dsig {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (fpres: forall a b, P a -> P b -> P (f a b)) l start:
      proj1_sig (fold_left (liftf f P fpres) l start) = fold_left f (map proj1_sig l) (`start).
    Proof using.
      revert start.
      induction l; auto.
      intros.  simpl.
      rewrite IHl.
      simpl.
      reflexivity.
    Qed.
  
  Lemma fold_split_condid1 {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: forall a, P a -> f id a = a) (ld: list (dsig P)) (lSplitSize: nat) (pid: P id)
    (fpres: forall a b, P a -> P b -> P (f a b)):
    let l:= map proj1_sig ld in
    fold_left f l id=
      f (fold_left f (firstn lSplitSize l) id) (fold_left f (skipn lSplitSize l) id).
  Proof using.
    pose proof (fun lid => @fold_split _  (liftf f P fpres) _ _ (dexist id pid) lid ld lSplitSize) as Hh.
    lapply Hh.
    2:{ hnf. intros x. destruct x. unfold liftf. simpl.
        apply dsig_eq. simpl. apply lid.
        apply bool_decide_unpack in i. assumption. }
    intros Hx.
    clear Hh.
    simpl.
    apply (f_equal proj1_sig) in Hx.
    simpl in Hx.

    repeat rewrite fold_left_proj1dsig in Hx.
    simpl.
    unfold dexist in Hx. simpl in Hx.
    repeat rewrite map_take in Hx.
    repeat rewrite map_drop in Hx.
    rewrite Hx.
    f_equal.
    f_equal.
    rewrite skipn_map.
    reflexivity.
  Qed.
    Fixpoint pairProofDsig {A} (l: list A) (P:A->Prop) {hdec: forall a, Decision (P a)} (pl: forall a, In a l -> P a) : list (dsig P).
      destruct l; simpl in *.
      - exact [].
      -  pose proof (pl a ltac:(left;apply eq_refl)) as pll.
         apply cons.
         + exists a. apply bool_decide_pack. assumption.
         +  apply pairProofDsig with (l:=l). intros. apply pl. right. assumption.
    Defined.
    Lemma pairProofDsigMapFst {A} (l: list A) (P:A->Prop) {hdec: forall a, Decision (P a)} (pl: forall a, In a l -> P a):
      map proj1_sig (pairProofDsig l P pl) = l.
    Proof using.
      induction l; auto.
      -  simpl. auto. f_equal.
         rewrite IHl.
         reflexivity.
    Qed.
  
  Lemma fold_split_condid {A:Type} (f: A->A->A) (P:A->Prop) {hdec: forall a, Decision (P a)} (c: Commutative (=) f) (asoc: Associative (=) f)
    (id: A) (lid: forall a, P a -> f id a = a) (l: list A) (pl: forall a, In a l -> P a) (lSplitSize: nat) (pid: P id)
    (fpres: forall a b, P a -> P b -> P (f a b)):
    fold_left f l id=
      f (fold_left f (firstn lSplitSize l) id) (fold_left f (skipn lSplitSize l) id).
  Proof using.
    pose proof (fold_split_condid1 f P c asoc id lid (pairProofDsig l P pl)) as Hx.
    simpl in Hx.
    repeat rewrite pairProofDsigMapFst in Hx.
    apply Hx; auto.
  Qed.

  Open Scope Z_scope.
  Lemma fold_split_gcd  (l: list Z) (pl: forall a, In a l -> 0 <= a) (lSplitSize: nat):
    fold_left Z.gcd l 0=
      Z.gcd (fold_left Z.gcd (firstn lSplitSize l) 0) (fold_left Z.gcd (skipn lSplitSize l) 0).
  Proof using.
    apply fold_split_condid with (P:= fun z => 0<=z); auto; try exact _; try lia;
      intros; try apply Z.gcd_nonneg.
    rewrite Z.gcd_0_l.
    rewrite Z.abs_eq; auto.
  Qed.
  Lemma obsUintArrayR (p:ptr) q (l: list Z): Observe [| forall (a : Z), In a l → 0 ≤ a|] (p|->arrayR "unsigned int" (fun i => primR "unsigned int" q (Vint i)) l) .
  Proof using.
    apply observe_intro; [exact _ |].
    revert p.
    induction l; auto.
    simpl. intros. rewrite arrayR_cons.
    hideRhs.
    go.
    rewrite -> IHl at 1.
    go.
    unhideAllFromWork.
    go.
    iPureIntro.
    intros? Hin.
    destruct Hin; auto.
    subst.
    type.has_type_prop.
  Qed.
  Lemma spurious {T:Type} {ing: Inhabited T} (P: mpred) :
  P |-- Exists a:T, P.
  Proof using.
    work.
    iExists (@inhabitant T _).
    work.
  Qed.
  
  Lemma arrayR_combinep {T} ty (R: T->Rep) i xs (p:ptr):
    p |-> arrayR ty R (take i xs) **
      p .[ ty ! i ] |-> arrayR ty R (drop i xs)
           |-- p |-> arrayR ty R xs.
  Proof using.
    go.
    hideLhs.
    rewrite <- arrayR_combine.
    unhideAllFromWork.
    go.
  Qed.
  Definition arrayR_combineC := [CANCEL] @arrayR_combinep. (* this hint will apply once we state everything in Z terms *)
    
  Lemma primR2_anyR : ∀ t (q:Qp) (v:val) (p:ptr),
      p|-> primR t (q/2) v ** p|->primR t (q/2) v  |-- p|->anyR t q.
  Proof. intros. setoid_rewrite <- primr_split.  go.  Admitted.
  Definition primR2_anyRC := [CANCEL] primR2_anyR.
  
  #[global] Instance learnArrUnsafe e t: LearnEq2 (@arrayR _ _ _ e _ t) := ltac:(solve_learnable).

  Definition atomic_core_field_offset : offset. Proof. Admitted.
  Definition atomicR (ty:type) (q : cQp.t) (v : val) : Rep :=
    structR (Ninst "std::atomic" [Atype ty]) q
    ** o_base CU (Ninst "std::atomic" [Atype ty]) (Ninst "std::__atomic_base" [Atype ty]) |-> structR  (Ninst "std::__atomic_base" [Atype ty]) q
    ** atomic_core_field_offset |-> primR ty q v.

(** Properties of [atomicR] *)
Section atomicR.
  Definition ns := (nroot .@@ "::SpinLock").

  #[global] Instance atomicR_frac T : CFracSplittable_1 (atomicR T).
  Proof.  solve_cfrac. Qed.

  #[global] Instance atomic_type_ptrR_observe ty v q
    : Observe (type_ptrR (Tnamed (Ninst "std::atomic" [Atype ty]))) (atomicR ty v q) := _.

  #[global] Instance atomic_type_ptrR_base_observe ty v q (p:ptr)
    : Observe (type_ptr (Tnamed (Ninst "std::__atomic_base" [Atype ty])) (p,, o_base CU (Ninst "std::atomic" [Atype ty]) (Ninst "std::__atomic_base" [Atype ty]))) (p |-> atomicR ty v q).
  Proof.
    apply observe_intro;[exact _|].
    iIntrosDestructs.
    unfold atomicR.
    hideRhs.
    go.
    unhideAllFromWork.
    go.
  Qed.
  
  #[global] Instance atomic_agree ty v1 v2 q1 q2
    : Observe2 [| v1 = v2 |] (atomicR ty q1 v1) (atomicR ty q2 v2) := _.

  #[global] Instance atomic_agree_inj `{Vinj : A -> val} `{!Inj eq eq Vinj} ty v1 v2 q1 q2
    : Observe2 [| v1 = v2 |] (atomicR ty q1 (Vinj v1)) (atomicR ty q2 (Vinj v2)).
  Proof. exact: (observe2_inj Vinj). Qed.

  Definition learn_atomic_val (p : ptr) ty v1 v2 q1 q2
    : Learnable (p |-> atomicR ty q1 v1) (p |-> atomicR ty q2 v2) [v2=v1].
  Proof. solve_learnable. Qed.

  Definition learn_atomic_val_UNSAFE (p : ptr) ty v1 v2 q1 q2
    : Learnable (p |-> atomicR ty q1 v1) (p |-> atomicR ty q2 v2) [v2=v1; q1=q2].
  Proof. solve_learnable. Qed.
  (** [atomicR ty q v] implies that value [v] has type [ty]. *)
  Lemma atomicR_has_type_prop ty v q :
    Observe [| has_type_prop v ty |] (atomicR ty q v).
  Proof. refine _. Qed.

  Opaque atomicR.
  Lemma atomicR_combine (p:ptr) (q1 q2: Qp) (v1 v2 : val) ty:
    p |-> atomicR ty q1 v1 ** p |-> atomicR ty q2 v2
      |-- p |-> atomicR ty (q1+q2) v1 ** [| v1 = v2 |].
  Proof using.
    go.
    wapplyObserveRep atomic_agree. eagerUnifyU. go.
    rewrite -> @cfractional.cfractional with (P := fun q => atomicR ty q v1);[| exact _].
    go.
  Qed.
  Lemma atomicR_combine_half (p:ptr) (q: Qp) (v1 v2 : val) ty:
    p |-> atomicR ty (q/2) v1 ** p |-> atomicR ty (q/2) v2
      |-- p |-> atomicR ty q v1 ** [| v1 = v2 |].
  Proof using.
    rewrite atomicR_combine.
    go.
    iClear "#".
    iStopProof.
    apply _at_mono.
    f_equiv.
    solveCqpeq.
  Qed.
  Definition atomicR_combineF := [FWD] atomicR_combine.
  
End atomicR.

  Definition fwd_later_exist := [FWD] (@bi.later_exist).
  Definition fwd_later_sep := [FWD] (@bi.later_sep).
  Definition bwd_later_exist := [BWD_MW->] (@bi.later_exist).
  Definition bwd_later_sep := [BWD_MW->] (@bi.later_sep).
  Definition fwd_at_later := [FWD<-] (@_at_later).

  Lemma splitcinvq (P:mpred) ns (invId: gname) (q:Qp):
    cinvq ns invId q P |-- cinvq ns invId (q/2) P ** cinvq ns invId (q/2) P.
  Proof using.
    rewrite <- (@fractional _ _ (cinvq_frac _)).
    f_equiv.
    solveCqpeq.
  Qed.
  Definition cinvqC := [CANCEL] splitcinvq.
  
    Opaque coPset_difference.

    Lemma peek_cinvq a b c P (C:mpred) learn:
      ▷ P |-- bupd (▷ P ** learn) 
      -> (learn -* cinvq a b c P -*  |={⊤}=> C) |-- cinvq a b c P -*  |={⊤}=> C.
    Proof using.
      intros hl.
      go.
      openCinvq.
      rewrite hl.
      ghost.
      go.
      wapply invariants.close_cinvQR4.
      eagerUnifyU.
      unhideAllFromWork.
      go.
      iModIntro.
      iFrame.
    Qed.

    Lemma admitReferenceTo ty ptr : emp |-- reference_to ty ptr.
    Proof. Admitted.

  Lemma atomicr_split (p:ptr) ty (q:Qp) v :
    p|-> atomicR ty (cQp.mut q) v -|- (p |-> atomicR ty (cQp.mut q/2) v) ** p |-> atomicR ty (cQp.mut q/2) v.
  Proof using.
    rewrite -> cfractional_split_half with (R := fun q => atomicR ty q v);[| exact _].
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
      solveCqpeq.
  Qed.
  Definition atomicrC := [CANCEL] atomicr_split.
  Definition lcinvqg_unsafe a1 g1 q1 P1 a2 g2 q2 P2:
    Learnable (cinvq a1 g1 q1 P1) (cinvq a2 g2 q2 P2) [g1=g2] := ltac:(solve_learnable).

  Section Hints.
    Context {T:Type} {ff : fracG T _}. (* {fff: fracG T   _Σ} *)
  (* Move and generalize colocate with [fgptsto_update]*)
  Lemma half_combine  (m1 m2:T) g q:
((g |--> logicalR (q / 2) m1):mpred) ∗ g |--> logicalR (q / 2) m2 ⊢ (g |--> logicalR q m1) ∗ [| m2 = m1 |].    
  Proof.
  Admitted.
  Lemma half_split  (m:T) g q:
    g |--> logicalR q m |-- ((g |--> logicalR (q / 2) m):mpred) ** ((g |--> logicalR (q / 2) m)).
  Proof.
  Admitted.
  Lemma logicalR_update (l : gname) (v' v : T) :
    l |--> logicalR 1 v |-- |==>
    l |--> logicalR 1 v'.
  Proof. apply @own_update; try exact _. apply cmra_update_exclusive. done. Qed.
  
  #[global] Instance learn_logicalR (l : gname) (v1 v2 : T) q q1 :
    Learnable (l |--> logicalR q1 v1)  (l |--> logicalR q v2) [v1=v2] := ltac:(solve_learnable).

  Definition  learn_logicalR_unsafe (l : gname) (v1 v2 : T) q1 q2 :
    Learnable (l |--> logicalR q1 v1)  (l |--> logicalR q2 v2) [v1=v2; q1=q2] := ltac:(solve_learnable).
  

  Definition ownhalf_combineF := [FWD->] half_combine.
  Definition ownhalf_splitC := [CANCEL] half_split.
  End Hints.

  Section stsg.
  Context {sts: stsT}.
  Import sts.
  Implicit Types s : state sts.
  Implicit Types S : states sts.
  Implicit Types T Tf: tokens sts.
  Context `{sss: !stsG sts}.

  (* auto typically stays in the invariant. frag can be used to constrain it : s ∈ S *)
  Lemma auth_frag_together (g: gname) s S T Tf:
  (g |--> sts_auth s T) ** (g |--> sts_frag S Tf)
   -|- (g |--> sts_auth s (Tf ∪ T)) ** [| T ## Tf /\ s ∈ S /\ closed S Tf|].
  Proof using.
    iSplit; go.
    {
      wapplyObserve (@own_2_valid _ _ _ _ _ _ (stsR sts)).
      eagerUnifyC. go.
      iStopProof.
      rewrite comm.
      rewrite <- own_op.
      hnf in H.
      forward_reason.
      hnf in Hrr.
      inverts Hrr.
      hnf in Hl. 
      forward_reason.
      rewrite sts_op_auth_fragg; auto.
    }
    {
      rewrite <- own_op.
      rewrite sts_op_auth_fragg; auto.
    }
  Qed.
  Check atomicR_combine.

  (* typical step when closing invariant: <- *)
  Lemma auth_frag_together2 (g: gname) s S Tf:
  (g |--> sts_auth s ∅) ** (g |--> sts_frag S Tf)
   -|- (g |--> sts_auth s Tf) ** [| s ∈ S /\ closed S Tf|].
  Proof using.
    rewrite auth_frag_together.
    rewrite right_id.
    iSplit; go.
    iPureIntro.
    split; auto.
    set_solver.
  Qed.

  
  Example auth_frag_together3 (g: gname) s S:
  (g |--> sts_auth s ∅) ** (g |--> sts_frag S ∅)
   -|- (g |--> sts_auth s ∅) ** [| s ∈ S /\ closed S ∅|].
  Proof using.
    rewrite auth_frag_together.
    rewrite right_id.
    iSplit; go.
    iPureIntro.
    split; auto.
    set_solver.
  Qed.
  
  Lemma auth_frag_together_dupl (g: gname) s S Tf:
  (g |--> sts_auth s Tf) ** (g |--> sts_frag S ∅)
   -|- (g |--> sts_auth s Tf) ** [| s ∈ S /\ closed S ∅|].
  Proof using.
    rewrite auth_frag_together.
    rewrite left_id.
    iSplit; go.
    iPureIntro.
    split; auto.
    set_solver.
  Qed.
  Search equiv bi_entails.

  Lemma auth_frag_together_dupl2 (g: gname) s S Tf:
    s ∈ S -> closed S ∅ ->
  (g |--> sts_auth s Tf) |-- (g |--> sts_auth s Tf) ** (g |--> sts_frag S ∅).
  Proof using.
    intros. iIntrosDestructs.
    wapplyRev  auth_frag_together_dupl.
    eagerUnifyU.
    go.
  Qed.
  
  (* sts_frag S ∅ is like knowledge: can be freely duplicated *)
    
  Lemma frag_frag_combine (g: gname) S1 S2 T1 T2:
  (g |--> sts_frag S1 T1) ** (g |--> sts_frag S2 T2)
    -|- (g |--> sts_frag (S1 ∩ S2) (T1 ∪ T2))
          ** [| T1 ## T2  /\ closed S1 T1 /\ closed S2 T2 |].
  Proof using.
    iSplit; go.
    {
      wapplyObserve (@own_2_valid _ _ _ _ _ _ (stsR sts)).
      eagerUnifyC.
      go.
      hnf in H.
      forward_reason.
      hnf in Hrr.
      inverts Hrr.
      hnf in Hl, Hrl.
      forward_reason.
      rewrite sts_op_frag; try auto.
      rewrite own_op. go.
      auto.
    }
    {
      rewrite sts_op_frag; try auto.
      rewrite <- own_op. go.
    }
  Qed.

      
  Example frag_frag_combine2 (g: gname) S:
  (g |--> sts_frag S ∅) ** (g |--> sts_frag S ∅)
    -|- (g |--> sts_frag S ∅) ** [| closed S ∅  |].
  Proof using.
    rewrite frag_frag_combine.
    rewrite left_id.
    autorewrite with syntactic.
    assert (S ∩ S ≡ S) as Heq by set_solver.
    rewrite Heq.
    iSplit;go.
    iPureIntro.
    split_and !; auto.
    set_solver +.
  Qed.
  
  Lemma observePure g (a: (stsR sts)) : Observe [| ✓ a |] (own g a).
  Proof.  apply observe_intro. exact _. go. Qed.
  
  Lemma stable_frag (g: gname) (S: states sts) (T: tokens sts):
    (g |--> sts_frag S T)
|-- (g |--> sts_frag S T) ** [|valid (sts_frag S T) |].
  Proof using. go. Qed.
  
  Example frag_dupl (g: gname) S:
  (g |--> sts_frag S ∅) |-- (g |--> sts_frag S ∅) ** (g |--> sts_frag S ∅).
  Proof using.
    rewrite -> stable_frag at 1.
    rewrite frag_frag_combine2.
    go.
    hnf in H.
    forward_reason.
    work.
  Qed.
  (*
  Lemma update_lloc (g:gname) (s sf: State) (toks: tokens spsc) :
    rtc (sts.step toks) s sf ->
      g |--> sts_auth s  toks |-- |==>
      g |--> sts_auth sf toks.
  Proof using.
    intros.
    forward_reason.
    apply own_update.
    apply sts_update_auth.
    assumption.
  Qed.
*)
  Lemma update_lloc (g:gname) (s sf: sts.state sts) (toks: tokens sts) :
    rtc (sts.step toks) s sf ->
      g |--> sts_auth s  toks |-- |==>
      g |--> sts_auth sf toks.
  Proof using.
    intros.
    forward_reason.
    apply own_update.
    apply sts_update_auth.
    assumption.
  Qed.

  
#[global] Instance ll g s1 s2 t1 t2: Learnable (g |--> sts_auth s1 t1) (g |--> sts_auth s2 t2) [s1=s2]
                                                   := ltac:(solve_learnable).
Lemma hideWandL (L C: mpred) E:
  (forall  (Lh:mpred), Hide.Hidden (Lh=L) ->  environments.envs_entails E (Lh -* C)) -> environments.envs_entails E (L -* C).
  intros Hl.
  specialize (Hl L).
  apply Hl.
  constructor.
  reflexivity.
Qed.

Lemma hideDuplWandL (L C: mpred) E:
  (L|--L**L) ->
  (forall  (Lh:mpred), Hide.Hidden (Lh=L) ->  environments.envs_entails E (Lh ** L -* C)) -> environments.envs_entails E (L -* C).
  intros Hd Hl.
  specialize (Hl L).
  rewrite Hd.
  apply Hl.
  constructor.
  reflexivity.
Qed.

Lemma forget_empty_frag (g: gname) S:
  (g |--> sts_frag S ∅) |-- (emp:mpred).
Proof using Sigma. apply lose_resources. Qed.
  
  End stsg.
  
End cp.

Ltac hideEmptyTokenFrag :=
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | _ |--> sts_frag ?S ∅ => hideFromWork L
                        end
                     ).
Ltac closedN := closed.norm closed.numeric_types .

Hint Resolve prefix_app_r: list.

Ltac bwdRev L :=
  wapplyRev L; last (iSplitFrameL; [| iIntrosDestructs; eagerUnifyC ; maximallyInstantiateLhsEvar_nonpers]).

Ltac renValAtLoc' loc name:=
  IPM.perm_left ltac:( fun L _ =>
    match L with
    | loc |--> logicalR _ ?v =>
        rename v into name
    | loc |--> stsg.sts_auth ?v _ =>
        rename v into name
    end).
Tactic Notation "renValAtLoc" open_constr(loc) "into" ident(name) :=
  renValAtLoc' loc name.
(* eliminate a Step.committer in context *)
Ltac useCommitter :=
  work;
  (rewrite -wp_shift || rewrite <- wp_stmt_shift);
  unfold Step.committer;
  rewrite atomic.aupd_aacc;
  simpl;
  unfold atomic.atomic_acc;
  ego;
  simpl.
Ltac useAC :=
  work;
  (rewrite -wp_shift || rewrite <- wp_stmt_shift);
  unfold Step.committer;
  rewrite atomic_commit_elim;
  work; (* unnecesary? *)
  unfold commit_acc.

Opaque parrayR.
(*  Hint Resolve fwd_later_exist fwd_later_sep bwd_later_exist
    bwd_later_sep : br_opacity. *)
Lemma cancelLstar {PROP:bi} {T} l (va vb : T -> PROP):
  (forall id, id ∈ l -> va id |-- vb id) ->
  ([∗ list] id ∈ l, va id) |-- ([∗ list] id ∈ l,vb id).
Proof using.
  intros He.
  apply big_sepL_mono.
  intros.
  apply He.
  eapply elem_of_list_lookup_2; eauto.
Qed.
Hint Opaque parrayR: br_opacity.
Hint Rewrite @arrayR_nils: syntactic.

Lemma takesr2 {X} l n (x:X) : length l = n → take (S n) (l++[x]) = take n l ++ [x].
Proof using. Admitted. (* easy *)

Hint Rewrite @length_take_le using lia: syntactic.

Lemma cancel_at `{xx: cpp_logic} (p:ptr) (R1 R2 : Rep) :
  (R1 |-- R2) -> (p |-> R1 |-- p |-> R2).
Proof using.
  apply _at_mono.
Qed.

Hint Resolve primR_split_C : br_opacity.




Require Import bluerock.prelude.propset.


Ltac erefl :=
  unhideAllFromWork;
  match goal with
    H := _ |- _ => subst H
  end;
  iClear "#";
  iStopProof; reflexivity.

Ltac unhideAllFromWork :=  tactics.unhideAllFromWork;
                           try match goal with
                               H := _ |- _ => subst H
                             end.

Ltac instWithPEvar name :=
  match goal with
  | |- environments.envs_entails _ (@bi_exist _ ?T _) =>
      evar (name:T);
      iExists name;
      let hname := fresh name "P" in
      hideFromWorkAs name hname
  end.

Lemma cqpp2 q: (cQp.scale (1 / 2) (cQp.mut q)) = (cQp.mut (q / 2)).
Proof using.    
      rewrite cQp.scale_mut;
      f_equiv;
      destruct q; simpl in *.
    f_equal.
      solveQpeq;
        solveQeq.
Qed.

Ltac aac_norm :=
  aac_normalise;
  repeat match goal with
    | H: _ |- _ => aac_normalise in H
    end.
    Hint Rewrite Nat2Z.inj_div : syntactic.
    Hint Rewrite Nat2Z.inj_sub using lia: syntactic.
    Hint Rewrite Z.quot_div_nonneg using lia : syntactic.

Ltac arith := (try aac_norm); Arith.arith_solve.
Ltac ren addr v :=
  IPM.perm_left
    ltac:(fun L n =>
            match L with
              addr |-> primR _ _ (Vint ?x) => rename x into v
            end
         ).
Ltac lose_resources := try iStopProof; apply lose_resources.



(* open all cinvq invariants then open rest. used in callAtomicCommitCinv*)
Ltac openCinvqsRest :=
  repeat openCinvq;
  work using fwd_later_exist, fwd_later_sep;
  repeat removeLater;
  iApply fupd_mask_intro;[set_solver |]; (* openRest *)
  iIntrosDestructs.

(**
   the RHS of your goal should look like a permutation of
   [[
   AC pre post ?Q ** (forall ..., ?Q ... -* ...)
   ]]
  it first calls [callAtomicCommit] to instantiate the public post Q.
  then it opens all cinvq invariants
  then it opens everything else (change the goal from [|={⊤ \ ..\ ... ,∅}=> U)] to  [|={∅}=> U)])
  and then "does iModIntro" so that you can start proving U which is typically of the form [pre ** ...]
 *)
Ltac callAtomicCommitCinv :=
  repeat (iExists _);
  callAtomicCommit;
  openCinvqsRest.

(* applies to goals that look like [|-- AC pre post Q] or [|-- AU pre post Q]  in IPM: only 1 conjuct in conclusion and not 2, where [callAtomicCommitCinv] works. it sets up the proof of AC/AU by doing the usual initialization
 and opening all invariants and rest so that you can immediately begin proving [pre] *)
Ltac proveAuAc :=
  (iAcIntro || iAuIntro);
  (unfold commit_acc || unfold atomic_acc);
  openCinvqsRest.

Lemma cinvq_alloc_no_shared_pages `{Σ : cpp_logic} (E : coPset) (N : namespace) (P : mpred) :
  ▷ P |-- |={E}=> ∃ γ : gname, cinvq N γ 1 P.
  Proof.
    intros.
    apply cinvq_alloc.
  Admitted. (* when there are no shared pages between processes, all C++ memory locations (ptr) are objective, else one has to look at the underlying physical address on the host machine *)
  
Notation uint := "unsigned int"%cpp_type.

(* this is currently needed at some method calls. it admits some reference_to obligations which can be proven with more bookkeeping. but the plan is anyway to tweak the method call derived rules to make it not produce these obligations *)
Ltac solveRefereceTo :=
  IPM.perm_right ltac:(fun R _ =>
                             match R with
                             | reference_to ?ty ?p =>
                                 wapply (admitReferenceTo ty p)
                             end
                      ).

Lemma fold_id2 {A:Type} (f: A->A->A) (asoc: Associative (=) f)
  (start id: A) (lid: LeftId (=) id f) (rid: RightId (=) id f) (l: list A):
  fold_left f l start = f start (fold_left f l id).
Proof using.
  hnf in lid.
  hnf in rid.
  revert start.
  induction l; auto.
  simpl.
  simpl. rewrite lid.
  intros.
  simpl.
  rewrite IHl.
  symmetry.
  rewrite IHl.
  aac_reflexivity.
Qed.
#[export] Hint Resolve ownhalf_combineF : br_opacity.
#[export] Hint Resolve ownhalf_splitC : br_opacity.
#[global] Hint Rewrite <- @spurious using exact _: slbwd.
#[global] Hint Resolve arrayR_combineC : br_opacity.

#[global] Hint Resolve primR2_anyRC: br_opacity.

(* uncomment if it doesnt break proofs 
#[global] Hint Resolve offsetR_only_fwd: br_opacity.
*)

(*
uncomment if there is no significant performance regression:

Import ZifyClasses.
      
Lemma zifyModNat: ∀ x y : nat, True →  y ≠ 0%nat → (x `mod` y < y)%nat.
Proof using.
  intros.
  apply Nat.mod_upper_bound.
  assumption.
Qed.
        
#[global]
Instance SatMod : Saturate Nat.modulo :=
  {|
    PArg1 := fun x => True;
    PArg2 := fun y => y ≠ 0%nat;
    PRes  := fun _ y r => (r <y)%nat;
    SatOk := zifyModNat
  |}.
*)



(*
In the current Coq context, I have `block_state_cpp.module:translation_unit` which is a translation of the AST of block_state.cpp (and its includes, recursively) to Coq.
Write a gallina function `lookup_function` that takes a `translation_unit` and an argumement `nm: name` and returns an `option _` which is a definition of the function/method whose fully qualified name is `nm`. Chose an appropriate type for the placeholder `_`.
Note that the AST treats classes as structs as well.

+++ QUERIES
Print translation_unit.
Print name.
*)
Definition lookup_function
           (tu : translation_unit) (nm : name)
  : option (sum Func Method) :=
  match symbols tu !! nm with
  | Some (Ofunction f) => Some (inl f)
  | Some (Omethod m)   => Some (inr m)
  | _                  => None
  end.




(* lookup a function/method declaration and its methods by fully‐qualified name *)
Definition symbol_table_to_list
  (st: bluerock.lang.cpp.syntax.translation_unit.symbol_table)
  : list (bluerock.lang.cpp.syntax.core.obj_name
          * bluerock.lang.cpp.syntax.translation_unit.ObjValue) :=
  (* NM.elements is already available and produces a list of (key * elt) *)
  bluerock.lang.cpp.syntax.namemap.NM.elements st.

#[only(lens)] derive Method'.

Definition AvailableButErased: option (OrDefault Stmt).
  exact None.
Qed.

#[only(lens)] derive Method'.

Import LensNotations.
Open Scope lens_scope.
Definition erase_body (m:Method) : Method :=
  match m_body m with
  | Some (UserDefined _) =>  m &: _m_body .= AvailableButErased
  | _ => m
  end.

(* pick out a method of class [nm] from one symbol‐table entry *)
Definition select_method_of_class
           (nm: bluerock.lang.cpp.syntax.core.name)
           (entry: bluerock.lang.cpp.syntax.core.obj_name
                   * bluerock.lang.cpp.syntax.translation_unit.ObjValue)
  : option (bluerock.lang.cpp.syntax.core.obj_name
            * bluerock.lang.cpp.syntax.decl.Method) :=
  let '(n,o) := entry in
  match o with
  | bluerock.lang.cpp.syntax.translation_unit.Omethod m =>
      if bool_decide (bluerock.lang.cpp.syntax.decl.m_class m = nm)
      then Corelib.Init.Datatypes.Some (n, erase_body m)
      else Corelib.Init.Datatypes.None
  | _ => Corelib.Init.Datatypes.None
  end.


(* lookup the Struct declaration and its methods by fully‐qualified name *)
Definition lookup_struct
           (tu: bluerock.lang.cpp.syntax.translation_unit.translation_unit)
           (nm: bluerock.lang.cpp.syntax.core.name)
  : option ( bluerock.lang.cpp.syntax.decl.Struct
             * list ( bluerock.lang.cpp.syntax.core.obj_name
                      * bluerock.lang.cpp.syntax.decl.Method ) ) :=
  match bluerock.lang.cpp.syntax.translation_unit.types tu !! nm with
  | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st) =>
      let syms := bluerock.lang.cpp.syntax.translation_unit.symbols tu in
      let mds :=
        List.fold_right
          (fun entry acc =>
             match select_method_of_class nm entry with
             | Corelib.Init.Datatypes.Some md => md :: acc
             | Corelib.Init.Datatypes.None => acc
             end)
          []
          (symbol_table_to_list syms) in
      Corelib.Init.Datatypes.Some (st, mds)
  | _ =>
      Corelib.Init.Datatypes.None
  end.



Require Import bluerock.ltac2.extra.extra.
Require Ltac2.Ltac2.

Import Ltac2.Ltac2.
Import Ltac2.Printf.

From Ltac2 Require Import Ltac2 String.
  Ltac2 newlines () : string := String.concat (string.String.newline ()) [string.String.newline (); string.String.newline ()].

Ltac2 missingSpecs tu s := 
  match cpp_proof.parse_fn_spec s with
  | (sp_parsed, nm, sp) =>
      let (missing, deps) := cpp_proof.bundle_deps tu nm sp in
      printf "%a"
        (Printf.pp_list_sep (newlines ()) Printf.pp_constr)
        (Constr.ConstrSet.elements missing)
  end.


(** caller should ensure that l is nonempty *)
Definition maxL (l: list N) : N :=
  match l with
  | [] => 0
  | x :: xs => fold_left N.max xs x
  end.

(** caller should ensure that l is nonempty *)
Definition minL (l: list N) : N :=
  match l with
  | [] => 0
  | x :: xs => fold_left N.min xs x
  end.


(** [splitL n l] splits [l] into the first [n] elements and the remainder,
    used to partition finalized vs unfinalized block groups in [validDbModel]. *)
Definition splitL {A} (n: N) (l: list A) : list A * list A :=
  (takeN n l, dropN n l).

(** nth element of a list *)
Definition nthElem {A: Type} (l: list A) (n: N) : option A :=
  nth_error l (N.to_nat n).


Ltac searchL t :=
  try (IPM.perm_left ltac:(fun L _ =>
                             match L with
                             | context[t] => idtac L; fail
                             end
      )).
