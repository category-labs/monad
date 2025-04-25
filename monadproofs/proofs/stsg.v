(*
 * Copyright © 2020 BlueRock Security, Inc. (“BlueRock”)
 *
 * This file is CONFIDENTIAL AND PROPRIETARY to BlueRock. All rights reserved.
 *
 * Use of this file is only permitted subject to a separate written license agreement with BlueRock.
*)

(*
 * The following code is derived from code original to the
 * Iris project. That original code is
 *
 *	Copyright Iris developers and contributors
 *
 * and used according to the following license.
 *
 *	SPDX-License-Identifier: BSD-3-Clause
 *
 * Original Code:
 * https://gitlab.mpi-sws.org/iris/iris/blob/b958d569a1613c673ff52be14661b298a56b71fc/theories/algebra/sts.v
 * Original Iris License:
 * https://gitlab.mpi-sws.org/iris/iris/blob/b958d569a1613c673ff52be14661b298a56b71fc/LICENSE-CODE
 *)

(**
   The guarded STS library embeds a labeled transition system into SL where
   transitions are guarded by tokens.

   Example. Consider the following flag STS.
   <<
     false ---{}---> true
           <-{RST}--
   >>
   The state can freely transition from [false] to [true] without requiring any
   tokens, but requires the [RST] (reset) token to transition the state from
   [true] to [false].

   The state of the STS and the partitioning of the tokens is expressed using
   an <<auth>>/<<frag>> pattern with the following predicates which bundle the
   tokens and the state.
   - [sts_auth S s ts] states the current state is exactly [s] and [ts] tokens have
     not been given out to any party.
   - [sts_frag S ss ts] asserts ownership of tokens [ts] and states that the current authoritative state is included in
     [ss] and that [ss] is closed under transitions that do *not* require
     tokens in [ts].

   The authoritative state ([sts_auth S s ts]) may be updated to any new state [s']
   as long as [s'] is reachable from [s] using only tokens in [ts].

   Guarded STSs admit a subtle theory to ensure that
   [valid (A ⋅ B) -> valid A /\ valid B]. The validity theory includes:
   - [valid (sts_auth S s ts) <-> True]
   - [valid (sts_frag S ss ts) <-> NonEmpty ss /\ closed ss ts]
     i.e. [ss] is closed under transitions that do *not* require any
     tokens in [ts].
   - [sts_auth S s ts ⋅ sts_frag S ss ts' -> s ∈ ss /\ ts ∩ ts' = ∅]
   - [sts_frag S ss1 ts1 ⋅ sts_frag S ss2 ts2 -> ss1 ∩ ss2 <> ∅ /\ ts1 ∩ ts2 = ∅]

   Because of this the following equations only hold when both sides are [valid].
   - [sts_auth S s ts ⋅ sts_frag S ss ts' ≡ sts_auth S s (ts ∪ ts')
   - [sts_frag S ss1 ts1 ⋅ sts_frag S ss2 ts2 ≡ sts_frag S (ss1 ∩ ss2) (ts1 ∪ ts2)]

   Idiomatic reasoning in this theory involves saturating validity facts and
   canonicalizing all elements, performing appropriate updates, and then
   breaking up the combined element appropriately.
 *)

Require Import bluerock.auto.miscPure.
Require Export stdpp.propset.
Require Export iris.algebra.cmra.
Require Import monad.proofs.dra.
Require Import bluerock.iris.extra.base_logic.iprop_own.
Require Import bluerock.iris.extra.proofmode.proofmode.
Set Default Proof Using "Type".
Local Arguments valid _ _ !_ /.
Local Arguments op _ _ !_ !_ /.
Local Arguments core _ _ !_ /.
Notation "a |--> r" := (own a r) (at level 80).

(** * Definition of STSs  *)
Module sts.
  Structure stsT := Sts {
    state : Type;
    token : Type;
    (* [stepr] should specify exactly the tokens needed and can choose any
       specific ordering. Below, [step], deals with the case
       of having more tokens and set equivalence (ordering/multiplicity invariance) *)
    stepr :  forall (keys: propset token), state -> state -> Prop;
  }.

  Arguments Sts {_ _} _.
  Arguments stepr {_} _ _.
  Notation states sts := (propset (state sts)).
  Notation tokens sts := (propset (token sts)).

  (** * Theory and definitions *)
  Section sts.
    Context {sts : stsT}.
    Definition step  (allKeys: tokens sts) (s1 s2 : state sts): Prop :=
      exists usedKeys, stepr usedKeys s1 s2 /\  usedKeys ⊆ allKeys.

    Notation steps := (rtc step).
    Definition frame_step (myTokens : tokens sts) (s1 s2 : state sts) : Prop :=
      exists ts, step ts s1 s2 /\ ts ## myTokens.

    (** ** Closure under frame steps *)
    Definition closed (S : states sts) (myTokens : tokens sts) : Prop :=
      forall s1 s2, s1 ∈ S → frame_step myTokens s1 s2 → s2 ∈ S.

    Definition frame_steps t := (rtc (frame_step t)).

    Definition up (s : state sts) (T : tokens sts) : states sts :=
      {[ s' | frame_steps T s s' ]}.

    Definition up_set (S : states sts) (T : tokens sts) : states sts :=
      S ≫= λ s, up s T.

    (** Tactic setup *)
    #[local] Hint Extern 50 (equiv (A:=propset _) _ _) => set_solver : sts.
    #[local] Hint Extern 50 (¬equiv (A:=propset _) _ _) => set_solver : sts.
    #[local] Hint Extern 50 (_ ∈ _) => set_solver : sts.
    #[local] Hint Extern 50 (_ ⊆ _) => set_solver : sts.
    #[local] Hint Extern 50 (_ ## _) => set_solver : sts.

    (** ** Setoids *)
    (* if I own fewer tokens, more frame/environment steps are possible *)
    Instance frame_step_mono : Proper (flip (⊆) ==> (=) ==> (=) ==> impl) frame_step.
    Proof.
      intros ?? HT ?? <- ?? <-; destruct 1; econstructor;
        eauto with sts; try set_solver.
      destruct H.
      split; eauto. set_solver.
    Qed.

    Global Instance frame_step_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) frame_step.
    Proof. solve_proper. Qed.

    Instance frame_steps_proper' : Proper ((≡) ==> (=) ==> (=) ==> impl) (frame_steps).
    Proof.
      intros  ? ? ? ? ? ? ? ? ? ?.
      subst.
      unfold frame_steps in *.
      induction H2; eauto with sts.
      reflexivity.
      econstructor; eauto.
      eapply frame_step_proper;[ | | | eauto]; eauto.
    Qed.

    Global Instance frame_steps_proper : Proper ((≡) ==> (=) ==> (=) ==> iff) (frame_steps).
    Proof.
      intros  ? ? ? ? ? ? ? ? ?.
      split; apply frame_steps_proper'; eauto.
    Qed.

    Instance closed_proper_sub : Proper ( (≡) ==> (⊆) ==> impl) closed.
    Proof.
      unfold closed. intros  ? ? ? ? ? ? ? ? ? ? ?.
      hnf in H3. miscPure.forward_reason.
      rewrite <- H in H2.
      rewrite <- H.
      specialize (H1 _ s2  H2).
      apply H1. exists ts. split; eauto.
      set_solver.
    Qed.

    Instance closed_proper' : Proper ((≡) ==> (≡) ==> impl) closed.
    Proof.
      intros ? ? ? ? ? ?.
      apply closed_proper_sub; auto; set_solver.
    Qed.

    Global Instance closed_proper : Proper ((≡) ==> (≡) ==> iff) closed.
    Proof. by split; apply closed_proper'. Qed.

    Lemma  Frame_step myToks T s1 s2:
      T ## myToks → step T s1 s2 → frame_step myToks s1 s2.
    Proof using.
      intros a b.
      hnf.
      eexists. split; eauto.
    Qed.

    (* the more tokens I have, the smaller is the transitive closure *)
    Global Instance up_preserving : Proper ((=) ==> flip (⊆) ==> (⊆)) up.
    Proof.
      intros s ? <- T T' HT ; apply elem_of_subseteq.
      induction 1 as [|s1 s2 s3 [T1 T2]]; [constructor|].
      miscPure.forward_reason.
      eapply elem_of_PropSet, rtc_l;
        [eapply Frame_step|]; eauto with sts.
      set_solver.
    Qed.

    Lemma propSetEquiv {A:Type} (P Q: A->Prop) :
      (forall x, P x <-> Q x) -> {[ x | P x ]} ≡ {[ x | Q x ]}.
    Proof. by move => H x; rewrite 2!elem_of_PropSet. Qed.

    Global Instance up_proper : Proper ((=) ==> (≡) ==> (≡)) up.
    Proof.
      intros ? ? ? ? ? H. subst.
      unfold up.
      apply propSetEquiv.
      intros. rewrite H.
      reflexivity.
    Qed.

    Global Instance up_set_preserving : Proper ((⊆) ==> flip (⊆) ==> (⊆)) up_set.
    Proof.
      intros S1 S2 HS T1 T2 HT. rewrite /up_set.
      f_equiv=> // s1 s2. by apply up_preserving.
    Qed.
    Global Instance up_set_proper : Proper ((≡) ==> (≡) ==> (≡)) up_set.
    Proof. solve_proper. Qed.

    (** ** Properties of closure under frame steps *)
    Lemma closed_steps S T s1 s2 :
      closed S T → s1 ∈ S → frame_steps T s1 s2 → s2 ∈ S.
    Proof.
      unfold closed, frame_steps.
      intros.
      induction H1; eauto.
    Qed.

    Lemma closed_op T1 T2 S1 S2 :
      closed S1 T1 → closed S2 T2 → closed (S1 ∩ S2) (T1 ∪ T2).
    Proof.
      intros Ha Hb. unfold closed.
      intros ? ? Hint Hf.
      apply elem_of_intersection in Hint.
      miscPure.forward_reason.
      unfold closed in *.
      specialize (fun s2 => Ha _ s2 Hintl).
      specialize (fun s2 => Hb _ s2 Hintr).
      hnf in Hf.
      miscPure.forward_reason.
      apply elem_of_intersection.
      split; [apply Ha | apply Hb]; hnf; exists ts;
        split; eauto;set_solver.
    Qed.

    Lemma step_closed T s1 s2 S Tf :
      step T s1 s2 -> T ## Tf → closed S Tf → s1 ∈ S
      → s2 ∈ S.
    Proof.
      intros.
      unfold closed in H1.
      specialize (H1 s1 s2 H2).
      apply H1.
      clear H1.
      hnf.
      exists T.
      split; auto.
    Qed.

    Lemma steps_closed T s1 s2 S Tf :
      rtc (step T) s1 s2 -> T ## Tf → closed S Tf → s1 ∈ S
      → s2 ∈ S.
    Proof.
      intros Hsteps.
      induction Hsteps as [?|? ? ? Hstep Hsteps IH];
        intros; simplify_eq; first done.
      apply IH; eauto.
      eapply step_closed; eauto.
    Qed.

    (** ** Properties of the closure operators *)
    Lemma elem_of_up s T : s ∈ up s T.
    Proof. constructor. Qed.
    Lemma subseteq_up_set S T : S ⊆ up_set S T.
    Proof. intros s ?; apply elem_of_bind; eauto using elem_of_up. Qed.
    Lemma elem_of_up_set S T s : s ∈ S → s ∈ up_set S T.
    Proof. apply subseteq_up_set. Qed.
    Lemma up_up_set s T : up s T ≡ up_set {[ s ]} T.
    Proof. by rewrite /up_set set_bind_singleton. Qed.

    Lemma closed_up_set S T : closed (up_set S T) T.
    Proof.
      unfold closed.
      intros.
      hnf in H0.
      unfold up_set in *.
      rewrite -> elem_of_bind in *.
      miscPure.forward_reason.
      unfold up in *.
      exists y.
      split; auto.
      setoid_rewrite elem_of_PropSet in Hl.
      apply elem_of_PropSet.
      eapply rtc_r; eauto.
      hnf. exists ts. split; auto.
    Qed.

    Lemma closed_up s T : closed (up s T) T.
    Proof.
      intros; rewrite -(set_bind_singleton (λ s, up s T) s).
      apply closed_up_set; set_solver.
    Qed.

    Lemma up_closed S T : closed S T → up_set S T ≡ S.
    Proof.
      intros ?; apply set_equiv_subseteq; split; auto using subseteq_up_set.
      intros s; unfold up_set; rewrite elem_of_bind; intros (s'&Hstep&?).
      hnf in H.
      induction Hstep; eauto.
    Qed.

    Lemma up_subseteq s T S : closed S T → s ∈ S → sts.up s T ⊆ S.
    Proof. move=> ?? s' ?. eauto using closed_steps. Qed.
    Lemma up_set_subseteq S1 T S2 : closed S2 T → S1 ⊆ S2 → sts.up_set S1 T ⊆ S2.
    Proof. move=> ?? s [s' [? ?]]. eauto using closed_steps. Qed.
    Lemma up_op s T1 T2 : up s (T1 ∪ T2) ⊆ up s T1 ∩ up s T2.
    Proof. (* Notice that the other direction does not hold. *)
      intros x Hx. split; eapply elem_of_PropSet, rtc_subrel; try exact Hx.
      - intros; eapply frame_step_mono; last first; try done. set_solver+.
      - intros; eapply frame_step_mono; last first; try done. set_solver+.
    Qed.
  End sts.

  (* The type of bounds we can give to the state of an STS. This is the type
    that we equip with an RA structure. *)
  Inductive car (sts : stsT) :=
    | auth : state sts → tokens sts → car sts
    | frag : propset (state sts) → tokens sts → car sts.
  Arguments auth {_} _ _.
  Arguments frag {_} _ _.
End sts.

Notation stsT := sts.stsT.
Notation Sts := sts.Sts.

(** * STSs form a disjoint RA *)
Section sts_dra.
  Context (sts : stsT).
  Import sts.
  Implicit Types S : states sts.
  Implicit Types T : tokens sts.

  Inductive sts_equiv : Equiv (car sts) :=
    | auth_equiv s T1 T2 : T1 ≡ T2 → auth s T1 ≡ auth s T2
    | frag_equiv S1 S2 T1 T2 : T1 ≡ T2 → S1 ≡ S2 → frag S1 T1 ≡ frag S2 T2.

  Existing Instance sts_equiv.

  #[global] Instance sts_valid : Valid (car sts) := λ x,
    match x with
    | auth s T => True
    | frag S' T => closed S' T ∧  ∃ s, s ∈ S'
    end.

  (* what does the core represent. where is this used? *)
  #[global] Instance sts_core : PCore (car sts) := λ x,
    match x with
    | frag S' _ => Some (frag (up_set S' ∅ ) ∅)
    | auth s _  => Some (frag (up s ∅) ∅)
    end.

  (* this should rather be called "compatible" *)
  Inductive sts_disjoint : Disjoint (car sts) :=
    | frag_frag_disjoint S1 S2 T1 T2 :
      (∃ s, s ∈ S1 ∩ S2) → T1 ## T2 → frag S1 T1 ## frag S2 T2
    | auth_frag_disjoint s S T1 T2 : s ∈ S → T1 ## T2 → auth s T1 ## frag S T2
    | frag_auth_disjoint s S T1 T2 : s ∈ S → T1 ## T2 → frag S T1 ## auth s T2.
  (* disjointness is always symmetric. thus there should not be a need to specify
     this explicity. instead, there should be a relation transformer to perform
     closure under symmetry *)

  Existing Instance sts_disjoint.
  #[global] Instance sts_op : Op (car sts) := λ x1 x2,
    match x1, x2 with
    | frag S1 T1, frag S2 T2 => frag (S1 ∩ S2) (T1 ∪ T2)
    | auth s T1, frag _ T2 => auth s (T1 ∪ T2)
    | frag _ T1, auth s T2 => auth s (T1 ∪ T2)
      (* the use of [sts_disjoint] guarantees the next case will
         never happen. *)
    | auth s T1, auth _ T2 => auth s (T1 ∪ T2)
    end.

  #[local] Hint Extern 50 (equiv (A:=propset _) _ _) => set_solver : sts.
  #[local] Hint Extern 50 (∃ s : state sts, _) => set_solver : sts.
  #[local] Hint Extern 50 (_ ∈ _) => set_solver : sts.
  #[local] Hint Extern 50 (_ ⊆ _) => set_solver : sts.
  #[local] Hint Extern 50 (_ ## _) => set_solver : sts.

  Global Instance auth_proper s : Proper ((≡) ==> (≡)) (@auth sts s).
  Proof. by constructor. Qed.
  Global Instance frag_proper : Proper ((≡) ==> (≡) ==> (≡)) (@frag sts).
  Proof. by constructor. Qed.

  Instance sts_equivalence: Equivalence ((≡) : relation (car sts)).
  Proof.
    split.
    - by intros []; constructor.
    - by destruct 1; constructor.
    - destruct 1; inversion_clear 1; constructor; etrans; eauto.
  Qed.

  Lemma appSym {A:Type} (a b: propset A):
    a ∪ b ≡ b ∪ a.
  Proof. set_solver. Qed.

  #[local] Hint Resolve appSym: sts.


  Lemma sts_dra_mixin : DraMixin (car sts).
  Proof.
    split.
    - apply _.
    - intros ? ? ? ? ? ?.
      unfold op. unfold sts_op.
      destruct H; destruct H0; setoid_subst; auto.
    - by destruct 1; constructor; setoid_subst.
    - by destruct 1; simpl; intros ?; setoid_subst.
    - by intros ? [|]; destruct 1; inversion_clear 1; econstructor; setoid_subst.
    - destruct 3; simpl in *; destruct_and?; eauto using closed_op;
        match goal with H : closed _ _ |- _ => destruct H end; set_solver.
    - intros [];    naive_solver eauto using closed_up, closed_up_set,
        elem_of_up, elem_of_up_set with sts.
    - intros [] [] [] _ _ _ _ _; constructor; rewrite ?assoc; auto with sts.
    - destruct 4; inversion_clear 1; constructor; auto with sts.
    - destruct 4; inversion_clear 1; constructor; auto with sts.
    - destruct 1; constructor; auto with sts.
    - destruct 3; constructor; try auto with sts.
    - intros []; constructor; eauto with sts.
    - intros []; constructor; auto with sts.
    - intros [s T|S T]; constructor; auto with sts.
      + rewrite (up_closed (up _ _)); auto using closed_up with sts.
      + rewrite (up_closed (up_set _ _)); eauto using closed_up_set with sts.
    - intros x y. exists (core (x ⋅ y))=> ?? Hxy; split_and?.
      + destruct Hxy; constructor; unfold up_set; set_solver.
      + destruct Hxy; simpl;
          eauto using closed_up_set, closed_up with sts.
      + destruct Hxy; econstructor;
          repeat match goal with
          | |- context [ up_set ?S ?T ] =>
            unless (S ⊆ up_set S T) by done; pose proof (subseteq_up_set S T)
          | |- context [ up ?s ?T ] =>
            unless (s ∈ up s T) by done; pose proof (elem_of_up s T)
          end; auto with sts.
  Qed.
  Canonical Structure stsDR : draT := DraT (car sts) sts_dra_mixin.
End sts_dra.

(** * The STS Resource Algebra *)
(** Finally, the general theory of STS that should be used by users *)
Notation stsC sts := (validityO (stsDR sts)).
Notation stsR sts := (validityR (stsDR sts)).

Section sts_definitions.
  Context {sts : stsT}.
  Definition sts_auth (s : sts.state sts) (T : sts.tokens sts) : stsR sts :=
    to_validity (sts.auth s T).
  Definition sts_frag (S : sts.states sts) (T : sts.tokens sts) : stsR sts :=
    to_validity (sts.frag S T).
  Definition sts_frag_up (s : sts.state sts) (T : sts.tokens sts) : stsR sts :=
    sts_frag (sts.up s T) T.
End sts_definitions.
#[global] Instance: Params (@sts_auth) 2 := {}.
#[global] Instance: Params (@sts_frag) 1 := {}.
#[global] Instance: Params (@sts_frag_up) 2 := {}.

Section stsRA.
  Import sts.
  Context {sts : stsT}.
  Implicit Types s : state sts.
  Implicit Types S : states sts.
  Implicit Types T : tokens sts.
  Arguments dra_valid _ !_/.

  (** Setoids *)
  Global Instance sts_auth_proper s : Proper ((≡) ==> (≡)) (sts_auth s).
  Proof. solve_proper. Qed.
  Global Instance sts_frag_proper : Proper ((≡) ==> (≡) ==> (≡)) (@sts_frag sts).
  Proof. solve_proper. Qed.
  Global Instance sts_frag_up_proper s : Proper ((≡) ==> (≡)) (sts_frag_up s).
  Proof. solve_proper. Qed.

  (** Validity *)
  Lemma sts_auth_valid s T : ✓ sts_auth s T.
  Proof. done. Qed.
  Lemma sts_frag_valid S T : ✓ sts_frag S T ↔ closed S T ∧ ∃ s, s ∈ S.
  Proof. done. Qed.
  Lemma sts_frag_up_valid s T : ✓ sts_frag_up s T .
  Proof.
    - intros. apply sts_frag_valid; split. by apply closed_up. set_solver.
  Qed.

  Lemma sts_auth_frag_valid_inv s S T1 T2 :
    ✓ (sts_auth s T1 ⋅ sts_frag S T2) → s ∈ S.
  Proof. by intros (?&?&Hdisj); inversion Hdisj. Qed.

  (** Op *)
  Lemma sts_op_auth_frag s S T :
    s ∈ S → closed S T → sts_auth s ∅ ⋅ sts_frag S T ≡ sts_auth s T.
  Proof.
    intros; split; [split|constructor; set_solver]; simpl.
    - tauto.
    - firstorder. hnf.
      constructor; auto.
      set_solver.
  Qed.

  Lemma sts_op_auth_frag_up s T :
    sts_auth s ∅ ⋅ sts_frag_up s T ≡ sts_auth s T.
  Proof.
    intros; split; [split|constructor; set_solver]; simpl.
    - intros (?&[??]&?). tauto.
    - intros; split_and?.
      + tauto.
      + by apply closed_up.
      + exists s. set_solver.
      + constructor; last set_solver. apply elem_of_up.
  Qed.

  Lemma sts_op_frag S1 S2 T1 T2 :
    T1 ## T2 → sts.closed S1 T1 → sts.closed S2 T2 →
    sts_frag (S1 ∩ S2) (T1 ∪ T2) ≡ sts_frag S1 T1 ⋅ sts_frag S2 T2.
  Proof.
    intros HT HS1 HS2. rewrite /sts_frag -to_validity_op //.
    move=>/=[?[? ?]]. split_and!; [set_solver..|constructor; set_solver].
  Qed.

  Lemma sts_op_auth_fragg s S T Ta :
    Ta ## T->  s ∈ S → closed S T → sts_auth s Ta ⋅ sts_frag S T ≡ sts_auth s (T ∪ Ta).
  Proof.
    intros; split; [split|constructor; set_solver]; simpl.
    - tauto.
    - firstorder. hnf.
      constructor; auto.
  Qed.
  
  (* Notice that the following does *not* hold -- the composition of the
    two closures is weaker than the closure with the itnersected token
    set.  Also see up_op.
  Lemma sts_op_frag_up s T1 T2 :
    T1 ## T2 → sts_frag_up s (T1 ∪ T2) ≡ sts_frag_up s T1 ⋅ sts_frag_up s T2.
  *)

  (** Frame preserving updates *)
  Lemma sts_update_auth s1 s2 T :
    rtc (step T) s1 s2 → sts_auth s1 T ~~> sts_auth s2 T.
  Proof.
    intros ?; apply validity_update.
    intros ? Ha Hb Hc.
    hnf in Hc.
    inversion Hc. subst. simplify_eq/=. destruct_and?.
    pose proof (steps_closed T s1 s2 S T2); auto.
    repeat (done || constructor).
    apply H3; auto.
  Qed.

  Lemma sts_update_frag S1 S2 T1 T2 :
    (closed S1 T1 → closed S2 T2 ∧ S1 ⊆ S2 ∧ T2 ⊆ T1) → sts_frag S1 T1 ~~> sts_frag S2 T2.
  Proof.
    rewrite /sts_frag=> HC HS HT. apply validity_update.
    inversion 3 as [|? S ? Tf|]; simplify_eq/=;
      (destruct HC as (? & ? & ?); first by destruct_and?).
    - split_and!. done. set_solver. constructor; set_solver.
    - split_and!. done. set_solver. constructor; set_solver.
  Qed.

  Lemma sts_update_frag_up s1 S2 T1 T2 :
    (closed S2 T2) → s1 ∈ S2 → T2 ⊆ T1 → sts_frag_up s1 T1 ~~> sts_frag S2 T2.
  Proof.
    intros HC ? HT; apply sts_update_frag.
    intros HC1; split; last split; eauto using closed_steps.
    - rewrite <-HT. eapply up_subseteq; last done.
      eauto using HC, HC1, elem_of_up.
  Qed.

  Lemma sts_up_set_intersection S1 Sf Tf :
    closed Sf Tf → S1 ∩ Sf ≡ S1 ∩ up_set (S1 ∩ Sf) Tf.
  Proof.
    intros Hclf. apply (anti_symm (⊆)).
    - move=>s [HS1 HSf]. split. by apply HS1. by apply subseteq_up_set.
    - move=>s [HS1 [s' [/elem_of_PropSet Hsup Hs']]]. split; first done.
      eapply closed_steps, Hsup; first done. set_solver +Hs'.
  Qed.

  Global Instance sts_frag_core_id S : CoreId (sts_frag S ∅).
  Proof.
    constructor; split=> //= [[??]]. by rewrite /= sts.up_closed.
  Qed.

  Lemma closed_iff (S: states sts) (mytoks: tokens sts):
    (∀ s1 s2 otherToks, mytoks ## otherToks → s1 ∈ S → sts.step otherToks s1 s2 ->  s2 ∈ S)
    <-> closed S mytoks.
  Proof using.
    unfold closed, frame_step.
    intuition; forward_reason; eauto.
  Qed.
  
  (** Inclusion *)
  (* This is surprisingly different from to_validity_included. I am not sure
    whether this is because to_validity_included is non-canonical, or this
    one here is non-canonical - but I suspect both. *)
  (* TODO: These have to be proven again. *)
  (*
  Lemma sts_frag_included S1 S2 T1 T2 :
    closed S2 T2 → S2 ≢ ∅ →
    (sts_frag S1 T1 ≼ sts_frag S2 T2) ↔
    (closed S1 T1 ∧ S1 ≢ ∅ ∧ ∃ Tf, T2 ≡ T1 ∪ Tf ∧ T1 ## Tf ∧
                                  S2 ≡ S1 ∩ up_set S2 Tf).
  Proof.
    intros ??; split.
    - intros [[???] ?].
    destruct (to_validity_included (sts_dra.car sts) (sts_dra.frag S1 T1) (sts_dra.frag S2 T2)) as [Hfincl Htoincl].
    intros Hcl2 HS2ne. split.
    - intros Hincl. destruct Hfincl as ((Hcl1 & ?) & (z & EQ & Hval & Hdisj)).
      { split; last done. split; done. }
      clear Htoincl. split_and!; try done; [].
      destruct z as [sf Tf|Sf Tf].
      { exfalso. inversion_clear EQ. }
      exists Tf. inversion_clear EQ as [|? ? ? ? HT2 HS2].
      inversion_clear Hdisj as [? ? ? ? _ HTdisj | |]. split_and!; [done..|].
      rewrite HS2. apply up_set_intersection. apply Hval.
    - intros (Hcl & Hne & (Tf & HT & HTdisj & HS)). destruct Htoincl as ((Hcl' & ?) & (z & EQ)); last first.
      { exists z. exact EQ. } clear Hfincl.
      split; first (split; done). exists (sts_dra.frag (up_set S2 Tf) Tf). split_and!.
      + constructor; done.
      + simpl. split.
        * apply closed_up_set. move=>s Hs2. move:(closed_disjoint _ _ Hcl2 _ Hs2).
          set_solver +HT.
        * by apply up_set_non_empty.
      + constructor; last done. by rewrite -HS.
  Qed.

  Lemma sts_frag_included' S1 S2 T :
    closed S2 T → closed S1 T → S2 ≢ ∅ → S1 ≢ ∅ → S2 ≡ S1 ∩ up_set S2 ∅ →
    sts_frag S1 T ≼ sts_frag S2 T.
  Proof.
    intros. apply sts_frag_included; split_and?; auto.
    exists ∅; split_and?; done || set_solver+.
  Qed. *)

  
End stsRA.

(*
Definition oneWay : stsT :=
  @Sts bool unit
      (fun keys init final => init=false /\ final=true).


Lemma sts_update_auth2:
  @sts_auth oneWay false [tt] ~~> @sts_auth oneWay true [tt].
Proof.
  apply sts_update_auth.
  econstructor. hnf. exists [tt]. hnf. split; eauto.
  constructor; auto.
  reflexivity.
Qed.

Lemma validity_update_iff  {A: draT} (x y : validity A) :
  (∀ c, ✓ x → ✓ c → validity_car x ## c → ✓ y ∧ validity_car y ## c) <-> x ~~> y.
Proof.
  split.
  - apply validity_update.
  - intros H. setoid_rewrite cmra_discrete_update in H.
    intros.
    hnf.
  split_and!; try eapply Hxy; eauto.
Admitted.

Lemma sts_update_auth3:
 ~ (@sts_auth oneWay true [tt] ~~> @sts_auth oneWay false [tt]).
Proof.
  intros Hc.
  rewrite <- validity_update_iff in Hc.
  specialize (Hc (@sts.frag oneWay {[ s | s=true]} [])).
  destruct Hc.
  -  hnf. auto.
  - hnf. firstorder. exists true. set_solver.
  - hnf. econstructor. set_solver. set_solver.
  - hnf in H0. inverts H0. inversion H4.
Qed.
*)

(** The CMRA we need. *)
Class stsG {Σ} (sts : stsT) := StsG {
  sts_inG ::> inG Σ (stsR sts);
}.

(*
Lemma sts_alloc `{!stsG Σ sts} s:
  |-- |=> ∃ γ, own γ (sts_auth s ⊤).
Proof.
  iIntros.
  iApply (@own_alloc _ _ _ _).
  hnf. auto.
Qed.
*)
