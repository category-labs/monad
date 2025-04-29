(*
 * Copyright © 2024 BlueRock Security, Inc. (“BlueRock”)
 *
 * This file is CONFIDENTIAL AND PROPRIETARY to BlueRock. All rights reserved.
 *
 * Use of this file is only permitted subject to a separate written license agreement with BlueRock.
 *)

Require Import bluerock.ltac2.extra.extra.
Require Import monad.fmai.prompts.main.
Require Import monad.fmai.driver.ltac2.print.
Require Import monad.fmai.driver.ltac2.gcd.

From AAC_tactics Require Import AAC.
From AAC_tactics Require Instances.
Import Instances.Z.
Require Import ZArith.
Require Import Psatz.
#[export] Instance aac_Z_gcd_Comm : Commutative eq Z.gcd := Z.gcd_comm.
#[export] Instance aac_Z_gcd_assoc : Associative eq Z.gcd := Z.gcd_assoc.
Require Import bluerock.auto.lazy_unfold.
Require Import bluerock.auto.cpp.elpi.derive.
Require Import bluerock.ltac2.llm.llm.

  (* FIX: this likely does not normalize inside deep subterms of non-airth context, e.g. foo (gcd a b).
then remove the shallow prefix
also, despite the try, this seems to trhow a "Cannot infer a lifting" error *)
  Ltac aac_normalise_all_shallow :=
    aac_normalise;
    repeat match goal with
      | H: _ |- _ => aac_normalise in H
      end.

From Coq Require PeanoNat ZArith List Permutation Lia.


Require Import Coq.ZArith.Znumtheory.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.specs.
Require Import bluerock.auto.tactics.
Require Import bluerock.auto.cpp.tactics4.
Require Import bluerock.cpp.array.
(* Require Import bluerock.hw_models.misc *)
Require Import bluerock.auto.fancy_module.

  br.lock Definition NodeR `{Σ : cpp_logic, σ : genv} (q: cQp.t) (data: Z) (nextPtr: ptr): Rep :=
    structR "::Node" q
    ** _field "::Node::data_" |-> primR Ti32                       (cQp.mut q) (Vint data)
    ** _field "::Node::next_" |-> primR (Tptr (Tnamed "::Node")) (cQp.mut q) (Vptr nextPtr).

 #[only(lazy_unfold(global))] derive NodeR.

    Open Scope Z_scope.
    Import Verbose.


Section Spec.
  Context `{Σ: cpp_logic} {gg: genv} {modd: module ⊧ gg}.
  Locate module.
  Ltac2 Eval DemangleAll.print_names 'module.
  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
        \arg{a:Z} "a" (Vint a)
        \arg{b:Z} "b" (Vint b)
        \post [Vint (Z.gcd a b)] emp
      ).

  Import Verbose.

    Open Scope Z_scope.
    Set Printing Coercions.
    Lemma wpl f ρ s Qs Q:
      (Forall v, Qs v -* Q v) **  (wp f ρ s (Kreturn (λ v : ptr, Qs v))) |--
        (wp f ρ s (Kcleanup module [] (Kreturn (λ v : ptr, |> Q v)))).
    Proof using. Admitted.

  Fixpoint ListR (q : cQp.t) (l : list Z) : Rep :=
    match l with
    | [] => nullR
    | hd :: tl => Exists (p : ptr), NodeR q hd p ** pureR (p |-> ListR q tl)
    end.

  cpp.spec "split(Node*, Node*&, Node*&)" as split_spec with
    (\arg{ab_ptr_val} "ab" (Vptr ab_ptr_val)
     \arg{a_ptr_val} "a" (Vref a_ptr_val)
     \arg{b_ptr_val} "b" (Vref b_ptr_val)
     \pre a_ptr_val |-> ptrR<Tnamed "_Z4Node"> (cQp.m 1) nullptr
     \pre b_ptr_val |-> ptrR<Tnamed "_Z4Node"> (cQp.m 1) nullptr
     \pre{l} ab_ptr_val |-> ListR (cQp.m 1) l
     \post Exists a_ptr_val_ptr_val b_ptr_val_ptr_val la lb,
        a_ptr_val |-> ptrR<Tnamed "_Z4Node"> (cQp.m 1) a_ptr_val_ptr_val **
        b_ptr_val |-> ptrR<Tnamed "_Z4Node"> (cQp.m 1) b_ptr_val_ptr_val **
        a_ptr_val_ptr_val |-> ListR (cQp.m 1) la **
        b_ptr_val_ptr_val |-> ListR (cQp.m 1) lb **
        [| Permutation l (la ++ lb) |]).


  Ltac gpt_rewrite foo :=
    (tryif rewrite foo then idtac else aac_rewrite foo);try lia.

  (* already moved to rwdb.v in MR cpp2v/!3358  Import that file here*)
  Hint Rewrite @left_id using (exact _): equiv.
  Hint Rewrite @right_id using (exact _): equiv.

  Lemma spurious {T:Type} {ing: Inhabited T} (P: mpred) :
  P |-- Exists a:T, P.
  Proof using.
    work.
    iExists (@inhabitant T _).
    work.
  Qed.

  Hint Rewrite <- @spurious using exact _: slbwd.
  Hint Resolve @prim.primR_aggressiveC: br_opacity.
  Hint Rewrite @inj_iff using (typeclasses eauto): iff.

  Ltac slauto :=
    go; (* TODO: hide evars *)
    try name_locals;
  tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic equiv iff slbwd in *; try rewrite left_id (* in equiv rw db but doesnt work *))
  then slauto
  else idtac.

  Ltac resultsIn0or1Goals tac := try (tac; fail); (tac;[]).
  Goal N->False -> False.
    intros x F.
    Fail resultsIn0or1Goals ltac:(destruct x).
    resultsIn0or1Goals idtac.
    resultsIn0or1Goals auto.
  Abort.
  Lemma absorb_nop_false: forall P:mpred, (<absorb> P = P)%I.
  Proof. Admitted.

  Hint Rewrite NodeR.unlock: unfold.
Ltac proveFalseWeak :=
  (simpl in *; autounfold with transparent; autorewrite with unfold; simpl in *; slauto; fail).
(* destruct non proof : *)

From Ltac2 Require Import Ltac2.
Print Ltac2 Signatures.
Import Printf.
Ltac2 postCond () : string :=
  lazy_match! goal with
  | [|- environments.envs_entails _ (wp _ _ _ ?post)] =>
      Message.to_string (fprintf "%t" post)
  end.


Ltac2 loopInvPrompt () : string :=
  String.concat ""
[
"
In this case the command is a while loop and thus we would to provide a loop invariant to continue the proof.
Please re-review carefylly the section titled 'Loop invariant example' where we illustrated how to find the loop invariant
for the loop in the gcd function.

Currently, the hypotheses denote the resources and what was true just before entering the loop.
Typically, to prove a loop, one has to generalize the hypotheses so that they hold EVERY even at
the beginning of all subsequent iterations of the loop.
The generalized set of hypotheses is called the loop invariant.

Note that it also important that the loop invariant is strong enough to prove the function postcondition
when the loop terminates.
If this loop is at the end of the function, the loop invariant should imply the postcondition.
In this case, the postcondition is:
```coq
";
postCond ();
"
```
Some items in the postcondition just require returning back the ownership of location storing the function call arguments. (This prevents the function from storing this ownership in some data-structure that lives beyond this function call).
The values stored at those locations are existentially quantified (using `Exist`) and unconstrained.

You need to now tell me the loop invariant as a separation logic assertion of type `mpred`.
Be very mindful of the Coq syntax and ensure that it typechecks as I will enter what you suggest in my coq proof.
Note that if the loop invariant has multiple hypotheses, you can combine them by `**`.
Also, recall that pure hypotheses `P:Prop` can be represented as mpred as `[| P |]`.
If some spatial or pure hypothesis does not change during the loop execution, you do not need to mention it in the loop invariant. It would be automatically included.

You may need to use existential quantification (using `Exist`) to allow the variables to change their values from their initial values at the beginning of the loop. But then you must add constraints about the existentially quantified new values to ensure that when the loop terminates, the postcondition is satisified.

So, first informally (NOT in Coq) tell me what should be the loop invariant and why it is correct:
1) the loop invariant is preserved by each iteration of the loop
2) the loop invariant implies the postcondition when the loop terminates and runs the remaining code of the function

After the informal reasoning looks satisfactory, write the loop invariant in Coq.

The last ```coq ``` code block in your response must contain exactly the loop invariant written in proper Coq syntax and nothing else.
I will parse the loop invariant from your textual output and plug into my proof.
You can include the formal loop invariant (written in Coq) in earlier blocks as well to explain, but I will not enter them in Coq.

"].

  Ltac2 destructSomeVar () : message list :=
  match! goal with
  | [ h: list _ (* generalize to destructible_type *) |- _ ] =>
      printf "(* trying to destruct %I *)" h;
      ltac1:(hh |- resultsIn0or1Goals ltac:(destruct hh; try proveFalseWeak)) (Ltac1.of_ident h);
      [fprintf "destruct %I; proveFalseWeak" h] (* can this loop ? *)
  end.
  Hint Unfold NodeR: transparent. (* before a proof, ask GPT to come up with this? at least put in here all the Rep predicates mentioned in the spec. then, can try iteratively adding more: stuff mentioned in those Rep, as long as those Reps do not belong to another library *)

    Hint Opaque NodeR ListR: br_opacity.

  Lemma learn_list_nil x (y: list Z) : Learnable emp (nullptr |-> ListR (cQp.mut 1) x) [x=[]].
  Proof using.
    constructor.
    apply Some.
    hnf.
    ltac1:(slauto). (* can we make ltac1 the default so that the prefix is not needed? *)
    do 3 (rewrite -> absorb_nop_false).
    (destructSomeVar ()).
  Qed.

  (* TODO:
     specialize llm prompt to do output the correct loopinv and show that the full proof can be printed. add the missing gcd lemmas to db *)

  Ltac2 mutable x := 1.

  Ltac simplPure :=
    simpl in *; autorewrite with syntactic equiv iff  in *; try rewrite left_id in *; simpl in *.

  Ltac2 goalNotDone () : bool :=
    Control.plus (fun _ => Control.focus 1 1 (fun _ => true)) (fun _ => false).
  Ltac2 tryTac (tac: ( unit -> message list)) : message list  :=
    if goalNotDone () then
      match Control.case (fun _ => Control.plus tac (fun _ => [])) with
      | Err _ => []
      | Val (m, _ )=> m
      end
    else [].

  (* this is an ugly hack to work around a severe bug in coq, which is fixed in Coq 8.20
     https://github.com/coq-community/aac-tactics/issues/144
     Below, there is more ugliness cited to this issue.
     In Coq 8.20, this shoud just be
     `try aac_rewrite H; try aac_rewrite H in_right`.
     That may not rewrite deep inside terms. if so, one may need to build a deeper wrapper
     around aac_tatics. aac_normalize may have a similar issue mentioned above.
   *)
  Ltac aacrw H :=
    match goal with
    | |- ?l = _ =>
        match l with
          | context[Z.gcd _ _] =>
              aac_rewrite H
        end
    | |- _ = ?r =>
        match r with
          | context[Z.gcd _ _] =>
              aac_rewrite H in_right
        end
    end.

  Tactic Notation "aac_rewrite" uconstr(L) := (aacrw L).

  Lemma trans4 `{Equivalence} a b a' b': R a a' -> R b b' -> R a b -> R a' b'.
  Proof. now intros -> ->. Qed.

  Tactic Notation "aac_rewrite" uconstr(L) "in" hyp(H) :=
    (eapply trans4 in H;[| try aac_rewrite L; try reflexivity | try aac_rewrite L; try reflexivity ]).


  (* replace `rewrite foo` emitted by GPT by `gpt_rewrite foo` *)
  Tactic Notation "gpt_rewrite" uconstr(L) := (gpt_rewrite L).
  Tactic Notation "gpt_rewrite" uconstr(L) "in" hyp(H) :=
    (tryif rewrite L then idtac else aac_rewrite L in H).


  Ltac2 rec tryEvalConcatMsgs (tacs: ( unit -> message list) list) : message list :=
    match tacs with
    | [] => []
    | h::tl =>
        let msgs := tryTac h in
        List.append msgs (tryEvalConcatMsgs tl)
    end.

  Ltac2 goalDoneB () : bool :=
    Control.plus (fun _ => Control.focus 1 1 (fun _ => false)) (fun _ => true).

  Ltac2 rec repeatM (accumulatedSteps: message list) (tac: ( unit -> message list)) : message list  :=
    if goalDoneB () then accumulatedSteps else
    let oneStep := Control.plus (fun _ => Control.progress tac) (fun _ => []) in
    match oneStep with
    | [] => accumulatedSteps
    | _::_ => repeatM (List.append accumulatedSteps oneStep) tac
    end.

  Ltac2 aac_norm_in_hyps () : message list :=
    match! goal with
    | [ h:_ |- _] =>
        ltac1:(h |- aac_normalise in h) (Ltac1.of_ident h);
        [fprintf "aac_normalise in %I." h] (* this can fail if h is an autogenerated reserved name. we can write an Ltac2 to find a unique pattern that identifies this hypothesis's type and use that instead of name: that may be a weeklong project but could be generally useful e.g. in the proposed proof robustification engine *)
      end.

  Ltac2 aac_normaliseM () : message list:= ltac1:(aac_normalise); [fprintf "aac_normalise."].
  Ltac2 aac_normalise_all_shallowM () : message list :=
    let oneStep := Control.plus (fun _=> Control.progress aac_normaliseM) (fun _ => []) in
    repeatM oneStep  aac_norm_in_hyps.


  (* TODO: make it more frugal:
     1) only invoke arith_solve on the main goal if it actually solved it
     2) reimplement arith_solve to print a frugal proofs script only including steps that mattered. in most cases, just [faster_lia] works *)
  Ltac2 aacrwM (r: constr) : message list:=
    ltac1:(rr |- resultsIn0or1Goals ltac:(aac_rewrite rr; try Arith.arith_solve)) (Ltac1.of_constr r); [fprintf "aac_rewrite %t; try Arith.arith_solve." r].

  Ltac2 aacrwMH (r: constr) : message list:=
    match! goal with
    | [ h:_ |- _] =>
        ltac1:(rr hh |- resultsIn0or1Goals ltac:(aac_rewrite rr in hh; try Arith.arith_solve))
                (Ltac1.of_constr r) (Ltac1.of_ident h);
        [fprintf "aac_rewrite %t in %I; try Arith.arith_solve." r h]
      end.

  (* the caller is supposed to enusre that tac only succeeds if it makes progress *)
  Ltac2 rec iterConstrM (lemmas: constr list) (tac: constr -> message list)
    (accumulatedSteps: message list): message list :=
    match lemmas with
    | h::tl =>
      if goalDoneB () then accumulatedSteps else
        let onestep :=
          Control.plus (fun _ => tac h) (fun _ => []) in
        iterConstrM tl tac (List.append accumulatedSteps onestep)
    | [] =>accumulatedSteps
    end.

  Ltac2 rec aacrwML (lemmas: constr list): message list :=
    iterConstrM lemmas aacrwM [].

  Ltac2 rec aacrwMLH (lemmas: constr list) : message list :=
    iterConstrM lemmas (fun h => repeatM [] (fun _ => aacrwMH h)) [].

  Ltac2 rec aacrwMLall (lemmas: constr list): message list :=
    lazy_match! goal with (* needed due to bug in aac_tactics. remove when coq updated to 8.20 https://github.com/coq-community/aac-tactics/issues/144 *)
    | [ |- _ = _] =>

        let mc := aacrwML lemmas in
        if goalDoneB () then mc
        else let mh := aacrwMLH lemmas in List.append mc mh
    | [ |- _ ] => []
    end.

  Ltac2 arithSolveM () : message list:=
    ltac1:(Arith.arith_solve); [fprintf "Arith.arith_solve."].

  Open Scope list_scope.

  Lemma cons_as_app {T} (l:list T) (h:T): h::l = [h]++l.
  Proof using.
    reflexivity.
  Qed.
  Import Instances.Lists.

  (* does it suffice to do just rewrite ->!cons_as_app? *)
          Ltac cons_as_app :=
          let rw h tl :=
            lazymatch tl with
            | []=> fail
            | _ => rewrite (cons_as_app tl h)
            end in
          repeat match goal with
          | |- context[?h::?tl] => rw h tl
          | H:context[?h::?tl] |- _ => rw h tl
            end.
Ltac rwHypsP :=
  repeat match goal with
           | [ H: ?l = ?r |- _] =>
               match r with
               | context [l] => idtac
               | _ => rewrite -> H
               end
           | [ H: ?l ≡ₚ ?r |- _] =>
               match r with
               | context [l] => idtac
               | _ => rewrite -> H
               end
    end.

        Ltac perm_solver :=
          rwHypsP; (*TODO: be more selective: chose the right direction and rewrite only if we make "progress" *)
          cons_as_app;
          aac_reflexivity.

  Ltac2 permSolveM () : message list:=
    ltac1:(perm_solver); [fprintf "perm_solver."].

  Ltac2 rec mconcat (m: message list) : message:=
    match m with
    | [] => Message.of_string ""
    | h::tl => Message.concat h (mconcat tl)
    end.

  Ltac2 solvePure (stepsAlreadyDone: message list) : message list:=
      ltac1:(simplPure); (* cannot solve the goal *)
      let acn := aac_normalise_all_shallowM () in (* cannot solve the goal *)
      let arw := aacrwMLall [constr:(Z.gcd_mod); constr:(Z.gcd_0_r_nonneg)] in (* can solve the goal. so the tacs below are wrapped in tryTac *)
      let acn2 :=
        match arw with
        | [] => []
        | _::_ =>  tryTac (aac_normalise_all_shallowM)
        end in
      let asl := tryEvalConcatMsgs [arithSolveM; permSolveM] in
      List.concat [stepsAlreadyDone; [fprintf "simplPure."]; acn; arw; acn2; asl].

  (* this is the ; in the [message list] monad*)
  Ltac2 rec evalConcatMsgs (tacs: ( unit -> message list) list) : message list :=
    match tacs with
    | [] => []
    | h::tl =>
        let msgs := h () in
        List.append msgs (evalConcatMsgs tl)
    end.

  (* this is the ; in the [message list] monad*)
  Ltac2 rec evalConcatMsgs2 (tacs: ( unit -> message list) list) : message list :=
    match tacs with
    | [] => []
    | h::tl =>
        match Control.case (fun _ => Control.plus h (fun _ => [])) with
        | Err _ =>  [] (* it seems this case is not hit even if h throws *)
        | Val (msgs, _) =>
            List.append msgs (evalConcatMsgs tl)
        end
    end.

  Ltac2 constr_to_str (c: constr) : string :=
    Message.to_string (Message.of_constr c).

  Ltac2 pp_ident_clean (i: ident) : string :=
    let m:= Message.to_string  (pp_ident () i) in
    if Int.equal (Char.to_int (String.get m 0)) 95 then "_" else m.


  Ltac2 pp_hyp_clean hyp : message :=
    let (id, mdef, ty) := hyp in
    match mdef with
    | None => (Message.of_string (String.concat "" [pp_ident_clean id;" : "; constr_to_str ty]))
    | Some def => fprintf "%a : %t := %t" pp_ident id ty def
    end.

  Ltac2 rec printCoqHypsMr (hyps: (ident * constr option * constr) list) : message list:=
    match hyps with
    | h::hyps =>
        let (_,_,ht) := h in
        lazy_match! ht with
        | gFunctors => printCoqHypsMr hyps
        | genv => printCoqHypsMr hyps
        | _ ⊧ _ => printCoqHypsMr hyps
        | biIndex => printCoqHypsMr hyps
        | cpp_logic _ _ => printCoqHypsMr hyps
        | guard.GWs.GUARDS => printCoqHypsMr hyps
        | _ => (pp_hyp_clean h)::(printCoqHypsMr hyps) (* skip printing autogen names, especially if they are huge, like _auto_tele_binder0 *)
        end
    | [] => []
    end.

  (* TODO: consolidate vars of the same type *)
  Ltac2 printCoqHypsM () :=
    List.append
      ((fprintf "<pure_hypotheses>")::(printCoqHypsMr (Control.hyps ())))
      [fprintf "</pure_hypotheses>"].

  Ltac2 of_string_constrd (t : constr) : string :=
    match String.of_string_constr t with
    | Some s => s
    | None => ""
    end.

  Import environments.
  Ltac2 nameOfIdent (i:  constr (* base.ident.ident *)): string :=
    lazy_match! i with
    | IAnon ?ii => Message.to_string (fprintf "s%i" (Int.of_pos ii))
    | INamed ?s => of_string_constrd s
    end.


  Ltac2 rec printIPMEnv (e: constr (* env _ *)) : message list :=
    lazy_match! e with
    | Enil => []
    | Esnoc ?e ?i ?p =>
          (Message.of_string (String.concat "" [nameOfIdent i;" : "; constr_to_str p]))::
          (printIPMEnv e)
    end.

  Ltac2  printIPMEnvs (e: constr (* envs _ *)) : message list :=
    lazy_match! e with
    | Envs ?penv ?senv _ =>
        List.append
          (List.append [fprintf "<spatial_hypotheses>"] (printIPMEnv penv))
          (List.append (printIPMEnv senv) [fprintf "</spatial_hypotheses>"])
    end.


  Ltac2 newline () : message :=  Message.of_string (String.newline ()).
  Axiom Stmt_printer : nat -> Stmt -> string. (* TODO: reimplement *)
  Ltac2 printSpConclM (c: constr) : message :=
    lazy_match! c with
    | wp _ _ ?stmt ?spec => (* rename spec to postcond *)
        let pps := (Std.eval_cbv Std.red_flags_all constr:(Stmt_printer 2 $stmt)) in
        mconcat
          [fprintf "weakest_pre"; newline ();
         Message.of_string (of_string_constrd pps);
         (fprintf "%t" spec)
           ]

    | _ => fprintf "%t" c
    end.


  Ltac2 printConclM () : message list :=
   lazy_match! goal with
     [ |- environments.envs_entails ?e ?c] =>
       List.append
         (printIPMEnvs e)
         [fprintf "<spatial_goal>"; printSpConclM c; fprintf "</spatial_goal>"]
    | [ |- ?p] =>
         [fprintf "<pure_goal>"; fprintf "%t" p; fprintf "</pure_goal>"]
    end.

  Ltac2 printGoalM ():=
    List.append
      ((fprintf "(* Current goal state:")::printCoqHypsM ())
      (List.append (printConclM ()) [fprintf "*)"]).

Ltac2 slauto2 () : message list :=
      ltac1:(slauto); [fprintf "slauto."].

(*
Ltac2 slauto2 () : message list :=
  lazy_match! goal with
  | [|- environments.envs_entails _ _] =>
      ltac1:(slauto); [fprintf "slauto."]
  | [|- _] =>
      []
  end.
*)

  Ltac2 Type result :=
  [
  | GoalSplit(int* (message list)) (* int is the number of new subgoals created by the new split. we dont exit to emacs in this case. we start solving subgoals one by one. no coq sentence should be emitted after the one that splits the goal. however, in the sentence you split the goal, you can add a ; to do more stuff, e.g. destruct t;[assert (foo=bar) by auto | assert (foo<>bar) by auto]. *)
  | Backtrack(string * string) (* request for emacs to backtrack and reset the proof script to the first argument.
 possible backtracking steps in the proof script are indicated as (* __BACKTRACKING_POINT__ id *). typically the producer of this value will delete the proof script to one of those points.  ltac cannot get to the goal at that point. so emacs will help. emacs will revert to the beginning of the proof, which emacs will from when the first keybinding to start the proof was invoked. after reverting to the beginning, insert the proofscript given as the firrst argument and check until that point, which must succeed (obligation of the Ltac2 producer of this value). then emacs will invoke the continuation specified in the second argument. the second argument is a string representing an Ltac2 tactic "continuation" that emacs should execute last executing the sentences. this string should include almost all the arguments to the tactic. The last argument will be added by emacs, which will exactly the virst argument of this constructor: ltac2 cannot store state across calls. This clause is currently not supported in the emacs driver *)
  | AbortIfCurgoalUnifinished(message list) (* even in the case the goal is unfinished, to give the human feedback about what didnt work, the tried proofscript will be printed. will exit to emacs if the caller determines that the goal was indeed not finished. as there is no continuation, the emacs driver will also exit *)
  | GoalFinished(message list) (*
the arg denotes the proof steps done to finish the finished goal.
this case can be used in case the core tactic is sure that it finished its goal, e.g. lia succeeded or it did admit. we only exit to emacs in this case if this was the last remaining goal. as there is no continuation in this case, the emacs driver will also exit*)
  | Interact(string*string*string) (* this case when what is needed cannot be done in ltac2, e.g. declaring new lemmas/tactics or interpreting arbitrary tactics produced by GPT. the first argument is the current proof script. the second arg is string containing A single Coq sentence that should be executed by the external driver (e.g. e-lisp). E.g. it could be "wp_while (fun _ => "++ loopinvstring "++)".  Assume Set Nested Goals Allowed, so this could even be a definition of a helper ltac. the last argument is a string representing an Ltac2 tactic "continuation" that emacs should execute last executing the sentences. this string should include almost all the arguments to the tactic. howver, the driver will automatically 3 arguments, all of type string
1) this autoadded argument will exactly the first argument of this constructor: ltac2 cannot store state across calls.
2) this autoadded argument will exactly the second argument of this constructor.
3) this is the error in executing the sentence in the second argument of this constructor. if no error, empty. This could help in the usecase of GPT fixing type errors in the loop invariant.
Currently, the emacs driver assumes that the second argument of Interact is empty. and only adds the first argument.
 *)
  ].

  Ltac2 doWpIfPostLoopInv h (proofscript: message list): result :=
    ltac1:(hyp |- Hide.show_hyp hyp; subst; slauto; wp_if) (Ltac1.of_ident h);
    GoalSplit (2, List.append proofscript [
           fprintf "(* done proving that the loop invariant holds at the beginning of the loop *)"; (* nop but document the proof script for GPT *)
          fprintf "Hide.show_hyp %I; subst; slauto ; wp_if." h;
           fprintf "(* the first goal asks you to prove that the loop invariant is preserved if the loop condition is true and thus the loop does another iteration. the second subgoal lets you assume the loop invariant and that the loop condition is false and asks you to prove the postcondition (if the function ends after the loop) or wp (restOfFunction) postcondition *)" (* TODO: split and move this comment to later when the respective subgoals are opened uwing { *)
         ])
  .

  Ltac2 indentPerTreeDepth () : message := Message.of_string ("  ").

  (* indentPerTreeDepth * depth of tree *)
  Ltac2 rec indent (branchid: (int * int) list) : message :=
    match branchid with
    | _::tl => Message.concat (indentPerTreeDepth ()) (indent tl)
    | []=> Message.of_string ""
    end.

  Ltac2 indentS (branchid: (int * int) list) (str: string): string :=
      (String.app (Message.to_string (indent branchid)) (String.app str (String.newline ()))).

  Ltac2 backtrackingPointComment branchid backtrackingNum : string :=
    String.app (String.newline ())
      (String.app
         (indentS branchid (Message.to_string (fprintf "(* __BACKTRACKING_POINT__ %i *)" backtrackingNum)))
         (String.newline ())).

  Ltac2 rec msg_of_branchid (branchid: (int * int) list) : message :=
    match branchid with
    | [] => Message.of_string("[]")
    |(cur,max)::tl => Message.concat (fprintf "(%i,%i)::" cur max) (msg_of_branchid tl)
    end.

  Ltac2  string_of_branchid (branchid: (int * int) list) : string :=
    Message.to_string (msg_of_branchid branchid).

  Ltac2 printCont contTactic llmResp emacsExitCount branchid backtrackingNum : string :=
    Message.to_string
      (fprintf "%s constr:(%s) %i %s %i"
         contTactic
         llmResp
         emacsExitCount
         (Message.to_string (msg_of_branchid branchid))
         (Int.add backtrackingNum 1)).

  Ltac2 rec concatProofScriptSentences (indent: message) (l: message list) : message :=
    match l with
    | [] => newline ()
    | h::tl =>
        match tl with
        | [] => (Message.concat indent h)
        | _::_ => Message.concat (Message.concat indent h) (Message.concat (newline ()) (concatProofScriptSentences indent tl))
        end
    end.

  Ltac2 goalAsStr () : string :=
    Message.to_string (concatProofScriptSentences (indent []) (printGoalM ())).

  Ltac2 commonPrompt currentProofScript : string :=
    String.concat (String.newline ())
      [main.main ();
       "```coq";
       currentProofScript;
       "```";
       "The proof state at the end of the partial proof script is:";
       "```coq";
       goalAsStr ();
       "```"].

  Ltac2 fullLoopInvPrompt currentProofScript : string :=
    String.concat (String.newline ())
      [ commonPrompt currentProofScript;
        loopInvPrompt ()].

  (* https://chatgpt.com/share/69ac250c-094f-4e2b-b3f0-9415ec095b6e *)
Ltac2 rec check_from (searchFor: string) (str: string) (i: int) : bool :=
  let search_len := String.length searchFor in
  let rec aux j :=
    if Int.ge j search_len then true
    else if Char.equal (String.get str (Int.add i j)) (String.get searchFor j) then aux (Int.add j 1)
    else false
  in aux 0.

Ltac2 rec firstOccurrenceOf (searchFor: string) (str: string) (startIndex: int) : int option :=
  let search_len := String.length searchFor in
  let str_len := String.length str in
  let rec aux i :=
    if Int.gt i (Int.sub str_len search_len) then None
    else if check_from searchFor str i then Some i
    else aux (Int.add i 1)
  in aux startIndex.

Ltac2  lastOccurrenceOfFrom (searchFor: string) (str: string) (endIndex: int) : int option :=
  let search_len := String.length searchFor in
  let rec aux i :=
    if Int.lt i 0 then None
    else if check_from searchFor str i then Some i
    else aux (Int.sub i 1)
  in aux endIndex.

Ltac2 rec lastOccurrenceOf (searchFor: string) (str: string) : int option :=
  lastOccurrenceOfFrom searchFor str (Int.sub (String.length str) 1).

(* TODO: the prompt now asks the loop invariant to be the last ```coq ``` block, after GPT has done informal reasoning, possibly including ```coq blocks```. this likely improves the response quality (chain of thought principles). this code needs to be adapted accordingly *)
Ltac2 extractLastCoqCodeBlockFromResp (resp: string): string option :=
  match lastOccurrenceOf "```coq" resp with
  | None => None
  | Some start =>
      match firstOccurrenceOf "```" resp (Int.add 1 start) with
      | None => None
      | Some endi => Some (String.sub resp (Int.add 6 start) (Int.sub endi ((Int.add 6 start))))
      end
  end.

Ltac2 extractLoopInvFromResp := extractLastCoqCodeBlockFromResp.

Ltac2 promptGptForLoopinv currentProofScript : string :=
  let prompt:= fullLoopInvPrompt currentProofScript in
  printf "lprompt: %s" prompt;
  let response := LLM.query_gpt prompt in
  printf "lprompt_response: %s" response;
  match extractLoopInvFromResp response with
  | Some s => s
  | None => "" (*FIX: prompt GPT again, include old response and ask to fix formatting *)
  end.
(* "(Exists a' : Z, Exists b' : Z,
 [| 0 <= a' <= 2 ^ 32 - 1 |] ** [| 0 <= b' <= 2 ^ 32 - 1 |] **
 a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
 b_addr |-> primR Tu32 (cQp.mut 1) (Vint b') **
 [| Z.gcd a' b' = Z.gcd a b |])
".*)

  Ltac2 extendProofScript (currentProofScript: string) (branchid: (int * int) list (* to determine indent *))
    (msgs: message list) :=
    String.app
      currentProofScript
      (String.app (Message.to_string (concatProofScriptSentences (indent branchid) msgs)) (String.newline ())).


  Ltac verify_spec1 :=
    iApply (verify_spec_new false false false module with ""%string);
      [vm_compute; reflexivity|].

  Axiom printName: name -> bs.
  Import String.
  Definition unmangled_function_name (s: sym_info) : String.string :=
    let full_unmangled := BS.to_string (printName (info_name s)) in
    let argStart := String.findex 0 "(" full_unmangled in
    String.substring 0 argStart full_unmangled.

  Axiom Func_printer: nat -> sym_info -> Func -> String.string.
  Import String.
  Open Scope string_scope.
  Locate string.
  Definition pprint (s: sym_info) (c: genv_tu.CodeType) : String.string :=
    match c with
    | genv_tu.CTfunction f =>
        "C++ function: " ++ print.newline++ print.newline++ Func_printer 0 s f++ print.newline
    | _ => "pprint is currently only implemented for functions"
    end.


  Ltac2 proofStartComment (pprinted: constr) : message :=
    fprintf "(*%sThis is a correctness proof of the following %s %s*)%s"
       (String.newline()) (of_string_constrd pprinted) (String.newline()) (String.newline()).

  Ltac clearPost :=
    repeat match goal with
    | H: mpred |- _ => try clear H
    | H : ptr-> mpred |- _ => try clear H
    end.


  Lemma uncurry_post_wand (P:mpred) (Qs Q: ptr -> mpred):
    (P -* Forall x, (Qs x-* Q x))
      |-- (Forall x, ((P ** Qs x)-* Q x)).
  Proof. Admitted.
  Ltac verify_spec2 :=
    work; (* NOT go as that puts Seq into the continuation as Kseq, making the next rewrite fail *)
    try rewrite uncurry_post_wand; (* TODO: make it work only the hyp of the form -* POST v *)
    rewrite <- wpl;
    eagerUnifyU; (* this does not suffice: see split_spec proof. need to do evar tricks to infer Qs *)
    work;
    name_locals;
    cpp.hints.type.has_type_prop_prep;
    try clearPost.


  Ltac begin_function_correctness_proof :=
    iIntrosDestructs;
    verify_spec1;
    verify_spec2;
    name_locals;
    cpp.hints.type.has_type_prop_prep.

  Ltac2 verify_spec_llm () : message list :=
    ltac1:(iIntrosDestructs);
    match! goal with
      [|- environments.envs_entails _ ?spec] =>
        ltac1:(h|-unfold h) (Ltac1.of_constr spec);
        match! goal with
          [|- environments.envs_entails _ (specify ?sym _)] =>
            ltac1:(verify_spec1);
            match! goal with
              [|- context[genv_tu.wp_code_type _ _ _ ?ct]] =>
                ltac1:(verify_spec2);
                List.append
                  [proofStartComment (Std.eval_cbv Std.red_flags_all constr:(pprint $sym $ct))
                   ; fprintf "begin_function_correctness_proof."
                   ; fprintf "(* Instead of looking at the definition of %t (RHS of `|--`), you can look at the following proof state, which is the current proof state obtained after unfolding %t and doing minor simplifications. The pure hypotheses are the variables universally quantified in the spec. The spatial hypotheses are the preconditions. The last argument to `::wpS` is the postcondition. *)" spec spec
                  ]
                  (printGoalM ())
            end
        end
    end.


  (* proofScriptPostEntry accumulates proof script after entry. it will be a suffix of proofScriptAtEntry in the actual current proof script, which is only needed for preparing the prompt for GPT *)
  Ltac2 rec god  (proofScriptAtEntry: string) (emacsExitCount: int)  (branchid: (int * int) list) (backtrackingNum: int) (proofScriptPostEntry: message list) : result :=
    printf "running god on goal %t" (Control.goal ());
    let msgs1 := tryEvalConcatMsgs [verify_spec_llm;slauto2] in (* can fail if the goal is not IPM after intros *)
    (* TODO: do maximalObserve here just like  destructSomeVar and prepend its results to msg2*)
    let msgsD :=  tryTac destructSomeVar in
    let allMsgs := List.concat [proofScriptPostEntry;msgs1;msgsD] in
    if goalDoneB () then GoalFinished allMsgs else
    match msgsD with
    | _::_ => god proofScriptAtEntry emacsExitCount branchid backtrackingNum allMsgs (* tryDestruct did something so rerun automation *)
    | [] =>
        lazy_match! goal with
        | [h:Hide.Hidden (?v=gather_all.Spatial.gather) |- environments.envs_entails _ ?v] => (* done proving loopinv holds initially *)
            doWpIfPostLoopInv h allMsgs
        | [|- environments.envs_entails _ ( wp _ _ (Swhile _ ?cond ?body) _)] =>
            let newProofScript := (extendProofScript proofScriptAtEntry branchid allMsgs) in
            let loopInv:= promptGptForLoopinv newProofScript in
            let newProofScriptB := String.app newProofScript (backtrackingPointComment branchid backtrackingNum) in
            Interact (newProofScriptB, "",
                printCont
                  "continueWithWhileLoopinv" loopInv (Int.add 1 emacsExitCount) branchid backtrackingNum)
     (* TODO: add a case for branches.stmt *)
     (* TODO: existential  *)
        | [|- environments.envs_entails _ [| _ |] ] =>
            ltac1:(iPureIntro); (* we should do maximal observation before this to make it safer *)
            god proofScriptAtEntry emacsExitCount branchid backtrackingNum (List.append allMsgs [fprintf "iPureIntro."])
        | [|- environments.envs_entails _ _] => AbortIfCurgoalUnifinished allMsgs
        | [|- _] => AbortIfCurgoalUnifinished (solvePure allMsgs)
        end
    end.

  Ltac2 msg_of_branchid_commented (branchid: (int * int) list) : message :=
    Message.concat (Message.of_string("(*")) (Message.concat (msg_of_branchid branchid) (Message.of_string("*)"))).

(* ensure that the callers catch exceptions. with Control.focus (in the body), behaviour can be wierd if you let exceptions bubble all the way up. it seems previously sucessfully executed things can be reevaluated to fail *)
(* outpit: Some 0 means current goal done, Some n means goal was split into n subgoals. None otherwise *)
  Ltac2 goalDone (splitg: int option) : int option  :=
    match splitg with
    | Some n => Some n
    | None =>
        Control.plus (fun _ => Control.focus 1 1 (fun _ => None)) (fun _ => Some 0)
    end.

  Ltac2 rec nextBranchM (msgs: message list) (branchid: (int * int) list): ((int * int) list) * (message list) :=
    match branchid with
    | [] => ([], msgs)
    | (cur, max)::tl =>
        let msgb:= Message.concat (indent tl) (Message.of_string ("}")) in
        let cuplus1 := Int.add cur 1 in
        if Int.equal cuplus1 max
        then
          nextBranchM (List.append msgs [msgb]) tl
        else
          ((cuplus1,max)::tl, (List.append msgs [msgb]))
    end.

  Ltac2 goalDoneM (res: result) : result  :=
    match res with
    | AbortIfCurgoalUnifinished msgs =>
        Control.plus
          (fun _ => Control.focus 1 1 (fun _ => res))
          (fun _ => GoalFinished (msgs))
    | _ => res
    end.

  Ltac2 slautobigOnFstGoal  (proofScriptAtEntry: string) (emacsExitCount: int)  (branchid: (int * int) list) (backtrackingNum: int) : result :=
    Control.focus 1 1 (fun _ => let splitg := god proofScriptAtEntry emacsExitCount branchid backtrackingNum [] in goalDoneM splitg).

  (* outout: Some(newbr,m) iff we need to now focus on a new branch, possibly a child of the current one.
     m is the closing braces to be put in the proof script *)
  Ltac2 newBranch (branchid: (int * int) list) (res: result) : (((int * int) list) * (message list)) option :=
    match res with
    | GoalFinished msgs =>
        printf "goal done in stepDoneM";
        Some (nextBranchM [] branchid)
    | GoalSplit (numSubgoals, msgs) =>
        Some ((0,numSubgoals)::branchid, [])
    | _ => None
    end.

  Ltac2 snd (p:'a * 'b) : 'b := let (_,y) := p in y.

  Ltac2 promptGptForExistInstantiation proofScriptAtEntry := "1".


    (* hide  gather_all.Spatial.gather to mark in proofscript where the proof that loopinv holds initiall is done *)
  Ltac hideGather :=
     IPM.perm_right ltac:(fun R _ =>
                               let hg := fresh "loopInvPreservationAndExitObligations" in
                             match R with
                          | gather_all.Spatial.gather => hideFromWorkAs R hg
                             end
                         ).

  Ltac2 snewlines () : string :=  String.app "." (String.newline ()).


  Ltac2 string_of_int (i:int):= Message.to_string (fprintf "%i" i).


  Ltac2 newBranchProofScript proofScriptAtEntry branchid newbranchid (proofscript: message list)(closingBraces: message list): string :=
    let ps :=
      String.app
          (extendProofScript proofScriptAtEntry branchid proofscript)
          (extendProofScript "" [] closingBraces) (* already indented *) in

    match newbranchid with
    | [] => ps
    | _::_ =>
        String.app
          ps
          (indentS branchid (String.app
                               (String.app (String.newline ())"{ (*")
                               (String.app (string_of_branchid newbranchid) "*)")))
    end.

  (* this is similar to the [result] type but excludes the cases that are handled internally in Ltac2 and the disctinctions needed for that. this type is simplified to only capture what matters to emacs *)
  Ltac2 Type EmacsRequest :=
  [
  | EBacktrack(string * string) (* see comments in the similarly name constructor in result which maps to this 1:1 . The emacs driver currently does not implement this case *)
  | NoBacktrack (string (* proofscript*)
                 * string (* a SINGLE vernacular command to execute. for more details, see the comments for the Interact constructor for result *)
                 * string) (* continuation *)
  ].
  Ltac2 printProofscript (proofscript: string) :=
    printf "<PROOFSTEPS>";
    printf "%s" proofscript;
    printf "</PROOFSTEPS>".

  Ltac2 printConti (cont: string) :=
    printf "<CONTINUATION>";
    printf "%s" cont;
    printf "</CONTINUATION>".

  Ltac2 printEmacsRequest (e: EmacsRequest) :=
    match e with
    | EBacktrack (proofscript, cont) =>
        printf "<BACKTRACK>";
        printProofscript proofscript;
        printConti cont;
        printf "</BACKTRACK>"
    | NoBacktrack (proofscript, exec, cont) =>
        printf "<NOBACKTRACK>";
        printProofscript proofscript;
        printf "<EXECUTECOMMANDS>";
        printf "%s" exec;
        printf "</EXECUTECOMMANDS>";
        printConti cont;
        printf "</NOBACKTRACK>"
    end.



   (* TODO: print the goal at some places *)
  Ltac2 rec stepUntilEmacsInteractionNeeded (safeSaturated: bool) (proofScriptAtEntry: string) (emacsExitCount: int)  (branchid: (int * int) list) (backtrackingNum: int) : EmacsRequest :=
    let res := slautobigOnFstGoal proofScriptAtEntry emacsExitCount branchid backtrackingNum in
    match res with
    | GoalFinished proofscript =>
        let (newbranchid, closingBraces) := nextBranchM [] branchid in
        let newProofScript := newBranchProofScript proofScriptAtEntry branchid newbranchid proofscript closingBraces in
        match newbranchid with
        | _::_=> stepUntilEmacsInteractionNeeded false newProofScript emacsExitCount newbranchid backtrackingNum
        | [] => NoBacktrack (String.concat (String.newline ()) [newProofScript; "Qed."] , "", "")
        end

    | GoalSplit (numSubgoals, proofscript) =>
        let newbranchid:=((0,numSubgoals)::branchid) in
        let newProofScript := newBranchProofScript proofScriptAtEntry branchid newbranchid proofscript [] in
        stepUntilEmacsInteractionNeeded false newProofScript emacsExitCount newbranchid backtrackingNum
    | Interact (proofscript, commands, cont) =>
        NoBacktrack (proofscript , commands, cont)

    | AbortIfCurgoalUnifinished proofscript =>
        NoBacktrack ((extendProofScript proofScriptAtEntry branchid proofscript) , "", "")
    | Backtrack foo => EBacktrack foo
    end.


  Ltac2  stepUntilEmacsInteract (safeSaturated: bool) (proofScriptAtEntry: string) (emacsExitCount: int)  (branchid: (int * int) list) (backtrackingNum: int) : unit :=
    let er := stepUntilEmacsInteractionNeeded safeSaturated proofScriptAtEntry emacsExitCount branchid backtrackingNum in
    printEmacsRequest er.

  Ltac2 continueWithExistInst exitCnt inst proofScriptAtEntry branchid backtrackingNum :=
    ltac1:(einst |- iExists einst) (Ltac1.of_constr inst);
    let pstep := indentS branchid (Message.to_string (fprintf "iExists %t." inst)) in
    stepUntilEmacsInteract false (String.app proofScriptAtEntry pstep) exitCnt branchid backtrackingNum.


  Ltac2 continueWithWhileLoopinv loopinv emacsExitCount branchid backtrackingNum proofScriptAtEntry:=
    ltac1:(loopinv |- wp_while (fun _ => loopinv); hideGather) (Ltac1.of_constr loopinv);
    let pstep := indentS branchid (Message.to_string (fprintf "(wp_while  (fun _ => %t)); hideGather." loopinv)) in (* TODO: this may not properly indent the loopinv *)
    stepUntilEmacsInteract false (String.app proofScriptAtEntry pstep) emacsExitCount branchid backtrackingNum.




  (* when is a term x simpler than y: cases after x and y are aac_normalised :
     - x and y are definitionally equal
     - x is a subterm of y. "is" is upto definitional equality
     - x is definitionally equal to f (u, v) and y is definitionally equal to f (c, d)
          u is simpler than c and d is simpler than v.
     - x is a closed term in strong normal form
   *)

Set Default Proof Mode "Classic".

Open Scope Z_scope. (* the loopinv produced by GPT need this *)


    Disable Notation "x ∗ y" := (bi_sep x y).
    Disable Notation "λ".
    Disable Notation "∃" (all).
    Disable Notation "∀" (all).
    Disable Notation "→" (all).
    Disable Notation "ptrR<" .
    Disable Notation "refR<" .
    Disable Notation "∧"  (all).
    Disable Notation u32R.
    Disable Notation u8R.
    Disable Notation u16R.
    Disable Notation u64R.
    Disable Notation boolR.
    Disable Notation "⊢"(all).

    (*

    Lemma proof: denoteModule module |-- gcd_spec.
Proof.

(*
This is a correctness proof of the following C++ function:

unsigned int gcd(unsigned int a, unsigned int b)
  {
    while ((b) != (0))
      {
        unsigned int temp = (b);
        b = (a) % (b);
        a = (temp);
      }
    return (a);
  }

*)

begin_function_correctness_proof.
(* Instead of looking at the definition of gcd_spec (RHS of `|--`), you can look at the following proof state, which is the current proof state obtained after unfolding gcd_spec and doing minor simplifications. The pure hypotheses are the variables universally quantified in the spec. The spatial hypotheses are the preconditions. The last argument to `::wpS` is the postcondition. *)
(* Current goal state:
<pure_hypotheses>
a_addr : ptr
b_addr : ptr
a : Z
b : Z
_ : (0 ≤ a ≤ 2 ^ 32 - 1)
_ : (0 ≤ b ≤ 2 ^ 32 - 1)
</pure_hypotheses>
<spatial_hypotheses>
s1 : (type_ptr Tu32 b_addr)
s2 : (type_ptr Tu32 a_addr)
s3 : (denoteModule module)
s4 : (b_addr |-> primR Tu32 (cQp.mut 1) (Vint b))
s5 : (a_addr |-> primR Tu32 (cQp.mut 1) (Vint a))
</spatial_hypotheses>
<spatial_goal>
weakest_pre
  {
    while ((b) != (0))
      {
        unsigned int temp = (b);
        b = (a) % (b);
        a = (temp);
      }
    return (a);
  }
(Kreturn
   (fun v : ptr =>
    (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
    (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0) ** v |-> primR Tu32 (cQp.mut 1) (Vint (Z.gcd a b))))
</spatial_goal>
*)
slauto.

(* __BACKTRACKING_POINT__ 0 *)


(wp_while  (fun _ => (Exists a' b' : Z,
                      [| 0 ≤ a' ≤ 2 ^ 32 - 1 |] **
                      [| 0 ≤ b' ≤ 2 ^ 32 - 1 |] **
                      a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
                      b_addr |-> primR Tu32 (cQp.mut 1) (Vint b') ** [| Z.gcd a' b' = Z.gcd a b |]))); hideGather.
slauto.
(* done proving that the loop invariant holds at the beginning of the loop *)
Hide.show_hyp loopInvPreservationAndExitObligationseq; subst; slauto ; wp_if.
(* the first goal asks you to prove that the loop invariant is preserved if the loop condition is true and thus the loop does another iteration. the second subgoal lets you assume the loop invariant and that the loop condition is false and asks you to prove the postcondition (if the function ends after the loop) or wp (restOfFunction) postcondition *)



{ (*(0,2)::[]*)
  slauto.
  iPureIntro.
  simplPure.
  aac_normalise in H.
  aac_rewrite Z.gcd_mod; try Arith.arith_solve.
  aac_normalise.
  Arith.arith_solve.
}

{ (*(1,2)::[]*)
  slauto.
  iPureIntro.
  simplPure.
  aac_normalise in H.
  aac_rewrite Z.gcd_0_r_nonneg in H; try Arith.arith_solve.
}

Qed.



(* TODON:
1) DONE: insert goalDoneB/goalNotDone at more places as necesssary to rule out Not_focussed or No such goal exceptions
2) DONE: make the aac_rw db rewrite in hyps too. then test that countiuneWithWhileLoopinv solves entire goal
3) BLOCKED: remove Z.gcd_mod from the aac_rw db and check that nextStep is able to continue from first branch
4) DONE: write the emacs part
5) DONE: implement GPT ltac2 plugin
6) polish prompts
   - DONE verify_spec'' should pretty print the whole function and should (before the verify_spec'' line) look almost like the C++ function defn. after the verify_spec'' line, in comments, it shold print the goal and explain what is the postcondition and what is the precondition (context)
   - DONE printGoal () should
     - hide the AST in wp/wpe... and instead show the pretty printing
     - not print junk hyps: valid/ptr, type/ptr..
   - DONE  slauto should do name_locals as the first step
   - DONE implement the above tactics/tweaks but dont plug to main automation
   - DONE test the resultant proof script in a prompt and see if GPT can produce the loopinv
   - DONE plug those into main automation, which currently is missing init steps like verify_spec
   - run1 to document what is going on in the proof script (pretty printed code args of wp/wpe)

7) parse LLM output in ltac2
   - DONE ask GPT to start the ```coq ``` block that has the loop invariant with a specific marker comment
   - DONE now, GPT is asked to put the loopinv in the last block (see comment above about why). parsing needs to be updated
8) implement backtracking
   - separate prompt to ask where to back track or make it part of every prompt to ask whether GPT thinks the goal is unprovable and if so where to backtrack to and a summary of what went wrong in the backtracked part
9) implement auto adding of missing existential quantifiers as a Ltac2 constr->constr function. for large loopinvs like in the case split, GPT very often makes this kind of mistakes.
10) implement the exec/error feature of Interact
11) when backtracking keep a list previous loop invariants in the proof script, e.g. as string list parseable as Ltac2. ask GPT to retry immeditely if the equivalence prover can prove the new one equivalent to something that didnt work
*)

  (* https://chat.openai.com/share/5663d15c-dfba-4e43-bb65-a8a746f621d3
main strategies:
1) algorithmically solve as much as possible. only invoke LLMs when the set of distinct possible next steps is huge
2) put yourself in a teacher's shoe and try to understand what information chatgpt is missing so that it can have the right intuitions to solve the problem. Clear and unambigous tutorial. Ambiguous terms/notations in => ambigous terms out.
3) interpret chatgpts answers more liberally

   *)

(* other LLMs:
Google Gemini (wrong answer):

Exists b_new a_new,
  (* b_new and a_new are the new values of b and a after some loop iterations *)
  ([| 0 <= b_new <= 2^32 - 1%Z |] **  (* b_new is non-negative and less than 2^32 *)
   [| a_new <= a %Z |] **         (* a_new is less than or equal to a mod b *)
   b_addr |-> u32R (cQp.mut 1) b_new **  (* b points to b_new *)
   a_addr |-> u32R (cQp.mut 1) a)       (* a points to a_new *)


Gemini Advanced:

(Exists a' b' : Z,
  [| 0 <= b' <= a' < 2 ^ 32 |] **
  a_addr |-> u32R (cQp.mut 1) a' **
  b_addr |-> u32R (cQp.mut 1) b' **
  [| Z.gcd a b = Z.gcd a' b' |])


Anthropic Claude (correct, syntactically equal to ChatGPT's annswer):
Exists a' b' : Z,
  [| 0 <= a' <= 2^32 - 1 /\ 0 <= b' <= 2^32 - 1 |] **
  a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
  b_addr |-> primR Tu32 (cQp.mut 1) (Vint b') **
  [| Z.gcd a' b' = Z.gcd a b |]

Cohere CommandR (wrongest answer)
Exists a' b', [| a = a' /\ b = b' |] ** a_addr |-> u32R (cQp.mut 1) a' ** b_addr |-> u32R (cQp.mut 1) b'

*)

  Definition PointR (q: Qp) (x y: Z): Rep :=
    _field `::Point::x` |-> primR Ti32 (cQp.mut q) (Vint x)
      ** _field `::Point::y` |-> primR Ti32 (cQp.mut q) (Vint y).

    Ltac printPost :=
      match goal with
        |- context [Kreturn ?foo] =>
          let t:= constr:(Kreturn foo) in idtac t
      end.
    (* TODO: generate automatically *)
  #[global] Instance ListR_learnable (p : ptr) q1 q2 m1 m2 :
    Learnable (p |-> ListR q1 m1) (p |-> ListR q2 m2) [m1 = m2].
  Proof. solve_learnable. Qed.


  Hint Opaque NodeR ListR: br_opacity.
  Ltac unfoldSomething :=
    IPM.perm_left ltac:(fun L n=>
      match L with
      | ?f _ _ _ => unfold f in *
      | ?f _ _ => unfold f in *
      | _ |-> ?f _ _ _ => unfold f in *
      | _ |-> ?f _ _ => unfold f in *
      end).


  Ltac proveFalse slauto :=
    let n := fresh "pfalse" in
    hideRhsAs n;
    repeat (autounfold with transparent; simpl in * );
        slauto; unhideAllFromWork.


(** automation should to destruct values of these types, at least when that results in 1 or fewer cases *)
Ltac destructible_type T :=
  lazymatch T with
  | list _ => idtac
  end.


  Import Ltac1.
  Example xx (l: list nat): False.
  Proof using.
    Fail destructSomeVar ().
  Abort.

          Ltac headIsConstructor r :=
            lazymatch r with
            | ?c _=> headIsConstructor c
            | ?c => is_constructor c
            end.

   Ltac maximalSafeSteps:= ltac2:(god "" 0 [] 0 []).


   Import wp_path.WpPrimRSep.
   #[global] Instance autogen_this_nonsense:  Typed3 ``::Node`` NodeR.
   Proof using.
     rewrite NodeR.unlock; apply _.
   Qed.

   Hint Opaque ListR: br_opacity.

       (* TODO: state as -|- once the missing proper instances are added *)
    Lemma simplPost1 m r (foo: Kpred) :
      Kseq (wp_block m r []) foo = foo.
    Proof. Admitted.

    Lemma simplPost2 m (Q: ptr-> mpred) addr:
      Kfree m (1 >*> FreeTemps.delete Tbool addr) (Kreturn Q) =
        Kreturn (fun ret => Q ret ** Exists v:val, addr |-> primR Tbool (cQp.mut 1) v).
    Proof. Admitted.

    Hint Rewrite simplPost1 simplPost2: syntactic.
    #[local] Hint Resolve Permutation_refl : pure.
    Hint Resolve fractional.UNSAFE_read_prim_cancel: br_opacity.
    Hint Opaque NodeR: br_opacity.

Ltac useLoopInv foo := wp_while (fun _ => foo).

Disable Notation "≡ₚ".

   Set Nested Proofs Allowed.
   Lemma listRw {T:Type} (P: (list T) -> mpred):
     (P [] \\// Exists h tl, P (h::tl)) |--  Exists la, P la.
   Proof using. Admitted.
   Lemma ElimRSafely (L R: mpred):
     (R |-- [| False |]) (* this is necessary ONLY for safety: the lemma is provable without it *)
     -> L |-- (L \\// R).
   Proof using. go. iLeft. go. Qed.

   Lemma ElimLSafely (L R: mpred):
     (L |-- [| False |]) (* this is necessary ONLY for safety: the lemma is provable without it *)
     -> R |-- (L \\// R).
   Proof using. go. iRight. go. Qed.

   Ltac learnListCase :=
     rewrite <- listRw; simpl;
     progress (
         tryif (rewrite <- ElimRSafely;[|slauto; fail])
         then idtac
         else (rewrite <- ElimLSafely;[|slauto; fail])
       ).

(* this proof may take 20 minutes to execute. [slauto] and [destructSomeVar], which are invoked by god () (maximalSafeSteps) could be optimized for performance. also, need to add learnListCase to god () *)
Lemma split_ok: denoteModule module |-- split_spec.
Proof.
    begin_function_correctness_proof.
    maximalSafeSteps.

    (* loop invariant chosen by GPT on the actual prompt produced by M-x prove-fun.
  https://chatgpt.com/share/eedfc206-dc13-44c1-b7a3-12dfd667e9f4
the only thing I did was Existentially one or more free variables in the loop invariant that were not available in context. This needs to be implemented in Ltac2 to get this prove-fun to fully automatically generate this proof.
 Alternatively, showing GPT the raw error from coqtop also fixes it, BUT emphasize that the goal is not just to fix the error but to also have the result be the loop invariant satisfying the desirable properties mentioned above and following its own informal reasoning. So, instead of adding missing Existentials in Ltac2, we can implement the above-documented feature of EmacsRequest where Ltac2 can ask it to execute sentence and get back the error.
     *)
   useLoopInv (Exists a_ptr_val_new : ptr, Exists b_ptr_val_new : ptr, Exists ab_ptr_val_new : ptr,
Exists la lb lr : list Z, Exists which:bool,
[| Permutation l (la ++ lb ++ lr) |] **
a_ptr_val |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr a_ptr_val_new) **
b_ptr_val |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr b_ptr_val_new) **
ab_addr |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr ab_ptr_val_new) **
a_ptr_val_new |-> ListR (cQp.mut 1) la **
b_ptr_val_new |-> ListR (cQp.mut 1) lb **
ab_ptr_val_new |-> ListR (cQp.mut 1) lr **
which_addr |->  primR Tbool (cQp.mut 1) (Vbool which)
              ).
   maximalSafeSteps.

   learnListCase. (* iExists [], chosen by GPT, first attemt *)
   learnListCase. (* iExists [] *)
   go.
   maximalSafeSteps.
    wp_if.
    { (* loop condition is true and the loop continues *)
      maximalSafeSteps.
      wp_if. (* switch on which. how do generate this or something similar automatically? can we use run1 to document what is happening in the proof script? show the pretty printed wp/wpe code arg as run1 churns through it. fortunately, in this proof GPT was only needed for the loop invariant, after learnListCase was developed.*)
      {
        maximalSafeSteps.
        learnListCase. (* iExists (z::la), chosen by GPT, first attempt *)
        maximalSafeSteps.
      }
      {
        maximalSafeSteps.
        learnListCase. (* iExists (z::lb), chosen by GPT, first attempt *)
        maximalSafeSteps.
      }
    }

    {
      maximalSafeSteps.
    }
  Qed.

(* definitions below were loop invarints produced by GPT4o.... see the comment at the loopinv above *)
Definition splitLoopInv1 (ab_addr a_ptr_val b_ptr_val which_addr: ptr) l  : mpred :=
Exists a_ptr_val_new : ptr, Exists b_ptr_val_new : ptr, Exists ab_ptr_val_new : ptr,
Exists la lb lr : list Z, Exists which:bool,
[| Permutation l (la ++ lb ++ lr) |] **
a_ptr_val |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr a_ptr_val_new) **
b_ptr_val |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr b_ptr_val_new) **
ab_addr |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr ab_ptr_val_new) **
a_ptr_val_new |-> ListR (cQp.mut 1) la **
b_ptr_val_new |-> ListR (cQp.mut 1) lb **
ab_ptr_val_new |-> ListR (cQp.mut 1) lr **
which_addr |->  primR Tbool (cQp.mut 1) (Vbool which).
Definition splitLoopInv2 (ab_addr a_ptr_val b_ptr_val which_addr: ptr) l  : mpred :=
Exists ab' a' b' : ptr,
Exists la lb : list Z, Exists which:bool, Exists l',
  ab_addr |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr ab') **
  a_ptr_val |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr a') **
  b_ptr_val |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr b') **
  which_addr |-> primR Tbool (cQp.mut 1) (Vbool which) **
  ab' |-> ListR (cQp.mut 1) l' **
  a' |-> ListR (cQp.mut 1) la **
  b' |-> ListR (cQp.mut 1) lb **
  [| Permutation l (la ++ lb ++ l') |].


Lemma equiv ab_addr a_ptr_val b_ptr_val which_addr l:
  splitLoopInv2 ab_addr a_ptr_val b_ptr_val which_addr l -|- splitLoopInv1 ab_addr a_ptr_val b_ptr_val which_addr l.
Proof using.
  unfold splitLoopInv1, splitLoopInv2.
  iSplit; go.
Qed.

(*

https://chatgpt.com/share/9e2b26b1-26bc-4edd-bbd5-60f25a1bc506
other LLMs:

Claude 3 Sonnet :

(Exists (pl pr : list Z) (abp : ptr),
   a |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr a) **
   b |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr b) **
   ab_addr |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr abp) **
   abp |-> ListR (cQp.mut 1) abp_list **
   [| Permutation l (pl ++ (rev abp_list) ++ pr) |] **
   (Exists v : val, a_addr |-> primR (Tref (Tptr (Tnamed "_Z4Node"))) (cQp.mut 1) v) **
   (Exists v : val, b_addr |-> primR (Tref (Tptr (Tnamed "_Z4Node"))) (cQp.mut 1) v) **
   (Exists v : val, which_addr |-> primR Tbool (cQp.mut 1) v)
)

Cohere Command R:

(Exists (z z' : list Z),
  a |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr a_addr) **
  b |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr b_addr) **
  ab |-> ListR (cQp.mut 1) (z ++ z') **
  [| Permutation l (z ++ z') |])


Gemini advanced:

(Exists (abv : ptr) (al alr : list Z) (bl blr : list Z),
   (ab |-> ListR (cQp.mut 1) alr) **
   (ab_addr |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr abv)) **
   (a |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr al)) **
   (b |-> primR (Tptr (Tnamed "_Z4Node")) (cQp.mut 1) (Vptr bl)) **
   [| Permutation l (al ++ alr ++ bl ++ blr) |]) **
(Exists v : val, a_addr |-> primR (Tref (Tptr (Tnamed "_Z4Node"))) (cQp.mut 1) v) **
(Exists v : val, b_addr |-> primR (Tref (Tptr (Tnamed "_Z4Node"))) (cQp.mut 1) v) **
which_addr |-> boolR (cQp.mut 1) (negb (List_is_empty alr))

*)

  (* the 1:Qp is incorrect. but this should be [inv]. we can switch to [inv] once the AUAc tactics (esp [callAtomicCommitCinv]) can deal with [inv] *)
  Definition ginv (g: gname) (P: mpred): mpred := cinvq (nroot .@@ "::RwLock") g 1 P.
  Axiom atomic_boolR: cQp.t -> bool -> Rep.

(*
Definition SpinLockR (q: cQp.t) (invName: gname) (lockProtectedResource: mpred) : Rep :=
  as_Rep (fun (this:ptr)=>
     this |-> structR ``::SpinLock`` q
       ** ginv invName (Exists locked:bool,
                           this |-> _field ``::SpinLock::locked`` |-> atomic_boolR (cQp.mut 1) locked
	                     ** if locked then lockProtectedResource else emp
	                      )).

Definition ConcListR (q: cQp.t) (invName: gname) :=
  as_Rep (fun (this:ptr)=>
     this |-> structR ``::ConcList`` q
       ** this |-> _field `::ConcList::sp`
       |->  SpinLockR q invName (
         Exists (l: list Z) (lloc: ptr),
           this |-> _field `::ConcList::list` |-> primR (Tptr (Tnamed ``::Node``)) (cQp.mut q) (Vptr lloc) **
           lloc |-> ListR q l
    )).
 *)

(* early signs that GPT4 can write Rep predicates of concurrent classes
https://chatgpt.com/share/fc310084-c595-44ac-9738-cbcb113eee5d
There are still some uncertainities.
The very crisp feedback I gave manually
to correct the initially very wrong Rep predicate would seems impossible generate automatically.
(The current Rep predicate is still not fully correct for the current implementation which was also written by GPT in another chat, but it would be correct for a slightly different implementation where the 2 atomic fields are stored in a single machine word. Also. overflow is not currently accounted, but that would requiring chaning the signature of the spec)
Can GPT correct the Rep predicate based on less crisp feedback, by learning from how the proofs of the method (lock_read()) failed, seeing the raw Coq goals rather than my summarized diagnosis?
First, improve the prompt, running through an actual proof (lock) in much more detail.

*)

(* what chatgpt wrote:
Definition ReadWriteLockR (q: cQp.t) (invName rContender: gname) (resourceProtectedByLock: Q -> mpred) : Rep :=
  as_Rep (fun (this:ptr) =>
    this |-> structR ``::ReadWriteLock`` q **
    ginv invName (
      Exists rw_count: Z,
        this |-> _field ``::ReadWriteLock::rw_count`` |-> atomic_uint64R (cQp.mut 1) (Vint rw_count) **
        own_gname rContender (Qp.of_Z (rw_count / 2)) ** (* Ensuring the count of readers *)
        if rw_count mod 2 = 0 then resourceProtectedByLock (Qp.of_Z (rw_count / 2) / 2^31)
        else emp
    )
  ).
 *)
(*
Require Import bhv.lib.lang.proof.atomic_hpp_spec.
Definition atomic_intR q i := atomicR Tu64 (Vint i) q.

Require Import QArith.
Definition mkQp (q:Q) : Qp. Admitted.
Arguments mkQp q%Q_scope.

Require Import bluerock.lib.fracQ.
  Context {frgu: frac.fracG () _Σ}.
  Definition own_gname (r: gname) (q:Q) :=
    fracQ.fgptstoQ r q ().

Definition ReadWriteLockR (q: cQp.t) (invName rContender: gname) (resourceProtectedByLock: Q -> mpred) : Rep :=
  as_Rep (fun (this:ptr) =>
    this |-> structR ``::ReadWriteLock`` q **
    ginv invName (
      Exists rw_count: Z,
        this |-> _field ``::ReadWriteLock::rw_count`` |-> atomic_intR (cQp.mut 1) rw_count **
        own_gname rContender (((rw_count / 2)) # 2^63) ** (* Ensuring the count of readers *)
        if decide (rw_count = 0)%Z then resourceProtectedByLock 1
        else if decide (rw_count mod 2 = 0)%Z then resourceProtectedByLock ((rw_count / 2) # 2^63)
        else emp
    )
  ).

  Ltac2 Eval DemangleAll.print_names 'module.

  cpp.spec "ReadWriteLock::lock_read()" as lock_read_spec with (fun (this:ptr)=>
      \prepost{q invname rcontender resourceProtectedByLock} this |-> ReadWriteLockR q invname rcontender resourceProtectedByLock
      \pre own_gname rcontender (1#2^31)%Q
      \post resourceProtectedByLock (1#2^31)%Q).

  cpp.spec "ReadWriteLock::lock_write()" as lock_write_spec with (fun (this:ptr)=>
      \prepost{q invname rcontender resourceProtectedByLock} this |-> ReadWriteLockR q invname rcontender resourceProtectedByLock
      \post resourceProtectedByLock 1%Q).

Require Import iris.bi.lib.atomic.
Import atomic_commit.

  cpp.spec "atomic<unsigned long long>::operator unsigned long long() const" as atomic_model_cpu_load_spec with
      (fun this : ptr =>
        \pre{Q : Z → mpred}
              AC1 << ∀ (x : Z) (q : cQp.t), this |-> atomic_intR q x >> @ ⊤, ∅
                 << this |-> atomic_intR q x, COMM Q x >>
                                                \post{x : Z}[Vint x] Q x).

  cpp.spec "atomic<unsigned long long>::cas(unsigned long long&, unsigned long long, bool)" as atomic_model_cpu_cas_spec with (fun this : ptr =>
        \arg{(e : Z) (Q : Z → bool → mpred) (ep : ptr)} "e" (Vptr ep)
        \arg{d : Z} "d" (Vint d)
        \arg{weak : bool} "weak" (Vbool weak)
        \pre ep |-> primR Tu64 (cQp.mut 1) (Vint e)
        \pre
              AC1 << ∀ x : Z, this |-> atomic_intR (cQp.mut 1) x  >> @ ⊤, ∅
                 << ∃ (y : Z) (b : bool), this |-> atomic_intR (cQp.mut 1) y **
                                          (if weak
                                           then if b then [| x = e |] ** [| y = d |] else [| y = x |]
                                           else
                                            [| b =
                                               (if decide (x = e)
                                                then true
                                                else false) |] ** [| y = (if b then d else x) |]),
                    COMM Q x b >>
        \post{(x : Z) (b : bool)}[Vbool b]
            Q x b ** ep |-> primR Tu64 (cQp.mut 1) (Vint x)).


  Lemma rem_later_false:  forall (P:mpred), |> P |-- P.
  Proof. Admitted.

  Ltac callAtomicCommitCinv':=
    try (iExists _; go);
    callAtomicCommitCinv;
    repeat rewrite rem_later_false.

  #[global] Instance: Cbn (ShouldInlineFunction "_ZN13ReadWriteLock22increment_writer_countEy") := {}.

  Lemma redlock_ok: denoteModule module ** atomic_model_cpu_load_spec ** atomic_model_cpu_cas_spec
                      |-- lock_write_spec.
  Proof using modd.
    Hint Opaque ReadWriteLockR ginv own_gname atomic_intR: br_opacity .
    verify_spec'.
    name_locals.
    unfold ReadWriteLockR. unfold ginv.
    slauto.
    Opaque closeR.
    callAtomicCommitCinv'.
    Opaque difference.
    ego.
    ghost.
    closeCinvqs.
    ego.
    iModIntro.
    go.
    name_locals.
    wp_do_while (fun _ => Exists rw_count, expected_rw_count_addr |-> primR Tu64 (cQp.mut 1) rw_count).
    slauto.
    callAtomicCommitCinv'.
    ego.
    ghost.
    closeCinvqs.
    ego.
    simpl.
    go.
    IPM.perm_right ltac:(fun R n => match R with
                                      context [@decide ?P ?D] =>
  match P with
  |  context[@decide _ _] => fail 1
  | _ =>

                                      let b := fresh "b" in
                                      let H := fresh "H" in
                                      Algebra.define (@decide P D) b H; destruct b; Algebra.try_decide
  end

                         end).
    {
      subst. go. iModIntro. go.
    }
    {
      go. iModIntro. go.
    }
  Qed.

    #[global] Instance: Cbn (ShouldInlineFunction "_ZN13ReadWriteLock22increment_reader_countEy") := {}.
    Lemma readlock_ok: denoteModule module ** atomic_model_cpu_load_spec ** atomic_model_cpu_cas_spec
                      |-- lock_read_spec.
  Proof using modd.
    Hint Opaque ReadWriteLockR ginv own_gname atomic_intR: br_opacity .
    verify_spec'.
    name_locals.
    unfold ReadWriteLockR. unfold ginv.
    maximalSafeSteps.
    {
    Opaque closeR.
    callAtomicCommitCinv'.
    Opaque difference.
    ego.
    ghost.
    closeCinvqs.
    ego.
    iModIntro.
    go.
    name_locals.
    wp_do_while (fun _ => Exists rw_count, expected_rw_count_addr |->  primR Tu64  (cQp.mut 1) rw_count).
    ego.
    callAtomicCommitCinv'.
    ego.
    ghost.
    closeCinvqs.
    go.
    unfold atomic_intR.
    go.
    Import fracQ.FracQ_Hints.
    IPM.perm_right ltac:(fun R n => match R with
                                      context [@decide ?P ?D] =>
  match P with
  |  context[@decide _ _] => fail 1
  | _ =>

                                      let b := fresh "b" in
                                      let H := fresh "H" in
                                      Algebra.define (@decide P D) b H; destruct b; Algebra.try_decide
  end

                         end).
Abort.

End Spec.
(* fmpython ./fm-build.py apps/vmm/proof/gcd_cpp_proof.v  0.04s user 0.01s system 0% cpu 13:14.44 total *)
Require apps.vmm.vml.vcpu.vcpu_roundup.proof.primatomic_derivedspecs.
 *) *)
End Spec.
