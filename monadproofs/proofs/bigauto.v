Require Import bluerock.ltac2.extra.extra.

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
Require Import monad.fmai.prompts.main.

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
  Context `{Σ: cpp_logic} {gg: genv} {module: translation_unit}.

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
Definition newline := String Char.chr_newline EmptyString.
  
  Definition pprint (s: sym_info) (c: genv_tu.CodeType) : String.string :=
    match c with
    | genv_tu.CTfunction f =>
        "C++ function: " ++ newline++ newline++ Func_printer 0 s f++ newline
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

Ltac2 promptGptForLoopinv currentProofScript : string :=
  let prompt:= fullLoopInvPrompt currentProofScript in
  printf "lprompt: %s" prompt;
  let response := LLM.query_gpt prompt in
  printf "lprompt_response: %s" response;
  match extractLoopInvFromResp response with
  | Some s => s
  | None => "" (*FIX: prompt GPT again, include old response and ask to fix formatting *)
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

  Ltac2 stepp () := stepUntilEmacsInteract false "" 0 [] 0.
  
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

End Spec.
