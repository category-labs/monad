Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Init.Nat.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.

(* -------------------------------------------------------------------- *)
(* Assume Expr is defined elsewhere in your development, with its own
   pretty‐printer (not yet implemented here):                          *)
Parameter Expr : Type.
Fixpoint pretty_expr (n : nat) (e : Expr) : string. Admitted.  (* TODO: FILL IN LATER *)

(* -------------------------------------------------------------------- *)
(* Your C++‐stmt AST:                                                  *)
Inductive Stmt : Type :=
  | SEmpty  : Stmt
  | SExpr   : Expr -> Stmt
  | SReturn : option Expr -> Stmt
  | SIf     : Expr -> Stmt -> option Stmt -> Stmt
  | SWhile  : Expr -> Stmt -> Stmt
  | SBlock  : list Stmt -> Stmt.

(* -------------------------------------------------------------------- *)
(* High‐level pretty‐printer for statements.  We leave it admitted for now *)
Fixpoint pretty_stmt (n : nat) (s : Stmt) : string. Admitted.  (* TODO: FILL IN LATER *)

(* -------------------------------------------------------------------- *)
(* Hole #1: two‐space indentation per nesting level *)
Fixpoint indent (n : nat) : string :=
  match n with
  | O    => ""               
  | S n' => "  " ++ indent n'
  end.

(* -------------------------------------------------------------------- *)
(* A single newline character *)
Definition newline : string :=
  String (Ascii.ascii_of_nat 10) EmptyString.

(* -------------------------------------------------------------------- *)
(* Hole #2: pretty‐printer for a { … } block of statements *)
Definition pretty_block (n : nat) (stmts : list Stmt) : string :=
  let ind   := indent n in
  let ind_s := indent (S n) in
  (* render each sub‐statement at level (S n) *)
  let lines := List.map (fun s => pretty_stmt (S n) s) stmts in
  (* join them with “newline ++ deeper‐indent” *)
  let body  := String.concat (newline ++ ind_s) lines in
  (* assemble:
       indent(n) ++ "{" ++ "\n"
     ++ indent(n+1) ++ stmt1 ++ ("\n" ++ indent(n+1) ++ stmt2 …)
     ++ "\n" ++ indent(n) ++ "}"
  *)
  ind
  ++ "{"
  ++ newline
  ++ ind_s
  ++ body
  ++ newline
  ++ ind
  ++ "}".

(* -------------------------------------------------------------------- *)
(* Once you implement [pretty_stmt], you can remove its Admitted.      *)




Require Import Coq.Strings.String.
Require Import Coq.Lists.List.


Import ListNotations.
Open Scope string_scope.

(* helper to join a list of strings with a separator *)
Definition intercalate (sep : string) (l : list string) : string. Admitted.

(* admit conversion of identifiers to strings *)
Definition ident_to_string (i : ident) : string. Admitted.

(* admitted printers for nested syntactic categories *)
Definition pprint_expr (e : Expr) : string. Admitted.
Definition pprint_vardecl (d : VarDecl) : string. Admitted.
Definition pprint_switchbranch (br : SwitchBranch) : string. Admitted.

Fixpoint pprint_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      "(" ++ intercalate ";" (map pprint_stmt ss) ++ ")"
  | Sdecl ds =>
      "decl " ++ intercalate "," (map pprint_vardecl ds)
  | Sif dv e thn els =>
      "if " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " then " ++ pprint_stmt thn ++
      " else " ++ pprint_stmt els
  | Sif_consteval thn els =>
      "if_consteval " ++ pprint_stmt thn ++ " else_consteval " ++ pprint_stmt els
  | Swhile dv e body =>
      "while " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " do " ++ pprint_stmt body
  | Sfor init cond step body =>
      "for (" ++
      match init with Some st => pprint_stmt st | None => "" end ++ "; " ++
      match cond with Some e => pprint_expr e | None => "" end ++ "; " ++
      match step with Some e => pprint_expr e | None => "" end ++
      ") " ++ pprint_stmt body
  | Sdo body e =>
      "do " ++ pprint_stmt body ++ " while " ++ pprint_expr e
  | Sswitch dv e body =>
      "switch " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++ " { " ++ pprint_stmt body ++ " }"
  | Scase br =>
      "case " ++ pprint_switchbranch br
  | Sdefault => "default"
  | Sbreak => "break"
  | Scontinue => "continue"
  | Sreturn eo =>
      "return" ++
      match eo with Some e => " " ++ pprint_expr e | None => "" end
  | Sexpr e =>
      pprint_expr e
  | Sattr attrs st =>
      "attr[" ++ intercalate "," (map ident_to_string attrs) ++ "] " ++ pprint_stmt st
  | Sasm s vol inputs outputs clobs =>
      "asm(" ++ s ++
      if vol then ",volatile" else "" ++
      ", in{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) inputs) ++
      "}, out{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) outputs) ++
      "}, clob{" ++ intercalate "," (map ident_to_string clobs) ++ "})"
  | Slabeled lbl st =>
      ident_to_string lbl ++ ": " ++ pprint_stmt st
  | Sgoto lbl =>
      "goto " ++ ident_to_string lbl
  | Sunsupported s =>
      "unsupported(" ++ s ++ ")"
  end.



(*
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris_heap_lang/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris_deprecated/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris_unstable/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/eltac/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/eltac/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/eltac/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/cs/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/tc/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/tc/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/tc/elpi/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/coercion/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/coercion/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/test-suite/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/examples/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-hw-models/theories/gic/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/tests/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/stdpp/stdpp_unstable/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/stdpp/stdpp_bitvector/
[cannot-open-path,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/tests/
[cannot-open-path,filesystem,default]
Warning: /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/theories was
previously bound to bluerock.ltac2.llm; it is remapped to
bluerock.ltac2.llm.theories [overriding-logical-loadpath,filesystem,default]
Warning:
Cannot open /home/abhishek/fv-workspace/_build/default/BasicCoqTutorial
[cannot-open-path,filesystem,default]
Welcome to Rocq peach43.devcore4.com:/home/abhishek/fm-workspace/_build/default/fmdeps/coq,main (56dbc340ae8e12990f9af47f1dfadc0bec55d409)

<prompt>Rocq < 1 || 0 < </prompt>Redirect "/tmp/coqKXuDtM" Test Search Output Name Only.

<prompt>Rocq < 2 || 0 < </prompt>Timeout 1 Print Grammar tactic.
Entry ltac_expr is
[ "5" RIGHTA
  [  ]
| "4" LEFTA
  [ SELF; ";"; SELF
  | SELF; ";"; tactic_then_locality; for_each_goal; "]" ]
| "3" RIGHTA
  [ IDENT "try"; SELF
  | IDENT "do"; nat_or_var; SELF
  | IDENT "timeout"; nat_or_var; SELF
  | IDENT "time"; OPT string; SELF
  | IDENT "repeat"; SELF
  | IDENT "progress"; SELF
  | IDENT "once"; SELF
  | IDENT "exactly_once"; SELF
  | IDENT "abstract"; NEXT; "using"; ident
  | IDENT "abstract"; NEXT
  | IDENT "only"; goal_selector; ":"; SELF ]
| "2" RIGHTA
  [ SELF; "+"; SELF
  | SELF; "||"; SELF
  | IDENT "tryif"; SELF; "then"; SELF; "else"; SELF ]
| "1" RIGHTA
  [ "fun"; LIST1 input_fun; "=>"; ltac_expr LEVEL "5"
  | "let"; [ IDENT "rec" |  ]; LIST1 let_clause SEP "with"; "in"; ltac_expr
    LEVEL "5"
  | IDENT "first"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "solve"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "idtac"; LIST0 message_token
  | match_key; IDENT "goal"; "with"; match_context_list; "end"
  | match_key; IDENT "reverse"; IDENT "goal"; "with"; match_context_list;
    "end"
  | match_key; SELF; "with"; match_list; "end"
  | failkw; [ nat_or_var |  ]; LIST0 message_token
  | simple_tactic
  | tactic_value
  | reference; LIST0 tactic_arg ]
| "0" LEFTA
  [ "("; SELF; ")"
  | "["; ">"; for_each_goal; "]"
  | tactic_atom ] ]

Entry simple_tactic is
[ LEFTA
  [ IDENT "firstorder"; OPT tactic; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using
  | IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "congruence"; OPT natural
  | IDENT "dintuition"; tactic
  | IDENT "dintuition"
  | IDENT "intuition"; tactic
  | IDENT "intuition"
  | IDENT "assert_fails"; ltac_expr LEVEL "3"
  | IDENT "inversion_sigma"; hyp; "as"; simple_intropattern
  | IDENT "inversion_sigma"; hyp
  | IDENT "inversion_sigma"
  | IDENT "now"; tactic
  | IDENT "rewrite_all"; "<-"; constr
  | IDENT "rewrite_all"; constr
  | IDENT "destruct_with_eqn"; ":"; ident; ident
  | IDENT "destruct_with_eqn"; ":"; ident; constr
  | IDENT "destruct_with_eqn"; ident
  | IDENT "destruct_with_eqn"; constr
  | IDENT "clearbody"; LIST1 hyp
  | IDENT "clear"; IDENT "dependent"; hyp
  | IDENT "clear"; "-"; LIST1 hyp
  | IDENT "clear"; LIST0 hyp
  | IDENT "revert"; IDENT "dependent"; hyp
  | IDENT "revert"; LIST1 hyp
  | IDENT "rename"; LIST1 rename SEP ","
  | IDENT "move"; hyp; "at"; IDENT "top"
  | IDENT "move"; hyp; "at"; IDENT "bottom"
  | IDENT "move"; hyp; IDENT "after"; hyp
  | IDENT "move"; hyp; IDENT "before"; hyp
  | IDENT "intro"; "at"; IDENT "top"
  | IDENT "intro"; "at"; IDENT "bottom"
  | IDENT "intro"; IDENT "after"; hyp
  | IDENT "intro"; IDENT "before"; hyp
  | IDENT "intro"; ident; "at"; IDENT "top"
  | IDENT "intro"; ident; "at"; IDENT "bottom"
  | IDENT "intro"; ident; IDENT "after"; hyp
  | IDENT "intro"; ident; IDENT "before"; hyp
  | IDENT "intro"; ident
  | IDENT "intro"
  | IDENT "eexists"; LIST1 bindings SEP ","
  | IDENT "eexists"
  | "exists"; LIST1 bindings SEP ","
  | "exists"
  | IDENT "esplit"; "with"; bindings
  | IDENT "split"; "with"; bindings
  | IDENT "symmetry"; "in"; in_clause
  | IDENT "specialize"; constr_with_bindings; "as"; simple_intropattern
  | IDENT "specialize"; constr_with_bindings
  | IDENT "econstructor"; nat_or_var; "with"; bindings
  | IDENT "econstructor"; nat_or_var
  | IDENT "econstructor"
  | IDENT "constructor"; nat_or_var; "with"; bindings
  | IDENT "constructor"; nat_or_var
  | IDENT "constructor"
  | IDENT "eright"; "with"; bindings
  | IDENT "right"; "with"; bindings
  | IDENT "eleft"; "with"; bindings
  | IDENT "left"; "with"; bindings
  | IDENT "exact"; uconstr
  | IDENT "with_strategy"; strategy_level_or_var; "["; LIST1 smart_global;
    "]"; ltac_expr LEVEL "3"
  | IDENT "guard"; test
  | IDENT "swap"; int_or_var; int_or_var
  | IDENT "cycle"; int_or_var
  | IDENT "unshelve"; ltac_expr LEVEL "1"
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"; "using"; ident
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"
  | IDENT "destauto"; "in"; hyp
  | IDENT "destauto"
  | IDENT "specialize_eqs"; hyp
  | IDENT "generalize_eqs_vars"; hyp
  | IDENT "generalize_eqs"; hyp
  | IDENT "stepr"; constr; "by"; tactic
  | IDENT "stepr"; constr
  | IDENT "stepl"; constr; "by"; tactic
  | IDENT "stepl"; constr
  | IDENT "instantiate"; "("; ident; ":="; lconstr; ")"
  | IDENT "instantiate"; "("; natural; ":="; lconstr; ")"; hloc
  | IDENT "evar"; test_lpar_id_colon; "("; ident; ":"; lconstr; ")"
  | IDENT "evar"; constr
  | IDENT "subst"; LIST1 hyp
  | IDENT "subst"
  | IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "refine"; uconstr
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause
  | IDENT "autorewrite"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "with"; LIST1 preident; clause
  | IDENT "contradiction"; OPT constr_with_bindings
  | IDENT "decompose"; "["; LIST1 constr; "]"; constr
  | IDENT "decompose"; IDENT "record"; constr
  | IDENT "decompose"; IDENT "sum"; constr
  | IDENT "einjection"; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg
  | IDENT "einjection"
  | IDENT "injection"; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg
  | IDENT "injection"
  | IDENT "ediscriminate"; destruction_arg
  | IDENT "ediscriminate"
  | IDENT "discriminate"; destruction_arg
  | IDENT "discriminate"
  | IDENT "esimplify_eq"; destruction_arg
  | IDENT "esimplify_eq"
  | IDENT "simplify_eq"; destruction_arg
  | IDENT "simplify_eq"
  | IDENT "replace"; "<-"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "<-"; uconstr; clause
  | IDENT "replace"; "->"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "->"; uconstr; clause
  | IDENT "replace"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; uconstr; clause
  | IDENT "assert_succeeds"; ltac_expr LEVEL "3"
  | IDENT "unify"; constr; constr; "with"; preident
  | IDENT "unify"; constr; constr
  | IDENT "autounfold_one"; hintbases; "in"; hyp
  | IDENT "autounfold_one"; hintbases
  | IDENT "autounfold"; hintbases; clause
  | IDENT "info_eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "info_auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "trivial"; auto_using; hintbases
  | IDENT "info_trivial"; auto_using; hintbases
  | IDENT "trivial"; auto_using; hintbases
  | IDENT "autoapply"; constr; "with"; preident
  | IDENT "head_of_constr"; ident; constr
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var;
    "with"; LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var
  | IDENT "decide"; IDENT "equality"
  | IDENT "decide"; constr; "with"; constr
  | IDENT "setoid_transitivity"; constr
  | IDENT "setoid_etransitivity"
  | IDENT "setoid_symmetry"; "in"; hyp
  | IDENT "setoid_symmetry"
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences;
    "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp; "at";
    occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings
  | IDENT "substitute"; orient; constr_with_bindings
  | IDENT "rewrite_strat"; rewstrategy; "in"; hyp
  | IDENT "rewrite_strat"; rewstrategy
  | IDENT "rewrite_db"; preident; "in"; hyp
  | IDENT "rewrite_db"; preident
  | IDENT "finish_timing"; "("; string; ")"; OPT string
  | IDENT "finish_timing"; OPT string
  | IDENT "restart_timer"; OPT string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; IDENT "cutoff"; integer
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"
  | IDENT "reset"; IDENT "ltac"; IDENT "profile"
  | IDENT "stop"; IDENT "ltac"; IDENT "profiling"
  | IDENT "start"; IDENT "ltac"; IDENT "profiling"
  | IDENT "intros"; IDENT "until"; quantified_hypothesis
  | IDENT "intros"; ne_intropatterns
  | IDENT "intros"
  | IDENT "eintros"; ne_intropatterns
  | IDENT "eintros"
  | IDENT "apply"; "<-"; constr; "in"; hyp
  | IDENT "apply"; "<-"; constr
  | IDENT "apply"; "->"; constr; "in"; hyp
  | IDENT "apply"; "->"; constr
  | IDENT "apply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "elim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "eelim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "case"; induction_clause_list
  | IDENT "ecase"; induction_clause_list
  | "fix"; ident; natural; "with"; LIST1 fixdecl
  | "fix"; ident; natural
  | "cofix"; ident; "with"; LIST1 cofixdecl
  | "cofix"; ident
  | IDENT "set"; bindings_with_parameters; clause
  | IDENT "set"; constr; as_name; clause
  | IDENT "eset"; bindings_with_parameters; clause
  | IDENT "eset"; constr; as_name; clause
  | IDENT "remember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "eremember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "assert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "assert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "assert"; constr; as_ipat; by_tactic
  | IDENT "eassert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "eassert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eassert"; constr; as_ipat; by_tactic
  | IDENT "pose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "pose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "pose"; bindings_with_parameters
  | IDENT "pose"; constr; as_name
  | IDENT "epose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "epose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "epose"; bindings_with_parameters
  | IDENT "epose"; constr; as_name
  | IDENT "enough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "enough"; constr; as_ipat; by_tactic
  | IDENT "eenough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eenough"; constr; as_ipat; by_tactic
  | IDENT "generalize"; IDENT "dependent"; constr
  | IDENT "generalize"; constr; LIST1 constr
  | IDENT "generalize"; constr; lookup_at_as_comma; occs; as_name;
    LIST0 [ ","; pattern_occ; as_name ]
  | IDENT "generalize"; constr
  | IDENT "induction"; induction_clause_list
  | IDENT "einduction"; induction_clause_list
  | IDENT "destruct"; induction_clause_list
  | IDENT "edestruct"; induction_clause_list
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; "at"; occurrences;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; "in"; hyp;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; by_arg_tac
  | IDENT "rewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "erewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "dependent"; IDENT "destruction"; ident
  | IDENT "dependent"; IDENT "induction"; ident
  | IDENT "dependent"; IDENT "generalize_eqs_vars"; hyp
  | IDENT "dependent"; IDENT "generalize_eqs"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr; "in"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr
  | IDENT "dependent";
    [ IDENT "simple"; IDENT "inversion" | IDENT "inversion"
    | IDENT "inversion_clear" ]; quantified_hypothesis; as_or_and_ipat;
    OPT [ "with"; constr ]
  | IDENT "simple"; IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "simple"; IDENT "congruence"; OPT natural
  | IDENT "simple"; IDENT "destruct"; quantified_hypothesis
  | IDENT "simple"; IDENT "induction"; quantified_hypothesis
  | IDENT "simple"; IDENT "subst"
  | IDENT "simple"; IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "injection"; destruction_arg
  | IDENT "simple"; IDENT "injection"
  | IDENT "simple"; IDENT "apply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "inversion"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion_clear"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion"; quantified_hypothesis; "using"; constr; in_hyp_list
  | IDENT "inversion"; quantified_hypothesis; as_or_and_ipat; in_hyp_list
  | IDENT "red"; clause
  | IDENT "hnf"; clause
  | IDENT "simpl"; OPT [ IDENT "head" ]; delta_flag; OPT ref_or_pattern_occ;
    clause
  | IDENT "cbv"; strategy_flag; clause
  | IDENT "cbn"; strategy_flag; clause
  | IDENT "lazy"; strategy_flag; clause
  | IDENT "compute"; delta_flag; clause
  | IDENT "vm_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "native_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "unfold"; LIST1 unfold_occ SEP ","; clause
  | IDENT "fold"; LIST1 constr; clause
  | IDENT "pattern"; LIST1 pattern_occ SEP ","; clause
  | IDENT "change"; conversion; clause
  | IDENT "change_no_check"; conversion; clause ] ]

Entry tactic_value is
[ LEFTA
  [ IDENT "firstorder_using"; ":"; "("; firstorder_using; ")"
  | IDENT "test"; ":"; "("; test; ")"
  | IDENT "comparison"; ":"; "("; comparison; ")"
  | IDENT "opthints"; ":"; "("; opthints; ")"
  | IDENT "auto_using"; ":"; "("; auto_using; ")"
  | IDENT "hintbases"; ":"; "("; hintbases; ")"
  | IDENT "eauto_search_strategy"; ":"; "("; eauto_search_strategy; ")"
  | IDENT "eauto_search_strategy_name"; ":"; "("; eauto_search_strategy_name;
    ")"
  | IDENT "debug"; ":"; "("; debug; ")"
  | IDENT "rewstrategy"; ":"; "("; rewstrategy; ")"
  | IDENT "glob_constr_with_bindings"; ":"; "("; constr_with_bindings; ")"
  | IDENT "strategy_level_or_var"; ":"; "("; strategy_level_or_var; ")"
  | IDENT "strategy_level"; ":"; "("; strategy_level; ")"
  | IDENT "test_lpar_id_colon"; ":"; "("; test_lpar_id_colon; ")"
  | IDENT "in_clause"; ":"; "("; in_clause; ")"
  | IDENT "by_arg_tac"; ":"; "("; by_arg_tac; ")"
  | IDENT "rename"; ":"; "("; rename; ")"
  | IDENT "hloc"; ":"; "("; hloc; ")"
  | IDENT "lglob"; ":"; "("; lconstr; ")"
  | IDENT "lconstr"; ":"; "("; lconstr; ")"
  | IDENT "glob"; ":"; "("; constr; ")"
  | IDENT "occurrences"; ":"; "("; occurrences; ")"
  | IDENT "natural"; ":"; "("; natural; ")"
  | IDENT "orient"; ":"; "("; orient; ")"
  | IDENT "ltac"; ":"; "("; ltac_expr LEVEL "5"; ")"
  | IDENT "open_constr"; ":"; "("; lconstr; ")"
  | IDENT "ipattern"; ":"; "("; simple_intropattern; ")"
  | IDENT "constr"; ":"; "("; lconstr; ")"
  | IDENT "uconstr"; ":"; "("; lconstr; ")"
  | IDENT "reference"; ":"; "("; reference; ")"
  | IDENT "ident"; ":"; "("; ident; ")"
  | IDENT "smart_global"; ":"; "("; smart_global; ")"
  | IDENT "string"; ":"; "("; string; ")"
  | IDENT "integer"; ":"; "("; integer; ")"
  | IDENT "fresh"; LIST0 fresh_id
  | IDENT "type_term"; uconstr
  | IDENT "numgoals"
  | constr_eval ] ]


<prompt>Rocq < 3 || 0 < </prompt>Add Search Blacklist "Private_" "_subproof".

<prompt>Rocq < 4 || 0 < </prompt>Set Suggest Proof Using.

<prompt>Rocq < 5 || 0 < </prompt>Set Diffs "off".

<prompt>Rocq < 6 || 0 < </prompt>Set Printing Depth 50 .

<prompt>Rocq < 7 || 0 < </prompt>Set Printing Width 141.

<prompt>Rocq < 8 || 0 < </prompt>Require Import bluerock.auto.invariants.
<infomsg>[Loading ML file rocq-runtime.plugins.ring ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.zify ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.micromega_core ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.micromega ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.btauto ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.ssrmatching ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.ssreflect ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.ltac2 ... done]</infomsg>
<infomsg>[Loading ML file rocq-runtime.plugins.ltac2_ltac1 ... done]</infomsg>
<infomsg>[Loading ML file ppx_deriving.runtime (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file seq (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file re (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file re.str (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi.util (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi.lexer_config (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file menhirLib (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file stdlib-shims (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi.parser (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi.trace.runtime (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi.runtime (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi.compiler (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file elpi (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file rocq-elpi.elpi ... done]</infomsg>
<infomsg>[Loading ML file mtime (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file mtime.clock (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file mtime.clock.os (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file yojson (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file stdlib-extra (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file rocq-extra (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file ltac2-extra.plugin ... done]</infomsg>
<infomsg>[Loading ML file logger-lib (implicit dependency) ... done]</infomsg>
<infomsg>[Loading ML file ltac2-logger.plugin ... done]</infomsg>
<infomsg>[Loading ML file coq-bluerock-auto-core.custom_subgoals ... done]</infomsg>
<infomsg>[Loading ML file coq-bluerock-auto-core.ignored_hints ... done]</infomsg>

<prompt>Rocq < 9 || 0 < </prompt>Redirect "/tmp/coqzUiWEL" Print Ltac Signatures.

<prompt>Rocq < 10 || 0 < </prompt>Timeout 1 Print Grammar tactic.
Entry ltac_expr is
[ "5" RIGHTA
  [  ]
| "4" LEFTA
  [ SELF; ";"; IDENT "first"; ssr_first_else
  | SELF; ";"; IDENT "first"; ssrseqarg
  | SELF; ";"; IDENT "last"; ssrseqarg
  | SELF; ";"; SELF
  | SELF; ";"; tactic_then_locality; for_each_goal; "]"
  | SELF; ssrintros_ne ]
| "3" RIGHTA
  [ SELF; ssrintros_ne
  | IDENT "try"; SELF
  | IDENT "do"; ssrmmod; ssrdotac; ssrclauses
  | IDENT "do"; ssrortacarg; ssrclauses
  | IDENT "do"; nat_or_var; ssrmmod; ssrdotac; ssrclauses
  | IDENT "do"; nat_or_var; SELF
  | IDENT "timeout"; nat_or_var; SELF
  | IDENT "time"; OPT string; SELF
  | IDENT "repeat"; SELF
  | IDENT "progress"; SELF
  | IDENT "once"; SELF
  | IDENT "exactly_once"; SELF
  | IDENT "abstract"; ssrdgens
  | IDENT "abstract"; NEXT; "using"; ident
  | IDENT "abstract"; NEXT
  | IDENT "only"; goal_selector; ":"; SELF ]
| "2" RIGHTA
  [ SELF; "+"; SELF
  | SELF; "||"; SELF
  | IDENT "tryif"; SELF; "then"; SELF; "else"; SELF ]
| "1" RIGHTA
  [ "fun"; LIST1 input_fun; "=>"; ltac_expr LEVEL "5"
  | "let"; [ IDENT "rec" |  ]; LIST1 let_clause SEP "with"; "in"; ltac_expr
    LEVEL "5"
  | IDENT "first"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "solve"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "idtac"; LIST0 message_token
  | match_key; IDENT "goal"; "with"; match_context_list; "end"
  | match_key; IDENT "reverse"; IDENT "goal"; "with"; match_context_list;
    "end"
  | match_key; SELF; "with"; match_list; "end"
  | failkw; [ nat_or_var |  ]; LIST0 message_token
  | simple_tactic
  | tactic_value
  | reference; LIST0 tactic_arg ]
| "0" LEFTA
  [ "("; SELF; ")"
  | "["; ">"; for_each_goal; "]"
  | ssrparentacarg
  | tactic_atom ] ]

Entry simple_tactic is
[ LEFTA
  [ IDENT "f_contractive_fin"
  | IDENT "f_contractive"; "as"; ident; ident
  | IDENT "f_contractive"
  | IDENT "dist_later_intro"; "as"; ident; ident
  | IDENT "dist_later_intro"
  | IDENT "ofe_subst"; ident
  | IDENT "ofe_subst"
  | IDENT "discriminate_list"; hyp
  | IDENT "discriminate_list"
  | IDENT "simplify_option_eq"; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_option_eq"
  | IDENT "simpl_option"; "by"; ltac_expr LEVEL "3"
  | IDENT "naive_solver"; tactic
  | IDENT "naive_solver"
  | IDENT "select"; open_constr; ltac_expr LEVEL "3"
  | IDENT "learn_hyp"; constr; "as"; ident
  | IDENT "learn_hyp"; constr
  | IDENT "ospecialize"; "*"; uconstr
  | IDENT "ospecialize"; uconstr
  | IDENT "oinv"; integer; "as"; simple_intropattern
  | IDENT "oinv"; integer
  | IDENT "oinv"; uconstr; "as"; simple_intropattern
  | IDENT "oinv"; uconstr
  | IDENT "oinversion"; uconstr; "as"; simple_intropattern
  | IDENT "oinversion"; uconstr
  | IDENT "odestruct"; uconstr; "as"; simple_intropattern
  | IDENT "odestruct"; uconstr
  | IDENT "ogeneralize"; "*"; uconstr
  | IDENT "ogeneralize"; uconstr
  | IDENT "opose"; IDENT "proof"; "*"; uconstr; "as"; simple_intropattern
  | IDENT "opose"; IDENT "proof"; "*"; uconstr
  | IDENT "opose"; IDENT "proof"; uconstr; "as"; simple_intropattern
  | IDENT "opose"; IDENT "proof"; uconstr
  | IDENT "inv"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "inv"; IDENT "select"; open_constr
  | IDENT "inv"; integer; "as"; simple_intropattern
  | IDENT "inv"; integer
  | IDENT "inv"; ident; "as"; simple_intropattern
  | IDENT "inv"; ident
  | IDENT "iter"; tactic; tactic
  | IDENT "f_equiv"; "/="
  | IDENT "f_equal"; "/="
  | IDENT "csimpl"; "in"; "*"
  | IDENT "csimpl"; "in"; hyp
  | IDENT "csimpl"
  | IDENT "eunify"; open_constr; open_constr
  | IDENT "is_non_dependent"; constr
  | IDENT "repeat_on_hyps"; ltac_expr LEVEL "3"
  | IDENT "unless"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "case_guard"; "as"; ident
  | IDENT "case_guard"
  | IDENT "case_match"; IDENT "eqn"; ":"; ident
  | IDENT "destruct_or"; "!"; ident
  | IDENT "destruct_or"; "!"
  | IDENT "destruct_or"; "?"; ident
  | IDENT "destruct_or"; "?"
  | IDENT "destruct_and"; "!"; ident
  | IDENT "destruct_and"; "!"
  | IDENT "destruct_and"; "?"; ident
  | IDENT "destruct_and"; "?"
  | IDENT "split_and"; "!"
  | IDENT "split_and"; "?"
  | IDENT "split_and"
  | IDENT "etrans"
  | IDENT "trans"; constr
  | IDENT "fast_by"; tactic
  | IDENT "compute_by"; tactic
  | IDENT "compute_done"
  | IDENT "case_bool_decide"; "as"; ident
  | IDENT "case_bool_decide"
  | IDENT "case_decide"; "as"; ident
  | IDENT "case_decide"
  | IDENT "destruct_decide"; constr; "as"; ident
  | IDENT "destruct_decide"; constr
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "at"; LIST0 int_or_var; "by"; ltac_expr
    LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "at"; LIST0 int_or_var; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr
  | IDENT "setoid_replace"; constr; "with"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "by";
    ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "at";
    LIST0 int_or_var; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "at";
    LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp
  | IDENT "setoid_replace"; constr; "with"; constr; "at"; LIST0 int_or_var;
    "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr
  | IDENT "reduce"; "in"; hyp
  | IDENT "xpsatz_R"; nat_or_var; tactic
  | IDENT "wpsatz_Q"; nat_or_var; ident; constr
  | IDENT "xpsatz_Q"; nat_or_var; tactic
  | IDENT "wpsatz_Z"; nat_or_var; ident; constr
  | IDENT "xpsatz_Z"; nat_or_var; tactic
  | IDENT "xsos_R"; tactic
  | IDENT "wsos_Q"; ident; constr
  | IDENT "xsos_Q"; tactic
  | IDENT "wsos_Z"; ident; constr
  | IDENT "xsos_Z"; tactic
  | IDENT "wnia"; ident; constr
  | IDENT "xnia"; tactic
  | IDENT "xnra_R"; tactic
  | IDENT "wnra_Q"; ident; constr
  | IDENT "xnra_Q"; tactic
  | IDENT "wlia"; ident; constr
  | IDENT "xlia"; tactic
  | IDENT "xlra_R"; tactic
  | IDENT "wlra_Q"; ident; constr
  | IDENT "xlra_Q"; tactic
  | IDENT "ring_simplify"; "["; LIST0 constr; "]"; LIST0 constr; "in"; hyp
  | IDENT "ring_simplify"; "["; LIST0 constr; "]"; LIST0 constr
  | IDENT "ring_simplify"; LIST0 constr; "in"; hyp
  | IDENT "ring_simplify"; LIST0 constr
  | IDENT "ring"; "["; LIST0 constr; "]"
  | IDENT "ring"
  | IDENT "field_lookup"; tactic; "["; LIST0 constr; "]"; LIST1 constr
  | IDENT "ring_lookup"; ltac_expr LEVEL "0"; "["; LIST0 constr; "]";
    LIST1 constr
  | IDENT "protect_fv"; string; "in"; ident
  | IDENT "protect_fv"; string
  | IDENT "set_solver"; "+"; LIST0 hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"; "+"; LIST0 hyp
  | IDENT "set_solver"; "-"; LIST0 hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"; "-"; LIST0 hyp
  | IDENT "set_solver"; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"
  | IDENT "set_unfold"; "in"; ident
  | IDENT "set_unfold"
  | IDENT "under"; ssrrwarg; IDENT "do"; ssrhint3arg
  | IDENT "under"; ssrrwarg; ssrintros_ne; IDENT "do"; ssrhint3arg
  | IDENT "under"; ssrrwarg; ssrintros_ne
  | IDENT "under"; ssrrwarg
  | IDENT "generally"; IDENT "have"; ssrclear; ssr_idcomma; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "gen"; IDENT "have"; ssrclear; ssr_idcomma; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "without"; IDENT "loss"; IDENT "suffices"; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "without"; IDENT "loss"; IDENT "suff"; ssrhpats_nobs; ssrwlogfwd;
    ssrhint
  | IDENT "without"; IDENT "loss"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; IDENT "suffices"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; IDENT "suff"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "suffices"; IDENT "have"; ssrhpats_nobs; ssrhavefwd
  | IDENT "suffices"; ssrsufffwd
  | IDENT "suff"; IDENT "have"; ssrhpats_nobs; ssrhavefwd
  | IDENT "suff"; ssrsufffwd
  | IDENT "have"; IDENT "suffices"; ssrhpats_nobs; ssrhavefwd
  | IDENT "have"; IDENT "suff"; ssrhpats_nobs; ssrhavefwd
  | IDENT "have"; ssrhavefwdwbinders
  | IDENT "unlock"; ssrunlockargs; ssrclauses
  | IDENT "ssrinstancesofruleR2L"; ssrterm
  | IDENT "ssrinstancesofruleL2R"; ssrterm
  | IDENT "congr"; ssrcongrarg
  | "by"; tactic
  | "by"; ssrhintarg
  | IDENT "multiset_solver"; "by"; ltac_expr LEVEL "3"
  | IDENT "multiset_solver"
  | IDENT "simplify_map_eq"; "/="; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_map_eq"; "/="
  | IDENT "simplify_map_eq"; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_map_eq"
  | IDENT "simpl_map"; "by"; ltac_expr LEVEL "3"
  | IDENT "simpl_map"
  | IDENT "firstorder"; OPT tactic; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using
  | IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "congruence"; OPT natural
  | IDENT "dintuition"; tactic
  | IDENT "dintuition"
  | IDENT "intuition"; tactic
  | IDENT "intuition"
  | IDENT "assert_fails"; ltac_expr LEVEL "3"
  | IDENT "inversion_sigma"; hyp; "as"; simple_intropattern
  | IDENT "inversion_sigma"; hyp
  | IDENT "inversion_sigma"
  | IDENT "now"; tactic
  | IDENT "rewrite_all"; "<-"; constr
  | IDENT "rewrite_all"; constr
  | IDENT "destruct_with_eqn"; ":"; ident; ident
  | IDENT "destruct_with_eqn"; ":"; ident; constr
  | IDENT "destruct_with_eqn"; ident
  | IDENT "destruct_with_eqn"; constr
  | IDENT "clearbody"; LIST1 hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp;
    hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp;
    hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp
  | IDENT "clear"; "-"; LIST1 hyp
  | IDENT "clear"; natural
  | IDENT "clear"; LIST0 hyp
  | IDENT "revert"; IDENT "select"; open_constr
  | IDENT "revert"; IDENT "dependent"; hyp
  | IDENT "revert"; LIST1 hyp
  | IDENT "rename"; IDENT "select"; open_constr; IDENT "into"; ident
  | IDENT "rename"; LIST1 rename SEP ","
  | IDENT "move"; ssrmovearg; ssrrpat
  | IDENT "move"; ssrmovearg; ssrclauses
  | IDENT "move"; ssrrpat
  | IDENT "move"; hyp; "at"; IDENT "top"
  | IDENT "move"; hyp; "at"; IDENT "bottom"
  | IDENT "move"; hyp; IDENT "after"; hyp
  | IDENT "move"; hyp; IDENT "before"; hyp
  | IDENT "move"
  | IDENT "intro"; "at"; IDENT "top"
  | IDENT "intro"; "at"; IDENT "bottom"
  | IDENT "intro"; IDENT "after"; hyp
  | IDENT "intro"; IDENT "before"; hyp
  | IDENT "intro"; ident; "at"; IDENT "top"
  | IDENT "intro"; ident; "at"; IDENT "bottom"
  | IDENT "intro"; ident; IDENT "after"; hyp
  | IDENT "intro"; ident; IDENT "before"; hyp
  | IDENT "intro"; ident
  | IDENT "intro"
  | IDENT "eexists"; LIST1 bindings SEP ","
  | IDENT "eexists"
  | "exists"; LIST1 bindings SEP ","
  | "exists"
  | IDENT "esplit"; "with"; bindings
  | IDENT "split"; "with"; bindings
  | IDENT "symmetry"; "in"; in_clause
  | IDENT "specialize"; constr_with_bindings; "as"; simple_intropattern
  | IDENT "specialize"; constr_with_bindings
  | IDENT "econstructor"; nat_or_var; "with"; bindings
  | IDENT "econstructor"; nat_or_var
  | IDENT "econstructor"
  | IDENT "constructor"; nat_or_var; "with"; bindings
  | IDENT "constructor"; nat_or_var
  | IDENT "constructor"
  | IDENT "eright"; "with"; bindings
  | IDENT "right"; "with"; bindings
  | IDENT "eleft"; "with"; bindings
  | IDENT "left"; "with"; bindings
  | IDENT "exact"; "<:"; lconstr
  | IDENT "exact"; ssrexactarg
  | IDENT "exact"; uconstr
  | IDENT "exact"
  | IDENT "with_strategy"; strategy_level_or_var; "["; LIST1 smart_global;
    "]"; ltac_expr LEVEL "3"
  | IDENT "guard"; test
  | IDENT "swap"; int_or_var; int_or_var
  | IDENT "cycle"; int_or_var
  | IDENT "unshelve"; ltac_expr LEVEL "1"
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"; "using"; ident
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"
  | IDENT "destauto"; "in"; hyp
  | IDENT "destauto"
  | IDENT "specialize_eqs"; hyp
  | IDENT "generalize_eqs_vars"; hyp
  | IDENT "generalize_eqs"; hyp
  | IDENT "stepr"; constr; "by"; tactic
  | IDENT "stepr"; constr
  | IDENT "stepl"; constr; "by"; tactic
  | IDENT "stepl"; constr
  | IDENT "instantiate"; "("; ident; ":="; lconstr; ")"
  | IDENT "instantiate"; "("; natural; ":="; lconstr; ")"; hloc
  | IDENT "evar"; test_lpar_id_colon; "("; ident; ":"; lconstr; ")"
  | IDENT "evar"; constr
  | IDENT "subst"; LIST1 hyp
  | IDENT "subst"
  | IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "refine"; uconstr
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause
  | IDENT "autorewrite"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "with"; LIST1 preident; clause
  | IDENT "contradiction"; OPT constr_with_bindings
  | IDENT "decompose"; "["; LIST1 constr; "]"; constr
  | IDENT "decompose"; IDENT "record"; constr
  | IDENT "decompose"; IDENT "sum"; constr
  | IDENT "einjection"; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg
  | IDENT "einjection"
  | IDENT "injection"; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg
  | IDENT "injection"
  | IDENT "ediscriminate"; destruction_arg
  | IDENT "ediscriminate"
  | IDENT "discriminate"; destruction_arg
  | IDENT "discriminate"
  | IDENT "esimplify_eq"; destruction_arg
  | IDENT "esimplify_eq"
  | IDENT "simplify_eq"; "/="
  | IDENT "simplify_eq"; destruction_arg
  | IDENT "simplify_eq"
  | IDENT "replace"; "<-"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "<-"; uconstr; clause
  | IDENT "replace"; "->"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "->"; uconstr; clause
  | IDENT "replace"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; uconstr; clause
  | IDENT "assert_succeeds"; ltac_expr LEVEL "3"
  | IDENT "unify"; constr; constr; "with"; preident
  | IDENT "unify"; constr; constr
  | IDENT "autounfold_one"; hintbases; "in"; hyp
  | IDENT "autounfold_one"; hintbases
  | IDENT "autounfold"; hintbases; clause
  | IDENT "info_eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "info_auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "trivial"; auto_using; hintbases
  | IDENT "info_trivial"; auto_using; hintbases
  | IDENT "trivial"; auto_using; hintbases
  | IDENT "autoapply"; constr; "with"; preident
  | IDENT "head_of_constr"; ident; constr
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var;
    "with"; LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var
  | IDENT "decide"; IDENT "equality"
  | IDENT "decide"; constr; "with"; constr
  | IDENT "setoid_transitivity"; constr
  | IDENT "setoid_etransitivity"
  | IDENT "setoid_symmetry"; "in"; hyp
  | IDENT "setoid_symmetry"
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences;
    "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp; "at";
    occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings
  | IDENT "substitute"; orient; constr_with_bindings
  | IDENT "rewrite_strat"; rewstrategy; "in"; hyp
  | IDENT "rewrite_strat"; rewstrategy
  | IDENT "rewrite_db"; preident; "in"; hyp
  | IDENT "rewrite_db"; preident
  | IDENT "finish_timing"; "("; string; ")"; OPT string
  | IDENT "finish_timing"; OPT string
  | IDENT "restart_timer"; OPT string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; IDENT "cutoff"; integer
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"
  | IDENT "reset"; IDENT "ltac"; IDENT "profile"
  | IDENT "stop"; IDENT "ltac"; IDENT "profiling"
  | IDENT "start"; IDENT "ltac"; IDENT "profiling"
  | IDENT "intros"; IDENT "until"; quantified_hypothesis
  | IDENT "intros"; ne_intropatterns
  | IDENT "intros"
  | IDENT "eintros"; ne_intropatterns
  | IDENT "eintros"
  | IDENT "apply"; "*"; constr
  | IDENT "apply"; "<-"; constr; "in"; hyp
  | IDENT "apply"; "<-"; constr
  | IDENT "apply"; "->"; constr; "in"; hyp
  | IDENT "apply"; "->"; constr
  | IDENT "apply"; ssrapplyarg
  | IDENT "apply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "apply"
  | IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "elim"; ssrarg; ssrclauses
  | IDENT "elim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "elim"
  | IDENT "eelim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "case"; ssrcasearg; ssrclauses
  | IDENT "case"; induction_clause_list
  | IDENT "case"
  | IDENT "ecase"; induction_clause_list
  | "fix"; ident; natural; "with"; LIST1 fixdecl
  | "fix"; ident; natural
  | "cofix"; ident; "with"; LIST1 cofixdecl
  | "cofix"; ident
  | IDENT "set"; ssrfwdid; ssrsetfwd; ssrclauses
  | IDENT "set"; bindings_with_parameters; clause
  | IDENT "set"; constr; as_name; clause
  | IDENT "eset"; bindings_with_parameters; clause
  | IDENT "eset"; constr; as_name; clause
  | IDENT "remember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "eremember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "assert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "assert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "assert"; constr; as_ipat; by_tactic
  | IDENT "eassert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "eassert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eassert"; constr; as_ipat; by_tactic
  | IDENT "pose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "pose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "pose"; ssrfixfwd
  | IDENT "pose"; ssrcofixfwd
  | IDENT "pose"; ssrfwdid; ssrposefwd
  | IDENT "pose"; bindings_with_parameters
  | IDENT "pose"; constr; as_name
  | IDENT "epose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "epose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "epose"; bindings_with_parameters
  | IDENT "epose"; constr; as_name
  | IDENT "enough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "enough"; constr; as_ipat; by_tactic
  | IDENT "eenough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eenough"; constr; as_ipat; by_tactic
  | IDENT "generalize"; IDENT "dependent"; constr
  | IDENT "generalize"; constr; LIST1 constr
  | IDENT "generalize"; constr; lookup_at_as_comma; occs; as_name;
    LIST0 [ ","; pattern_occ; as_name ]
  | IDENT "generalize"; constr
  | IDENT "induction"; induction_clause_list
  | IDENT "einduction"; induction_clause_list
  | IDENT "destruct"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "destruct"; IDENT "select"; open_constr
  | IDENT "destruct"; induction_clause_list
  | IDENT "edestruct"; induction_clause_list
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; "at"; occurrences;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; "in"; hyp;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; by_arg_tac
  | IDENT "rewrite"; ssrrwargs; ssrclauses
  | IDENT "rewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "erewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "dependent"; IDENT "destruction"; ident
  | IDENT "dependent"; IDENT "induction"; ident
  | IDENT "dependent"; IDENT "generalize_eqs_vars"; hyp
  | IDENT "dependent"; IDENT "generalize_eqs"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr; "in"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr
  | IDENT "dependent";
    [ IDENT "simple"; IDENT "inversion" | IDENT "inversion"
    | IDENT "inversion_clear" ]; quantified_hypothesis; as_or_and_ipat;
    OPT [ "with"; constr ]
  | IDENT "simple"; IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "simple"; IDENT "congruence"; OPT natural
  | IDENT "simple"; IDENT "destruct"; quantified_hypothesis
  | IDENT "simple"; IDENT "induction"; quantified_hypothesis
  | IDENT "simple"; IDENT "subst"
  | IDENT "simple"; IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "injection"; destruction_arg
  | IDENT "simple"; IDENT "injection"
  | IDENT "simple"; IDENT "apply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "inversion"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion_clear"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "inversion"; IDENT "select"; open_constr
  | IDENT "inversion"; quantified_hypothesis; "using"; constr; in_hyp_list
  | IDENT "inversion"; quantified_hypothesis; as_or_and_ipat; in_hyp_list
  | IDENT "red"; clause
  | IDENT "hnf"; clause
  | IDENT "simpl"; OPT [ IDENT "head" ]; delta_flag; OPT ref_or_pattern_occ;
    clause
  | IDENT "cbv"; strategy_flag; clause
  | IDENT "cbn"; strategy_flag; clause
  | IDENT "lazy"; strategy_flag; clause
  | IDENT "compute"; delta_flag; clause
  | IDENT "vm_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "native_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "unfold"; LIST1 unfold_occ SEP ","; clause
  | IDENT "fold"; LIST1 constr; clause
  | IDENT "pattern"; LIST1 pattern_occ SEP ","; clause
  | IDENT "change"; conversion; clause
  | IDENT "change_no_check"; conversion; clause ] ]

Entry tactic_value is
[ LEFTA
  [ IDENT "elpi_code_appArg"; ":"; "("; elpi_code_appArg; ")"
  | IDENT "ghost"; ":"; "("; ghost; ")"
  | IDENT "elpi_code"; ":"; "("; elpi_code; ")"
  | IDENT "ltac_attributes"; ":"; "("; ltac_attributes; ")"
  | IDENT "elpi_tactic_arg"; ":"; "("; elpi_tactic_arg; ")"
  | IDENT "elpi_cmd_arg"; ":"; "("; elpi_cmd_arg; ")"
  | IDENT "attributes"; ":"; "("; attributes; ")"
  | IDENT "elpi_loc"; ":"; "("; elpi_loc; ")"
  | IDENT "qualified_name"; ":"; "("; qualified_name; ")"
  | IDENT "elpi_string"; ":"; "("; elpi_string; ")"
  | IDENT "ltac2val"; ":"; "("; tac2expr_in_env; ")"
  | IDENT "ltac2"; ":"; "("; tac2expr_in_env; ")"
  | IDENT "ssr_idcomma"; ":"; "("; ssr_idcomma; ")"
  | IDENT "ssrwlogfwd"; ":"; "("; ssrwlogfwd; ")"
  | IDENT "ssrsufffwd"; ":"; "("; ssrsufffwd; ")"
  | IDENT "ssrunlockargs"; ":"; "("; ssrunlockargs; ")"
  | IDENT "ssrunlockarg"; ":"; "("; ssrunlockarg; ")"
  | IDENT "ssrrwargs"; ":"; "("; ssrrwargs; ")"
  | IDENT "ssrrwarg"; ":"; "("; ssrrwarg; ")"
  | IDENT "ssrpattern_ne_squarep"; ":"; "("; ssrpattern_ne_squarep; ")"
  | IDENT "ssrpattern_squarep"; ":"; "("; ssrpattern_squarep; ")"
  | IDENT "ssrrule"; ":"; "("; ssrrule; ")"
  | IDENT "ssrrule_ne"; ":"; "("; ssrrule_ne; ")"
  | IDENT "ssrrwocc"; ":"; "("; ssrrwocc; ")"
  | IDENT "ssrcongrarg"; ":"; "("; ssrcongrarg; ")"
  | IDENT "ssrexactarg"; ":"; "("; ssrexactarg; ")"
  | IDENT "ssrapplyarg"; ":"; "("; ssrapplyarg; ")"
  | IDENT "ssragens"; ":"; "("; ssragens; ")"
  | IDENT "ssragen"; ":"; "("; ssragen; ")"
  | IDENT "ssrcasearg"; ":"; "("; ssrcasearg; ")"
  | IDENT "ssrmovearg"; ":"; "("; ssrmovearg; ")"
  | IDENT "ssrarg"; ":"; "("; ssrarg; ")"
  | IDENT "ssreqid"; ":"; "("; ssreqid; ")"
  | IDENT "ssrdgens"; ":"; "("; ssrdgens; ")"
  | IDENT "ssrdgens_tl"; ":"; "("; ssrdgens_tl; ")"
  | IDENT "ssrgen"; ":"; "("; ssrgen; ")"
  | IDENT "ssrseqdir"; ":"; "("; ssrseqdir; ")"
  | IDENT "ssrseqarg"; ":"; "("; ssrseqarg; ")"
  | IDENT "ssrdoarg"; ":"; "("; ssrdoarg; ")"
  | IDENT "ssrhavefwdwbinders"; ":"; "("; ssrhavefwdwbinders; ")"
  | IDENT "ssrhavefwd"; ":"; "("; ssrhavefwd; ")"
  | IDENT "ssrsetfwd"; ":"; "("; ssrsetfwd; ")"
  | IDENT "ssrcofixfwd"; ":"; "("; ssrcofixfwd; ")"
  | IDENT "ssrfixfwd"; ":"; "("; ssrfixfwd; ")"
  | IDENT "ssrposefwd"; ":"; "("; ssrposefwd; ")"
  | IDENT "ssrstruct"; ":"; "("; ssrstruct; ")"
  | IDENT "ssrbinder"; ":"; "("; ssrbinder; ")"
  | IDENT "ssrbvar"; ":"; "("; ssrbvar; ")"
  | IDENT "ssrfwd"; ":"; "("; ssrfwd; ")"
  | IDENT "ssrclauses"; ":"; "("; ssrclauses; ")"
  | IDENT "ssrclausehyps"; ":"; "("; ssrclausehyps; ")"
  | IDENT "ssrwgen"; ":"; "("; ssrwgen; ")"
  | IDENT "ssrhint"; ":"; "("; ssrhint; ")"
  | IDENT "ssrortacarg"; ":"; "("; ssrortacarg; ")"
  | IDENT "ssrhint3arg"; ":"; "("; ssrhint3arg; ")"
  | IDENT "ssrhintarg"; ":"; "("; ssrhintarg; ")"
  | IDENT "ssrortacs"; ":"; "("; ssrortacs; ")"
  | IDENT "ssrfwdid"; ":"; "("; ssrfwdid; ")"
  | IDENT "ssrintrosarg"; ":"; "("; ssrintrosarg; ")"
  | IDENT "ssrintros"; ":"; "("; ssrintros; ")"
  | IDENT "ssrintros_ne"; ":"; "("; ssrintros_ne; ")"
  | IDENT "ssrrpat"; ":"; "("; ssrrpat; ")"
  | IDENT "ssrhpats_nobs"; ":"; "("; ssrhpats_nobs; ")"
  | IDENT "ssrhpats_wtransp"; ":"; "("; ssrhpats_wtransp; ")"
  | IDENT "ssrhpats"; ":"; "("; ssrhpats; ")"
  | IDENT "ssripats_ne"; ":"; "("; ssripats_ne; ")"
  | IDENT "ssrcpat"; ":"; "("; ssrcpat; ")"
  | IDENT "ssriorpat"; ":"; "("; ssriorpat; ")"
  | IDENT "ssripats"; ":"; "("; ssripats; ")"
  | IDENT "ssripat"; ":"; "("; ssripat; ")"
  | IDENT "ident_no_do"; ":"; "("; ident_no_do; ")"
  | IDENT "ssrfwdview"; ":"; "("; ssrfwdview; ")"
  | IDENT "ssrbwdview"; ":"; "("; ssrbwdview; ")"
  | IDENT "ast_closure_lterm"; ":"; "("; ast_closure_lterm; ")"
  | IDENT "ast_closure_term"; ":"; "("; ast_closure_term; ")"
  | IDENT "ssrterm"; ":"; "("; ssrterm; ")"
  | IDENT "ssrdocc"; ":"; "("; ssrdocc; ")"
  | IDENT "ssrmult"; ":"; "("; ssrmult; ")"
  | IDENT "ssrmult_ne"; ":"; "("; ssrmult_ne; ")"
  | IDENT "ssrocc"; ":"; "("; ssrocc; ")"
  | IDENT "ssrindex"; ":"; "("; ssrindex; ")"
  | IDENT "ssrclear"; ":"; "("; ssrclear; ")"
  | IDENT "ssrclear_ne"; ":"; "("; ssrclear_ne; ")"
  | IDENT "ssrsimpl_ne"; ":"; "("; ssrsimpl_ne; ")"
  | IDENT "ssrhoi_id"; ":"; "("; ssrhoi_id; ")"
  | IDENT "ssrhoi_hyp"; ":"; "("; ssrhoi_hyp; ")"
  | IDENT "ssrhyp"; ":"; "("; ssrhyp; ")"
  | IDENT "ssrtclarg"; ":"; "("; ssrtacarg; ")"
  | IDENT "ssrtac3arg"; ":"; "("; ssrtac3arg; ")"
  | IDENT "ssrtacarg"; ":"; "("; ssrtacarg; ")"
  | IDENT "ssrviewposspc"; ":"; "("; ssrviewpos; ")"
  | IDENT "ssrviewpos"; ":"; "("; ssrviewpos; ")"
  | IDENT "ssrhintref"; ":"; "("; ssrhintref; ")"
  | IDENT "ssrpatternarg"; ":"; "("; rpattern; ")"
  | IDENT "lcpattern"; ":"; "("; lcpattern; ")"
  | IDENT "cpattern"; ":"; "("; cpattern; ")"
  | IDENT "rpattern"; ":"; "("; rpattern; ")"
  | IDENT "firstorder_using"; ":"; "("; firstorder_using; ")"
  | IDENT "test"; ":"; "("; test; ")"
  | IDENT "comparison"; ":"; "("; comparison; ")"
  | IDENT "opthints"; ":"; "("; opthints; ")"
  | IDENT "auto_using"; ":"; "("; auto_using; ")"
  | IDENT "hintbases"; ":"; "("; hintbases; ")"
  | IDENT "eauto_search_strategy"; ":"; "("; eauto_search_strategy; ")"
  | IDENT "eauto_search_strategy_name"; ":"; "("; eauto_search_strategy_name;
    ")"
  | IDENT "debug"; ":"; "("; debug; ")"
  | IDENT "rewstrategy"; ":"; "("; rewstrategy; ")"
  | IDENT "glob_constr_with_bindings"; ":"; "("; constr_with_bindings; ")"
  | IDENT "strategy_level_or_var"; ":"; "("; strategy_level_or_var; ")"
  | IDENT "strategy_level"; ":"; "("; strategy_level; ")"
  | IDENT "test_lpar_id_colon"; ":"; "("; test_lpar_id_colon; ")"
  | IDENT "in_clause"; ":"; "("; in_clause; ")"
  | IDENT "by_arg_tac"; ":"; "("; by_arg_tac; ")"
  | IDENT "rename"; ":"; "("; rename; ")"
  | IDENT "hloc"; ":"; "("; hloc; ")"
  | IDENT "lglob"; ":"; "("; lconstr; ")"
  | IDENT "lconstr"; ":"; "("; lconstr; ")"
  | IDENT "glob"; ":"; "("; constr; ")"
  | IDENT "occurrences"; ":"; "("; occurrences; ")"
  | IDENT "natural"; ":"; "("; natural; ")"
  | IDENT "orient"; ":"; "("; orient; ")"
  | IDENT "ltac"; ":"; "("; ltac_expr LEVEL "5"; ")"
  | IDENT "open_constr"; ":"; "("; lconstr; ")"
  | IDENT "ipattern"; ":"; "("; simple_intropattern; ")"
  | IDENT "constr"; ":"; "("; lconstr; ")"
  | IDENT "uconstr"; ":"; "("; lconstr; ")"
  | IDENT "reference"; ":"; "("; reference; ")"
  | IDENT "ident"; ":"; "("; ident; ")"
  | IDENT "smart_global"; ":"; "("; smart_global; ")"
  | IDENT "string"; ":"; "("; string; ")"
  | IDENT "integer"; ":"; "("; integer; ")"
  | IDENT "fresh"; LIST0 fresh_id
  | IDENT "type_term"; uconstr
  | IDENT "numgoals"
  | constr_eval ] ]


<prompt>Rocq < 11 || 0 < </prompt>Timeout 1 Print LoadPath.
Logical Path / Physical path:
LF /home/abhishek/fv-workspace/BasicCoqTutorial
monad /home/abhishek/fv-workspace/_build/default/monad/monadproofs
monad.EVMOpSem /home/abhishek/fv-workspace/_build/default/monad/monadproofs/EVMOpSem
monad.EVMOpSem.Lem /home/abhishek/fv-workspace/_build/default/monad/monadproofs/EVMOpSem/Lem
monad.asts /home/abhishek/fv-workspace/_build/default/monad/monadproofs/asts
monad.fmai /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai
monad.fmai.driver /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/driver
monad.fmai.driver.ltac2 /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/driver/ltac2
monad.fmai.prompts /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/prompts
monad.proofs /home/abhishek/fv-workspace/_build/default/monad/monadproofs/proofs
monad.proofs.execproofs /home/abhishek/fv-workspace/_build/default/monad/monadproofs/proofs/execproofs
monad.tutorials /home/abhishek/fv-workspace/_build/default/monad/monadproofs/tutorials
monad /home/abhishek/fv-workspace/monad/monadproofs
monad.EVMOpSem /home/abhishek/fv-workspace/monad/monadproofs/EVMOpSem
monad.EVMOpSem.Lem /home/abhishek/fv-workspace/monad/monadproofs/EVMOpSem/Lem
monad.asts /home/abhishek/fv-workspace/monad/monadproofs/asts
monad.fmai /home/abhishek/fv-workspace/monad/monadproofs/fmai
monad.fmai.driver /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver
monad.fmai.driver.elisp /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver/elisp
monad.fmai.driver.ltac2 /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver/ltac2
monad.fmai.prompts /home/abhishek/fv-workspace/monad/monadproofs/fmai/prompts
monad.proofs /home/abhishek/fv-workspace/monad/monadproofs/proofs
monad.proofs.execproofs /home/abhishek/fv-workspace/monad/monadproofs/proofs/execproofs
monad.tutorials /home/abhishek/fv-workspace/monad/monadproofs/tutorials
bluerock.ltac2.llm /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm
bluerock.ltac2.llm.plugin /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/plugin
bluerock.ltac2.llm.theories /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/theories
bedrocktest /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/tests
Ltac2 /home/abhishek/fv-workspace/fmdeps/coq/user-contrib/Ltac2
Ltac2.Compat /home/abhishek/fv-workspace/fmdeps/coq/user-contrib/Ltac2/Compat
Corelib /home/abhishek/fv-workspace/fmdeps/coq/theories
Corelib.Array /home/abhishek/fv-workspace/fmdeps/coq/theories/Array
Corelib.BinNums /home/abhishek/fv-workspace/fmdeps/coq/theories/BinNums
Corelib.Classes /home/abhishek/fv-workspace/fmdeps/coq/theories/Classes
Corelib.Compat /home/abhishek/fv-workspace/fmdeps/coq/theories/Compat
Corelib.Floats /home/abhishek/fv-workspace/fmdeps/coq/theories/Floats
Corelib.Init /home/abhishek/fv-workspace/fmdeps/coq/theories/Init
Corelib.Lists /home/abhishek/fv-workspace/fmdeps/coq/theories/Lists
Corelib.Numbers /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers
Corelib.Numbers.Cyclic /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers/Cyclic
Corelib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers/Cyclic/Int63
Corelib.Program /home/abhishek/fv-workspace/fmdeps/coq/theories/Program
Corelib.Relations /home/abhishek/fv-workspace/fmdeps/coq/theories/Relations
Corelib.Setoids /home/abhishek/fv-workspace/fmdeps/coq/theories/Setoids
Corelib.Strings /home/abhishek/fv-workspace/fmdeps/coq/theories/Strings
Corelib.derive /home/abhishek/fv-workspace/fmdeps/coq/theories/derive
Corelib.extraction /home/abhishek/fv-workspace/fmdeps/coq/theories/extraction
Corelib.ssr /home/abhishek/fv-workspace/fmdeps/coq/theories/ssr
Corelib.ssrmatching /home/abhishek/fv-workspace/fmdeps/coq/theories/ssrmatching
Corelib /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories
Corelib.Array /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Array
Corelib.BinNums /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/BinNums
Corelib.Classes /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Classes
Corelib.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Compat
Corelib.Floats /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Floats
Corelib.Init /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Init
Corelib.Lists /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Lists
Corelib.Numbers /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers
Corelib.Numbers.Cyclic /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers/Cyclic
Corelib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers/Cyclic/Int63
Corelib.Program /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Program
Corelib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Relations
Corelib.Setoids /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Setoids
Corelib.Strings /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Strings
Corelib.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/derive
Corelib.extraction /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/extraction
Corelib.ssr /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/ssr
Corelib.ssrmatching /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/ssrmatching
stdpp /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp
stdpp /home/abhishek/fv-workspace/_build/default/fmdeps/stdpp/stdpp
stdpp.bitvector /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp_bitvector
stdpp.unstable /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp_unstable
Stdlib /home/abhishek/fv-workspace/fmdeps/stdlib/theories
Stdlib.All /home/abhishek/fv-workspace/fmdeps/stdlib/theories/All
Stdlib.Arith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Arith
Stdlib.Array /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Array
Stdlib.BinNums /home/abhishek/fv-workspace/fmdeps/stdlib/theories/BinNums
Stdlib.Bool /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Bool
Stdlib.Classes /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Classes
Stdlib.Compat /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Compat
Stdlib.FSets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/FSets
Stdlib.Floats /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Floats
Stdlib.Init /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Init
Stdlib.Lists /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Lists
Stdlib.Logic /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Logic
Stdlib.MSets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/MSets
Stdlib.NArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/NArith
Stdlib.Numbers /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers
Stdlib.Numbers.Cyclic /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic
Stdlib.Numbers.Cyclic.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic/Abstract
Stdlib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic/Int63
Stdlib.Numbers.Integer /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer
Stdlib.Numbers.Integer.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/Abstract
Stdlib.Numbers.Integer.Binary /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/Binary
Stdlib.Numbers.Integer.NatPairs /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/NatPairs
Stdlib.Numbers.NatInt /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/NatInt
Stdlib.Numbers.Natural /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural
Stdlib.Numbers.Natural.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural/Abstract
Stdlib.Numbers.Natural.Binary /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural/Binary
Stdlib.PArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/PArith
Stdlib.Program /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Program
Stdlib.QArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/QArith
Stdlib.Reals /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals
Stdlib.Reals.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals/Abstract
Stdlib.Reals.Cauchy /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals/Cauchy
Stdlib.Relations /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Relations
Stdlib.Setoids /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Setoids
Stdlib.Sets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Sets
Stdlib.Sorting /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Sorting
Stdlib.Streams /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Streams
Stdlib.Strings /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Strings
Stdlib.Structures /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Structures
Stdlib.Unicode /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Unicode
Stdlib.Vectors /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Vectors
Stdlib.Wellfounded /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Wellfounded
Stdlib.ZArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ZArith
Stdlib.btauto /home/abhishek/fv-workspace/fmdeps/stdlib/theories/btauto
Stdlib.derive /home/abhishek/fv-workspace/fmdeps/stdlib/theories/derive
Stdlib.extraction /home/abhishek/fv-workspace/fmdeps/stdlib/theories/extraction
Stdlib.funind /home/abhishek/fv-workspace/fmdeps/stdlib/theories/funind
Stdlib.micromega /home/abhishek/fv-workspace/fmdeps/stdlib/theories/micromega
Stdlib.nsatz /home/abhishek/fv-workspace/fmdeps/stdlib/theories/nsatz
Stdlib.omega /home/abhishek/fv-workspace/fmdeps/stdlib/theories/omega
Stdlib.rtauto /home/abhishek/fv-workspace/fmdeps/stdlib/theories/rtauto
Stdlib.setoid_ring /home/abhishek/fv-workspace/fmdeps/stdlib/theories/setoid_ring
Stdlib.ssr /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ssr
Stdlib.ssrmatching /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ssrmatching
Stdlib /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories
Stdlib.All /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/All
Stdlib.Arith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Arith
Stdlib.Array /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Array
Stdlib.BinNums /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/BinNums
Stdlib.Bool /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Bool
Stdlib.Classes /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Classes
Stdlib.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Compat
Stdlib.FSets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/FSets
Stdlib.Floats /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Floats
Stdlib.Init /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Init
Stdlib.Lists /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Lists
Stdlib.Logic /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Logic
Stdlib.MSets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/MSets
Stdlib.NArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/NArith
Stdlib.Numbers /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers
Stdlib.Numbers.Cyclic /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic
Stdlib.Numbers.Cyclic.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic/Abstract
Stdlib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic/Int63
Stdlib.Numbers.Integer /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer
Stdlib.Numbers.Integer.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/Abstract
Stdlib.Numbers.Integer.Binary /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/Binary
Stdlib.Numbers.Integer.NatPairs /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/NatPairs
Stdlib.Numbers.NatInt /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/NatInt
Stdlib.Numbers.Natural /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural
Stdlib.Numbers.Natural.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural/Abstract
Stdlib.Numbers.Natural.Binary /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural/Binary
Stdlib.PArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/PArith
Stdlib.Program /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Program
Stdlib.QArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/QArith
Stdlib.Reals /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals
Stdlib.Reals.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals/Abstract
Stdlib.Reals.Cauchy /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals/Cauchy
Stdlib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Relations
Stdlib.Setoids /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Setoids
Stdlib.Sets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Sets
Stdlib.Sorting /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Sorting
Stdlib.Streams /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Streams
Stdlib.Strings /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Strings
Stdlib.Structures /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Structures
Stdlib.Unicode /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Unicode
Stdlib.Vectors /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Vectors
Stdlib.Wellfounded /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Wellfounded
Stdlib.ZArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ZArith
Stdlib.btauto /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/btauto
Stdlib.derive /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/derive
Stdlib.extraction /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/extraction
Stdlib.funind /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/funind
Stdlib.micromega /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/micromega
Stdlib.nsatz /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/nsatz
Stdlib.omega /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/omega
Stdlib.rtauto /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/rtauto
Stdlib.setoid_ring /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/setoid_ring
Stdlib.ssr /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ssr
Stdlib.ssrmatching /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ssrmatching
bluerock.nova_interface /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories
bluerock.nova_interface.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64
bluerock.nova_interface.aarch64.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/opsem
bluerock.nova_interface.aarch64.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/wp_nova
bluerock.nova_interface.hypercall /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/hypercall
bluerock.nova_interface.machine_logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/machine_logic
bluerock.nova_interface.model /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/model
bluerock.nova_interface.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/opsem
bluerock.nova_interface.predicates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/predicates
bluerock.nova_interface.upstream /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/upstream
bluerock.nova_interface.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/wp_nova
bluerock.nova_interface.x86_64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64
bluerock.nova_interface.x86_64.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/opsem
bluerock.nova_interface.x86_64.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/wp_nova
bluerock.elpi.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp
bluerock.elpi.cpp.Command /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Command
bluerock.elpi.cpp.Program /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Program
bluerock.elpi.cpp.Program.interp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Program/interp
bluerock.elpi.cpp.Tactic /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Tactic
bluerock.elpi.cpp.internal /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/internal
bluerock.elpi.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp
bluerock.elpi.cpp.Command /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Command
bluerock.elpi.cpp.Program /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Program
bluerock.elpi.cpp.Program.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Program/interp
bluerock.elpi.cpp.Tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Tactic
bluerock.elpi.cpp.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/internal
bluerock_tests.elpi.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/tests
bluerock /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories
bluerock.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/algebra
bluerock.auto /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto
bluerock.auto.big_sep /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/big_sep
bluerock.auto.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp
bluerock.auto.cpp.auto_frac /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/auto_frac
bluerock.auto.cpp.database /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/database
bluerock.auto.cpp.default_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/default_spec
bluerock.auto.cpp.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi
bluerock.auto.cpp.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/derive
bluerock.auto.cpp.elpi.enum /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum
bluerock.auto.cpp.elpi.enum.variant /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum/variant
bluerock.auto.cpp.elpi.synth /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth
bluerock.auto.cpp.elpi.synth.both /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/both
bluerock.auto.cpp.elpi.synth.interp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp
bluerock.auto.cpp.elpi.synth.interp.model
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/model
bluerock.auto.cpp.elpi.synth.interp.rep
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/rep
bluerock.auto.cpp.elpi.synth.synterp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp
bluerock.auto.cpp.elpi.synth.synterp.rep
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp/rep
bluerock.auto.cpp.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints
bluerock.auto.cpp.hints.ptrs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints/ptrs
bluerock.auto.cpp.pretty /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/pretty
bluerock.auto.cpp.specs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/specs
bluerock.auto.cpp.templates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates
bluerock.auto.cpp.templates.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/hints
bluerock.auto.cpp.templates.logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/logic
bluerock.auto.cpp.templates.semantics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/semantics
bluerock.auto.cpp.templates.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/spec
bluerock.auto.cpp.templates.syntax /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/syntax
bluerock.auto.cpp.templates.upstream /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream
bluerock.auto.cpp.templates.upstream.ast
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/ast
bluerock.auto.cpp.templates.upstream.bi
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/bi
bluerock.auto.cpp.templates.upstream.brick
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/brick
bluerock.auto.cpp.templates.upstream.prelude
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/prelude
bluerock.auto.cpp.templates.verif /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/verif
bluerock.auto.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi
bluerock.auto.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi/derive
bluerock.auto.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/hints
bluerock.auto.lemmas /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/lemmas
bluerock.auto.pure /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/pure
bluerock.auto.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/tactics
bluerock.base_logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic
bluerock.base_logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic/lib
bluerock.bi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/bi
bluerock.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp
bluerock.cpp.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp/spec
bluerock.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/lib
bluerock.micromega /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/micromega
bluerock.prelude /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude
bluerock.prelude.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/elpi
bluerock.prelude.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics
bluerock.prelude.tactics.ltac2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics/ltac2
bluerock.proofmode /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode
bluerock.proofmode.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode/cpp
bluerock /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories
bluerock.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/algebra
bluerock.auto /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto
bluerock.auto.big_sep /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/big_sep
bluerock.auto.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp
bluerock.auto.cpp.auto_frac /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/auto_frac
bluerock.auto.cpp.database /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/database
bluerock.auto.cpp.default_spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/default_spec
bluerock.auto.cpp.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi
bluerock.auto.cpp.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/derive
bluerock.auto.cpp.elpi.enum /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum
bluerock.auto.cpp.elpi.enum.variant
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum/variant
bluerock.auto.cpp.elpi.synth /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth
bluerock.auto.cpp.elpi.synth.both
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/both
bluerock.auto.cpp.elpi.synth.interp
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp
bluerock.auto.cpp.elpi.synth.interp.model
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/model
bluerock.auto.cpp.elpi.synth.interp.rep
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/rep
bluerock.auto.cpp.elpi.synth.synterp
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp
bluerock.auto.cpp.elpi.synth.synterp.rep
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp/rep
bluerock.auto.cpp.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints
bluerock.auto.cpp.hints.ptrs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints/ptrs
bluerock.auto.cpp.pretty /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/pretty
bluerock.auto.cpp.specs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/specs
bluerock.auto.cpp.templates /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates
bluerock.auto.cpp.templates.hints
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/hints
bluerock.auto.cpp.templates.logic
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/logic
bluerock.auto.cpp.templates.semantics
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/semantics
bluerock.auto.cpp.templates.spec
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/spec
bluerock.auto.cpp.templates.syntax
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/syntax
bluerock.auto.cpp.templates.upstream
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream
bluerock.auto.cpp.templates.upstream.ast
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/ast
bluerock.auto.cpp.templates.upstream.bi
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/bi
bluerock.auto.cpp.templates.upstream.brick
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/brick
bluerock.auto.cpp.templates.upstream.prelude
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/prelude
bluerock.auto.cpp.templates.verif
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/verif
bluerock.auto.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi
bluerock.auto.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi/derive
bluerock.auto.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/hints
bluerock.auto.lemmas /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/lemmas
bluerock.auto.pure /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/pure
bluerock.auto.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/tactics
bluerock.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic
bluerock.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic/lib
bluerock.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/bi
bluerock.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp
bluerock.cpp.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp/spec
bluerock.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/lib
bluerock.micromega /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/micromega
bluerock.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude
bluerock.prelude.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/elpi
bluerock.prelude.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics
bluerock.prelude.tactics.ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics/ltac2
bluerock.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode
bluerock.proofmode.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode/cpp
bluerock_auto.tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests
bluerock_auto.tests.anonymous_union /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/anonymous_union
bluerock_auto.tests.arch_indep /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep
bluerock_auto.tests.arch_indep.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep/aarch64
bluerock_auto.tests.arch_indep.x86_64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep/x86_64
bluerock_auto.tests.arith /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arith
bluerock_auto.tests.array /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/array
bluerock_auto.tests.ast /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/ast
bluerock_auto.tests.brick_eval /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/brick_eval
bluerock_auto.tests.brick_eval.bad /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/brick_eval/bad
bluerock_auto.tests.casts /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/casts
bluerock_auto.tests.const /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/const
bluerock_auto.tests.constants /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/constants
bluerock_auto.tests.control_flow /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/control_flow
bluerock_auto.tests.cpp_proof /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/cpp_proof
bluerock_auto.tests.cpp_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/cpp_spec
bluerock_auto.tests.data_class /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/data_class
bluerock_auto.tests.dataclass_demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/dataclass_demo
bluerock_auto.tests.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/derive
bluerock_auto.tests.duck_types /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/duck_types
bluerock_auto.tests.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi
bluerock_auto.tests.elpi.enums /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi/enums
bluerock_auto.tests.elpi.specifications /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi/specifications
bluerock_auto.tests.fields /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/fields
bluerock_auto.tests.fupd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/fupd
bluerock_auto.tests.inc /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inc
bluerock_auto.tests.includes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/includes
bluerock_auto.tests.inheritence /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inheritence
bluerock_auto.tests.inits /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inits
bluerock_auto.tests.io /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/io
bluerock_auto.tests.lambda /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lambda
bluerock_auto.tests.lazy_unfold /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lazy_unfold
bluerock_auto.tests.lib_alloc /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lib_alloc
bluerock_auto.tests.llist /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/llist
bluerock_auto.tests.llist_cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/llist_cpp
bluerock_auto.tests.local_scope /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/local_scope
bluerock_auto.tests.micromega /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/micromega
bluerock_auto.tests.misc_tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/misc_tests
bluerock_auto.tests.new_delete /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/new_delete
bluerock_auto.tests.operator_auto /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/operator_auto
bluerock_auto.tests.params /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/params
bluerock_auto.tests.perf /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/perf
bluerock_auto.tests.pretty /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/pretty
bluerock_auto.tests.read_prim /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/read_prim
bluerock_auto.tests.reps /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/reps
bluerock_auto.tests.return_void /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/return_void
bluerock_auto.tests.simple /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/simple
bluerock_auto.tests.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/spec
bluerock_auto.tests.specify /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify
bluerock_auto.tests.specify.challenge /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify/challenge
bluerock_auto.tests.specify.copymove /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify/copymove
bluerock_auto.tests.specify_cmd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify_cmd
bluerock_auto.tests.static_methods /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/static_methods
bluerock_auto.tests.synth_names /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/synth_names
bluerock_auto.tests.tactics4 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/tactics4
bluerock_auto.tests.templates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/templates
bluerock_auto.tests.union /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/union
bluerock_auto.tests.universes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/universes
bluerock_auto.tests.unlocked /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/unlocked
bluerock_auto.tests.val_cat /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/val_cat
bluerock_auto.tests.validate_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/validate_spec
bluerock_auto.tests.var_args /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/var_args
bluerock_auto.tests.virtual /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/virtual
bluerock_auto.tests.virtual.mdc_noimpl /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/virtual/mdc_noimpl
bluerock.hw_models.gic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/gic
bluerock.hw_models.cpu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu
bluerock.hw_models.cpu.inst /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/inst
bluerock.hw_models.cpu.inst.sail /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/inst/sail
bluerock.hw_models.cpu.msr /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/msr
bluerock.hw_models.core /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core
bluerock.hw_models.core.ip /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core/ip
bluerock_auto_core.examples /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples
bluerock_auto_core.examples.classes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples/classes
bluerock_auto_core.examples.tutorial /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples/tutorial
bluerock.auto.core /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories
bluerock.auto.core.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints
bluerock.auto.core.hints.classes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/classes
bluerock.auto.core.hints.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/lib
bluerock.auto.core.internal /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal
bluerock.auto.core.internal.VM /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/VM
bluerock.auto.core.internal.instr /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/instr
bluerock.auto.core.internal.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/lib
bluerock.auto.core.internal.ltac2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/ltac2
bluerock.auto.core.internal.plib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plib
bluerock.auto.core.internal.plugins /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plugins
bluerock.auto.core.internal.syntactic_bi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi
bluerock.auto.core.internal.syntactic_bi.forced
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi/forced
bluerock.auto.core.internal.tactic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/tactic
bluerock.auto.core /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories
bluerock.auto.core.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints
bluerock.auto.core.hints.classes /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/classes
bluerock.auto.core.hints.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/lib
bluerock.auto.core.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal
bluerock.auto.core.internal.VM /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/VM
bluerock.auto.core.internal.instr /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/instr
bluerock.auto.core.internal.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/lib
bluerock.auto.core.internal.ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/ltac2
bluerock.auto.core.internal.plib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plib
bluerock.auto.core.internal.plugins /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plugins
bluerock.auto.core.internal.syntactic_bi
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi
bluerock.auto.core.internal.syntactic_bi.forced
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi/forced
bluerock.auto.core.internal.tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/tactic
bluerock_auto_core.tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests
bluerock_auto_core.tests.cancelx /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/cancelx
bluerock_auto_core.tests.fwd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/fwd
bluerock_auto_core.tests.id /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/id
bluerock_auto_core.tests.learn /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/learn
bluerock_auto_core.tests.observe /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/observe
bluerock.cpp.demo /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof
bluerock.cpp.demo.aggregate01 /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/aggregate01
bluerock.cpp.demo.basic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/basic
bluerock.cpp.demo.data_class /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/data_class
bluerock.cpp.demo.inline /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/inline
bluerock.cpp.demo.loops /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/loops
bluerock.lts_adequacy_demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories
bluerock.lts_adequacy_demo.example /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example
bluerock.lts_adequacy_demo.example.apps /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/apps
bluerock.lts_adequacy_demo.example.languages /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/languages
bluerock.lts_adequacy_demo.example.logics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/logics
bluerock.lts_adequacy_demo.example.lts /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/lts
bluerock.lts_adequacy_demo.example.programs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/programs
bluerock.lts_adequacy_demo.iris /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/iris
bluerock.lts_adequacy_demo.refinement /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/refinement
bluerock.cpp.stdlib /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories
bluerock.cpp.stdlib.allocator /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/allocator
bluerock.cpp.stdlib.atomic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/atomic
bluerock.cpp.stdlib.cassert /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/cassert
bluerock.cpp.stdlib.concepts /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/concepts
bluerock.cpp.stdlib.exception /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/exception
bluerock.cpp.stdlib.new /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/new
bluerock.cpp.stdlib.vector /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/vector
bluerock.cpp.stdlib.test /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests
bluerock.cpp.stdlib.test.atomic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/atomic
bluerock.cpp.stdlib.test.concepts /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/concepts
bluerock.cpp.stdlib.test.vector /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/vector
bluerock.hw_models /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories
bluerock.hw_models.computer2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/computer2
bluerock.hw_models.demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/demo
bluerock.hw_models.mmu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/mmu
bluerock.hw_models.smmu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/smmu
bluerock.hw_models.smmu.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/smmu/aarch64
Equations.TestSuite /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite
Equations.TestSuite.HoTT /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/HoTT
Equations.TestSuite.disabled /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/disabled
Equations.TestSuite.issues /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/issues
Equations.Examples /home/abhishek/fv-workspace/fmdeps/coq-equations/examples
Equations.Examples.disabled /home/abhishek/fv-workspace/fmdeps/coq-equations/examples/disabled
Equations /home/abhishek/fv-workspace/fmdeps/coq-equations/theories
Equations.HoTT /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/HoTT
Equations.Type /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/Type
Equations /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories
Equations.Type /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories/Type
Equations.Prop /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/Prop
Equations.Prop /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories/Prop
elpi.apps.coercion /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/coercion/theories
elpi.apps.coercion.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/coercion/tests
elpi.apps.locker.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/elpi
elpi.apps.locker /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/locker/theories
elpi.apps.locker /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/theories
elpi.apps.locker.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/locker/tests
elpi.apps.derive.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/elpi
elpi.apps.derive.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/examples
elpi.apps.derive /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/theories
elpi.apps.derive.derive /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/theories/derive
elpi.apps.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/theories
elpi.apps.derive.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/theories/derive
elpi.apps.derive.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/tests
elpi.apps.tc /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/theories
elpi.apps.tc.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests
elpi.apps.tc.tests.WIP /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/WIP
elpi.apps.tc.tests.WIP.premisesSort /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/WIP/premisesSort
elpi.apps.tc.tests.importOrder /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/importOrder
elpi.apps.tc.tests.register /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/register
elpi.apps.cs /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/cs/theories
elpi.apps.eltac.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/examples
elpi.apps.eltac /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/theories
elpi.apps.eltac.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/tests
elpi.apps.NES.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/elpi
elpi.apps.NES.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/examples
elpi.apps.NES /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/theories
elpi.apps.NES /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/theories
elpi.apps.NES.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/tests
elpi_elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/elpi
elpi_examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/examples
elpi /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories
elpi.attic /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/attic
elpi.core /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/core
elpi.wip /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/wip
elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/theories
elpi.core /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/theories/core
elpi.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/tests
iris.unstable /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable
iris.unstable.algebra /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/algebra
iris.unstable.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/base_logic
iris.unstable.heap_lang /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/heap_lang
iris.deprecated /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated
iris.deprecated.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated/base_logic
iris.deprecated.program_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated/program_logic
iris.heap_lang /home/abhishek/fv-workspace/fmdeps/iris/iris_heap_lang
iris.heap_lang.lib /home/abhishek/fv-workspace/fmdeps/iris/iris_heap_lang/lib
iris /home/abhishek/fv-workspace/fmdeps/iris/iris
iris.algebra /home/abhishek/fv-workspace/fmdeps/iris/iris/algebra
iris.algebra.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/algebra/lib
iris.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/base_logic
iris.base_logic.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/base_logic/lib
iris.bi /home/abhishek/fv-workspace/fmdeps/iris/iris/bi
iris.bi.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/bi/lib
iris.prelude /home/abhishek/fv-workspace/fmdeps/iris/iris/prelude
iris.program_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/program_logic
iris.proofmode /home/abhishek/fv-workspace/fmdeps/iris/iris/proofmode
iris.si_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/si_logic
iris /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris
iris.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/algebra
iris.algebra.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/algebra/lib
iris.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/base_logic
iris.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/base_logic/lib
iris.bi /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/bi
iris.bi.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/bi/lib
iris.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/prelude
iris.program_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/program_logic
iris.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/proofmode
iris.si_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/si_logic
AAC_tactics /home/abhishek/fv-workspace/fmdeps/aac-tactics/theories
AAC_tactics /home/abhishek/fv-workspace/_build/default/fmdeps/aac-tactics/theories
ExtLibExamples /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/examples
ExtLib /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories
ExtLib.Core /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Core
ExtLib.Data /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data
ExtLib.Data.Eq /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Eq
ExtLib.Data.Graph /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Graph
ExtLib.Data.Map /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Map
ExtLib.Data.Monads /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Monads
ExtLib.Data.Set /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Set
ExtLib.Generic /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Generic
ExtLib.Programming /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Programming
ExtLib.Recur /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Recur
ExtLib.Relations /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Relations
ExtLib.Structures /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Structures
ExtLib.Tactics /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Tactics
ExtLib /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories
ExtLib.Core /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Core
ExtLib.Data /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data
ExtLib.Data.Eq /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Eq
ExtLib.Data.Graph /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Graph
ExtLib.Data.Map /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Map
ExtLib.Data.Monads /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Monads
ExtLib.Data.Set /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Set
ExtLib.Generic /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Generic
ExtLib.Programming /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Programming
ExtLib.Recur /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Recur
ExtLib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Relations
ExtLib.Structures /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Structures
ExtLib.Tactics /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Tactics
bluerock.prelude /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories
bluerock.prelude.arith /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/arith
bluerock.prelude.axioms /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/axioms
bluerock.prelude.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi
bluerock.prelude.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi/derive
bluerock.prelude.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/tactics
bluerock.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories
bluerock.prelude.arith /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/arith
bluerock.prelude.axioms /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/axioms
bluerock.prelude.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi
bluerock.prelude.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi/derive
bluerock.prelude.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/tactics
Lens /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-lens/Lens
Lens.Elpi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-lens/Lens/Elpi
Lens /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-lens/Lens
Lens.Elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-lens/Lens/Elpi
bluerock.ltac2.llm /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-llm/theories
bluerock.ltac2.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/theories
bluerock.ltac2.extra.internal /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/theories/internal
bluerock.ltac2.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/theories
bluerock.ltac2.extra.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/theories/internal
bluerock_tests.ltac2.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/tests
bluerock_tests.ltac2.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/tests
bluerock.iris.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories
bluerock.iris.extra.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/algebra
bluerock.iris.extra.base_logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic
bluerock.iris.extra.base_logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic/lib
bluerock.iris.extra.bi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi
bluerock.iris.extra.bi.spec /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi/spec
bluerock.iris.extra.proofmode /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/proofmode
bluerock.iris.extra.si_logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/si_logic
bluerock.iris.extra.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/tactics
bluerock.iris.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories
bluerock.iris.extra.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/algebra
bluerock.iris.extra.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic
bluerock.iris.extra.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic/lib
bluerock.iris.extra.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi
bluerock.iris.extra.bi.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi/spec
bluerock.iris.extra.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/proofmode
bluerock.iris.extra.si_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/si_logic
bluerock.iris.extra.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/tactics
bluerock.ltac2.logger /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-logger/theories
bluerock.ltac2.logger /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-logger/theories
accumulate_bug /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/accumulate_bug
accumulate_bug /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/accumulate_bug
bluerock.elpi.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra
bluerock.elpi.extra.Command /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Command
bluerock.elpi.extra.Command.both /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Command/both
bluerock.elpi.extra.Program /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program
bluerock.elpi.extra.Program.both /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program/both
bluerock.elpi.extra.Program.interp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program/interp
bluerock.elpi.extra.Tactic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Tactic
bluerock.elpi.extra.TacticCommand /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand
bluerock.elpi.extra.TacticCommand.interp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand/interp
bluerock.elpi.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra
bluerock.elpi.extra.Command /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Command
bluerock.elpi.extra.Command.both /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Command/both
bluerock.elpi.extra.Program /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program
bluerock.elpi.extra.Program.both /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program/both
bluerock.elpi.extra.Program.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program/interp
bluerock.elpi.extra.Tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Tactic
bluerock.elpi.extra.TacticCommand /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand
bluerock.elpi.extra.TacticCommand.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand/interp
bluerock_tests.elpi.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/tests
bluerock_tests.elpi.extra.NES /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/tests/NES
bluerock_tests.elpi.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/tests
bluerock_tests.elpi.extra.NES /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/tests/NES
bluerock.noimport /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport
bluerock.noimport.doc /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc
bluerock.noimport.doc.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc/cpp
bluerock.noimport /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport
bluerock.noimport.doc /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc
bluerock.noimport.doc.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc/cpp
bluerock.lang.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp
bluerock.lang.cpp.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/algebra
bluerock.lang.cpp.bi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi
bluerock.lang.cpp.bi.spec /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi/spec
bluerock.lang.cpp.logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic
bluerock.lang.cpp.logic.heap_pred /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/heap_pred
bluerock.lang.cpp.logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/lib
bluerock.lang.cpp.model /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/model
bluerock.lang.cpp.mparser /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/mparser
bluerock.lang.cpp.parser /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser
bluerock.lang.cpp.parser.plugin /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser/plugin
bluerock.lang.cpp.semantics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/semantics
bluerock.lang.cpp.specs /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/specs
bluerock.lang.cpp.syntax /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax
bluerock.lang.cpp.syntax.name_notation
  /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax/name_notation
bluerock.lang.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp
bluerock.lang.cpp.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/algebra
bluerock.lang.cpp.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi
bluerock.lang.cpp.bi.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi/spec
bluerock.lang.cpp.logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic
bluerock.lang.cpp.logic.heap_pred
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/heap_pred
bluerock.lang.cpp.logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/lib
bluerock.lang.cpp.model /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/model
bluerock.lang.cpp.mparser /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/mparser
bluerock.lang.cpp.parser /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser
bluerock.lang.cpp.parser.plugin
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser/plugin
bluerock.lang.cpp.semantics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/semantics
bluerock.lang.cpp.specs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/specs
bluerock.lang.cpp.syntax /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax
bluerock.lang.cpp.syntax.name_notation
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax/name_notation
tc_db_info /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-tc-db-info/theories
tc_db_info /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-tc-db-info/theories
bluerock.upoly /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-upoly/upoly
bluerock.upoly /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-upoly/upoly
<> /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib
Ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib/Ltac2
Ltac2.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib/Ltac2/Compat

<prompt>Rocq < 12 || 0 < </prompt>Set Silent.

<prompt>Rocq < 13 || 0 < </prompt>Require Import bluerock.auto.cpp.proof.

<prompt>Rocq < 14 || 0 < </prompt>Unset Silent.

<prompt>Rocq < 15 || 0 < </prompt>Import linearity.

<prompt>Rocq < 16 || 0 < </prompt>Redirect "/tmp/coqjWduHy" Print Ltac Signatures.

<prompt>Rocq < 17 || 0 < </prompt>Timeout 1 Print Grammar tactic.
Entry ltac_expr is
[ "5" RIGHTA
  [  ]
| "4" LEFTA
  [ SELF; ";"; IDENT "first"; ssr_first_else
  | SELF; ";"; IDENT "first"; ssrseqarg
  | SELF; ";"; IDENT "last"; ssrseqarg
  | SELF; ";"; SELF
  | SELF; ";"; tactic_then_locality; for_each_goal; "]"
  | SELF; ssrintros_ne ]
| "3" RIGHTA
  [ SELF; ssrintros_ne
  | IDENT "try"; SELF
  | IDENT "do"; ssrmmod; ssrdotac; ssrclauses
  | IDENT "do"; ssrortacarg; ssrclauses
  | IDENT "do"; nat_or_var; ssrmmod; ssrdotac; ssrclauses
  | IDENT "do"; nat_or_var; SELF
  | IDENT "timeout"; nat_or_var; SELF
  | IDENT "time"; OPT string; SELF
  | IDENT "repeat"; SELF
  | IDENT "progress"; SELF
  | IDENT "once"; SELF
  | IDENT "exactly_once"; SELF
  | IDENT "abstract"; ssrdgens
  | IDENT "abstract"; NEXT; "using"; ident
  | IDENT "abstract"; NEXT
  | IDENT "only"; goal_selector; ":"; SELF ]
| "2" RIGHTA
  [ SELF; "+"; SELF
  | SELF; "||"; SELF
  | IDENT "tryif"; SELF; "then"; SELF; "else"; SELF ]
| "1" RIGHTA
  [ "fun"; LIST1 input_fun; "=>"; ltac_expr LEVEL "5"
  | "let"; [ IDENT "rec" |  ]; LIST1 let_clause SEP "with"; "in"; ltac_expr
    LEVEL "5"
  | IDENT "first"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "solve"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "idtac"; LIST0 message_token
  | match_key; IDENT "goal"; "with"; match_context_list; "end"
  | match_key; IDENT "reverse"; IDENT "goal"; "with"; match_context_list;
    "end"
  | match_key; SELF; "with"; match_list; "end"
  | failkw; [ nat_or_var |  ]; LIST0 message_token
  | simple_tactic
  | tactic_value
  | reference; LIST0 tactic_arg ]
| "0" LEFTA
  [ "("; SELF; ")"
  | "["; ">"; for_each_goal; "]"
  | ssrparentacarg
  | tactic_atom ] ]

Entry simple_tactic is
[ LEFTA
  [ IDENT "hint_label"; reference
  | IDENT "wthrough"; open_constr; ltac_expr LEVEL "3"; ltac_expr LEVEL "3"
  | IDENT "wthrough"; open_constr; ltac_expr LEVEL "3"
  | IDENT "wthrough"; open_constr
  | IDENT "wuntil"; open_constr; ltac_expr LEVEL "3"
  | IDENT "unBP2"; open_constr
  | IDENT "BP"; open_constr
  | IDENT "wmod_"; uconstr
  | IDENT "wmod"; uconstr
  | IDENT "gc"; "-"; LIST1 ident
  | IDENT "step"; LIST0 br_modifier
  | IDENT "learn_exist"; LIST0 br_modifier
  | IDENT "pgo1"; LIST0 br_modifier
  | IDENT "ego1"; LIST0 br_modifier
  | IDENT "go1"; LIST0 br_modifier
  | IDENT "pgo"; LIST0 br_modifier
  | IDENT "ego"; LIST0 br_modifier
  | IDENT "go"; LIST0 br_modifier
  | IDENT "prun1"; LIST0 br_modifier
  | IDENT "erun1"; LIST0 br_modifier
  | IDENT "run1"; LIST0 br_modifier
  | IDENT "prun"; LIST0 br_modifier
  | IDENT "erun"; LIST0 br_modifier
  | IDENT "run"; LIST0 br_modifier
  | IDENT "pwork"; LIST0 br_modifier
  | IDENT "ework"; LIST0 br_modifier
  | IDENT "work"; LIST0 br_modifier
  | IDENT "wgc"; LIST0 br_modifier
  | IDENT "learner"; LIST0 br_modifier
  | IDENT "psep"; LIST0 br_modifier
  | IDENT "esep"; LIST0 br_modifier
  | IDENT "sep"; LIST0 br_modifier
  | "with_log_tmp_file!"; constr; tactic
  | IDENT "with_log_tmp_file"; constr; tactic
  | IDENT "with_log_tmp"; constr; constr; tactic
  | "output_log_tmp_file!"; constr
  | IDENT "output_log_tmp_file"; constr
  | IDENT "output_log_tmp"; constr; constr
  | "with_log_file!"; constr; tactic
  | IDENT "with_log_file"; constr; tactic
  | "with_log!"; tactic
  | IDENT "with_log"; tactic
  | IDENT "with_log_generic"; constr; constr; tactic
  | "output_log_file!"; constr
  | IDENT "output_log_file"; constr
  | "output_log!"
  | IDENT "output_log"
  | IDENT "output_log_generic"; constr; constr
  | IDENT "pop_all_spans"
  | IDENT "reset_log"
  | IDENT "with_unsealed_bi"; tactic
  | IDENT "vc_split"; rpattern
  | IDENT "vc_split"
  | IDENT "iAaccIntro1"; "with"; constr
  | IDENT "iAuIntro1"
  | IDENT "icancel"; open_constr
  | IDENT "wrename"; "["; rpattern; "]"; constr
  | IDENT "wname"; "["; rpattern; "]"; constr
  | IDENT "cut_pure"; open_constr
  | IDENT "wsplit_matchL"; open_constr
  | IDENT "wsplit_matchR"; open_constr
  | IDENT "wfocus"; open_constr; "-"; constr
  | IDENT "wfocus"; open_constr; constr
  | IDENT "ren_hyp"; ident; open_constr
  | IDENT "bind_ren"; ident; "["; rpattern; "]"
  | IDENT "shadow_rename"; ident; IDENT "into"; ident
  | IDENT "bind"; "["; rpattern; "]"; ltac_expr LEVEL "3"
  | IDENT "wexists"; open_constr
  | IDENT "use_protectb"; open_constr
  | IDENT "use_protect"; open_constr
  | IDENT "useb"; open_constr
  | IDENT "use"; open_constr
  | IDENT "ren_evar"; open_constr; ident
  | IDENT "solve_proper"; "using"; uconstr; ","; uconstr; ","; uconstr; ",";
    uconstr
  | IDENT "solve_proper"; "using"; uconstr; ","; uconstr; ","; uconstr
  | IDENT "solve_proper"; "using"; uconstr; ","; uconstr
  | IDENT "solve_proper"; "using"; uconstr
  | IDENT "destruct_tele"; "/="
  | IDENT "pclean"
  | IDENT "punfold"; hyp
  | IDENT "punfold"
  | IDENT "pinst"; hyp; open_constr
  | IDENT "ipExists"; ident
  | IDENT "ipExists"
  | IDENT "pexists"; ident
  | IDENT "pexists"
  | IDENT "iAccu"
  | IDENT "iInv"; constr; "as"; "("; LIST1 simple_intropattern; ")"; constr;
    constr
  | IDENT "iInv"; constr; "as"; "("; LIST1 simple_intropattern; ")"; constr
  | IDENT "iInv"; constr; "as"; constr; constr
  | IDENT "iInv"; constr; "as"; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; constr; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; constr
  | IDENT "iInvCore"; constr; "in"; ltac_expr LEVEL "3"
  | IDENT "iInvCore"; constr; "as"; constr; "in"; ltac_expr LEVEL "3"
  | IDENT "iInvCore"; constr; "with"; constr; "in"; ltac_expr LEVEL "3"
  | IDENT "iInvCore"; constr; "with"; constr; "as"; open_constr; "in";
    ltac_expr LEVEL "3"
  | IDENT "iAssumptionInv"; constr
  | IDENT "iMod"; open_constr; "as"; "%"; simple_intropattern
  | IDENT "iMod"; open_constr; "as"; "("; LIST1 simple_intropattern; ")";
    constr
  | IDENT "iMod"; open_constr; "as"; constr
  | IDENT "iMod"; open_constr
  | IDENT "iRewrite"; "-"; open_constr; "in"; constr
  | IDENT "iRewrite"; "-"; open_constr
  | IDENT "iRewrite"; open_constr; "in"; constr
  | IDENT "iRewrite"; open_constr
  | IDENT "iAssert"; open_constr; "as"; "%"; simple_intropattern
  | IDENT "iAssert"; open_constr; "as"; "("; LIST1 simple_intropattern; ")";
    constr
  | IDENT "iAssert"; open_constr; "as"; constr
  | IDENT "iAssert"; open_constr; "with"; constr; "as"; "%";
    simple_intropattern
  | IDENT "iAssert"; open_constr; "with"; constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr
  | IDENT "iAssert"; open_constr; "with"; constr; "as"; constr
  | IDENT "iAssertCore"; open_constr; "as"; constr; ltac_expr LEVEL "3"
  | IDENT "iAssertCore"; open_constr; "with"; constr; "as"; constr; ltac_expr
    LEVEL "3"
  | IDENT "iLöb"; "as"; constr; "forall"; "("; LIST1 ident; ")"; constr
  | IDENT "iLöb"; "as"; constr; "forall"; "("; LIST1 ident; ")"
  | IDENT "iLöb"; "as"; constr; "forall"; constr
  | IDENT "iLöb"; "as"; constr
  | IDENT "iLöbCore"; "as"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr;
    "forall"; "("; LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr;
    "forall"; "("; LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr;
    "forall"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "forall"; "(";
    LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "forall"; "(";
    LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "forall"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr; "forall"; "("; LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr; "forall"; "("; LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr; "forall"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "forall";
    "("; LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "forall";
    "("; LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "forall";
    constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern
  | IDENT "iInductionCore"; ltac_expr LEVEL "3"; "as"; constr
  | IDENT "iPoseProof"; open_constr; "as"; "("; LIST1 simple_intropattern;
    ")"; constr
  | IDENT "iPoseProof"; open_constr; "as"; constr
  | IDENT "iDestruct"; IDENT "select"; open_constr; "as"; "%";
    simple_intropattern
  | IDENT "iDestruct"; IDENT "select"; open_constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr
  | IDENT "iDestruct"; IDENT "select"; open_constr; "as"; constr
  | IDENT "iDestruct"; open_constr; "as"; "%"; simple_intropattern
  | IDENT "iDestruct"; open_constr; "as"; "("; LIST1 simple_intropattern;
    ")"; constr
  | IDENT "iDestruct"; open_constr; "as"; constr
  | IDENT "iDestructCore"; open_constr; "as"; constr; ltac_expr LEVEL "3"
  | IDENT "iRevertIntros"; "with"; ltac_expr LEVEL "3"
  | IDENT "iRevertIntros"; "("; LIST1 ident; ")"; "with"; ltac_expr LEVEL "3"
  | IDENT "iRevertIntros"; "("; LIST1 ident; ")"; constr; "with"; ltac_expr
    LEVEL "3"
  | IDENT "iRevertIntros"; constr; "with"; ltac_expr LEVEL "3"
  | IDENT "iIntros"; "("; LIST1 simple_intropattern; ")"; constr
  | IDENT "iIntros"; "("; LIST1 simple_intropattern; ")"
  | IDENT "iIntros"; constr; "("; LIST1 simple_intropattern; ")"; constr
  | IDENT "iIntros"; constr; "("; LIST1 simple_intropattern; ")"
  | IDENT "iIntros"; constr
  | IDENT "iIntros"
  | IDENT "iCombineAsGivesCore"; constr; "as"; constr; IDENT "gives";
    ltac_expr LEVEL "3"
  | IDENT "iCombineGivesCore"; constr; IDENT "gives"; ltac_expr LEVEL "3"
  | IDENT "iCombine"; constr; IDENT "gives"; "%"; simple_intropattern
  | IDENT "iCombine"; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; "as"; constr; IDENT "gives"; "%";
    simple_intropattern
  | IDENT "iCombine"; constr; "as"; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; "as"; constr
  | IDENT "iCombine"; constr; constr; IDENT "gives"; "%"; simple_intropattern
  | IDENT "iCombine"; constr; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; constr; "as"; constr; IDENT "gives"; "%";
    simple_intropattern
  | IDENT "iCombine"; constr; constr; "as"; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; constr; "as"; constr
  | IDENT "iDestructHyp"; constr; "as"; "("; LIST1 simple_intropattern; ")";
    constr
  | IDENT "iDestructHyp"; constr; "as"; constr
  | IDENT "iModCore"; constr; "as"; constr
  | IDENT "iNext"; open_constr
  | IDENT "iNext"
  | IDENT "iAlways"
  | IDENT "iModIntro"; uconstr
  | IDENT "iModIntro"
  | IDENT "iExists"; LIST1 uconstr SEP ","
  | IDENT "iSplitR"; constr
  | IDENT "iSplitR"
  | IDENT "iSplitL"; constr
  | IDENT "iSplitL"
  | IDENT "iSplit"
  | IDENT "iOrDestruct"; constr; "as"; constr; constr
  | IDENT "iRight"
  | IDENT "iLeft"
  | IDENT "iApply"; open_constr
  | IDENT "iApplyHyp"; constr
  | IDENT "iPoseProofCore"; open_constr; "as"; constr; ltac_expr LEVEL "3"
  | IDENT "iSpecialize"; open_constr; "as"; "#"
  | IDENT "iSpecialize"; open_constr
  | IDENT "iSpecializeCore"; open_constr; "as"; constr
  | IDENT "iSpecializeCore"; open_constr; "with"; open_constr; open_constr;
    "as"; constr
  | IDENT "iPoseProofCoreLem"; open_constr; "as"; ltac_expr LEVEL "3"
  | IDENT "iPoseProofCoreHyp"; constr; "as"; constr
  | IDENT "iRevert"; IDENT "select"; open_constr
  | IDENT "iRevert"; "("; LIST1 ident; ")"; constr
  | IDENT "iRevert"; "("; LIST1 ident; ")"
  | IDENT "iRevert"; constr
  | IDENT "iRevertHyp"; constr; "with"; ltac_expr LEVEL "1"
  | IDENT "iRevertHyp"; constr
  | IDENT "iFrame"; IDENT "select"; open_constr
  | IDENT "iFrame"; "("; LIST1 constr; ")"; constr
  | IDENT "iFrame"; "("; LIST1 constr; ")"
  | IDENT "iFrame"; constr
  | IDENT "iFrame"
  | IDENT "iPureIntro"
  | IDENT "iEmpIntro"
  | IDENT "iPure"; constr; "as"; simple_intropattern
  | IDENT "iExFalso"
  | IDENT "iAssumption"
  | IDENT "iAssumptionCoq"
  | IDENT "iAssumptionCore"
  | IDENT "iExact"; constr
  | IDENT "iUnfold"; LIST1 reference SEP ","; "in"; constr
  | IDENT "iUnfold"; LIST1 reference SEP ","
  | IDENT "iSimpl"; "in"; constr
  | IDENT "iSimpl"
  | IDENT "iEval"; ltac_expr LEVEL "3"; "in"; constr
  | IDENT "iEval"; ltac_expr LEVEL "3"
  | IDENT "iClear"; IDENT "select"; open_constr
  | IDENT "iClear"; "("; LIST0 ident; ")"; constr
  | IDENT "iClear"; constr
  | IDENT "iRename"; IDENT "select"; open_constr; IDENT "into"; constr
  | IDENT "iRename"; constr; IDENT "into"; constr
  | IDENT "iStopProof"
  | IDENT "iStartProof"; uconstr
  | IDENT "iStartProof"
  | IDENT "iSelect"; open_constr; ltac_expr LEVEL "1"
  | IDENT "iMatchHyp"; ltac_expr LEVEL "1"
  | IDENT "wmod_base"; ltac_expr LEVEL "3"; uconstr
  | IDENT "wpose_with_mask_change"; uconstr
  | IDENT "wpose"; uconstr
  | IDENT "wassert"; open_constr
  | IDENT "wapply"; open_constr
  | IDENT "wp_for_"; uconstr
  | IDENT "wp_for"; uconstr
  | IDENT "wp_do_while_"; uconstr
  | IDENT "wp_do_while"; uconstr
  | IDENT "wp_while_"; uconstr
  | IDENT "wp_while"; uconstr
  | IDENT "wp_switch_"; uconstr
  | IDENT "wp_switch"; uconstr
  | IDENT "wp_switch"
  | IDENT "wpe_spec"; uconstr
  | "wpe_spec["; open_constr; "]"; uconstr
  | IDENT "wpe_if"; uconstr
  | IDENT "wpe_if"
  | "wpe_if["; open_constr; "]"; uconstr
  | IDENT "wp_if_"; uconstr
  | IDENT "wp_if"; uconstr
  | IDENT "wp_if"
  | IDENT "updateGll"; open_constr; open_constr
  | IDENT "mk_obs_fwd"; uconstr
  | IDENT "ltac_attributes"; ":"; "("; ltac_attributes; ")"; IDENT "elpi";
    qualified_name; LIST0 elpi_tactic_arg
  | "#["; attributes; "]"; IDENT "elpi"; qualified_name;
    LIST0 elpi_tactic_arg
  | IDENT "elpi"; IDENT "query"; ghost; elpi_string
  | IDENT "elpi"; IDENT "query"; qualified_name; elpi_string
  | IDENT "elpi"; qualified_name; LIST0 elpi_tactic_arg
  | IDENT "iCaccIntro"; "with"; constr
  | IDENT "iAcIntro"
  | IDENT "iAaccIntro"; "with"; constr
  | IDENT "iAuIntro"
  | IDENT "solve_ne_proper"; "using"; constr
  | IDENT "field_simplify_eq"; "in"; hyp
  | IDENT "field_simplify_eq"; "["; LIST0 constr; "]"; "in"; hyp
  | IDENT "field_simplify_eq"; "["; LIST0 constr; "]"
  | IDENT "field_simplify_eq"
  | IDENT "field"; "["; LIST0 constr; "]"
  | IDENT "field"
  | IDENT "field_simplify"; "["; LIST0 constr; "]"; LIST0 constr; "in"; hyp
  | IDENT "field_simplify"; "["; LIST0 constr; "]"; LIST0 constr
  | IDENT "field_simplify"; LIST0 constr; "in"; hyp
  | IDENT "field_simplify"; LIST0 constr
  | IDENT "f_contractive_fin"
  | IDENT "f_contractive"; "as"; ident; ident
  | IDENT "f_contractive"
  | IDENT "dist_later_intro"; "as"; ident; ident
  | IDENT "dist_later_intro"
  | IDENT "ofe_subst"; ident
  | IDENT "ofe_subst"
  | IDENT "discriminate_list"; hyp
  | IDENT "discriminate_list"
  | IDENT "simplify_option_eq"; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_option_eq"
  | IDENT "simpl_option"; "by"; ltac_expr LEVEL "3"
  | IDENT "naive_solver"; tactic
  | IDENT "naive_solver"
  | IDENT "select"; open_constr; ltac_expr LEVEL "3"
  | IDENT "learn_hyp"; constr; "as"; ident
  | IDENT "learn_hyp"; constr
  | IDENT "ospecialize"; "*"; uconstr
  | IDENT "ospecialize"; uconstr
  | IDENT "oinv"; integer; "as"; simple_intropattern
  | IDENT "oinv"; integer
  | IDENT "oinv"; uconstr; "as"; simple_intropattern
  | IDENT "oinv"; uconstr
  | IDENT "oinversion"; uconstr; "as"; simple_intropattern
  | IDENT "oinversion"; uconstr
  | IDENT "odestruct"; uconstr; "as"; simple_intropattern
  | IDENT "odestruct"; uconstr
  | IDENT "ogeneralize"; "*"; uconstr
  | IDENT "ogeneralize"; uconstr
  | IDENT "opose"; IDENT "proof"; "*"; uconstr; "as"; simple_intropattern
  | IDENT "opose"; IDENT "proof"; "*"; uconstr
  | IDENT "opose"; IDENT "proof"; uconstr; "as"; simple_intropattern
  | IDENT "opose"; IDENT "proof"; uconstr
  | IDENT "inv"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "inv"; IDENT "select"; open_constr
  | IDENT "inv"; integer; "as"; simple_intropattern
  | IDENT "inv"; integer
  | IDENT "inv"; ident; "as"; simple_intropattern
  | IDENT "inv"; ident
  | IDENT "iter"; tactic; tactic
  | IDENT "f_equiv"; "/="
  | IDENT "f_equal"; "/="
  | IDENT "csimpl"; "in"; "*"
  | IDENT "csimpl"; "in"; hyp
  | IDENT "csimpl"
  | IDENT "eunify"; open_constr; open_constr
  | IDENT "is_non_dependent"; constr
  | IDENT "repeat_on_hyps"; ltac_expr LEVEL "3"
  | IDENT "unless"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "case_guard"; "as"; ident
  | IDENT "case_guard"
  | IDENT "case_match"; IDENT "eqn"; ":"; ident
  | IDENT "destruct_or"; "!"; ident
  | IDENT "destruct_or"; "!"
  | IDENT "destruct_or"; "?"; ident
  | IDENT "destruct_or"; "?"
  | IDENT "destruct_and"; "!"; ident
  | IDENT "destruct_and"; "!"
  | IDENT "destruct_and"; "?"; ident
  | IDENT "destruct_and"; "?"
  | IDENT "split_and"; "!"
  | IDENT "split_and"; "?"
  | IDENT "split_and"
  | IDENT "etrans"
  | IDENT "trans"; constr
  | IDENT "fast_by"; tactic
  | IDENT "compute_by"; tactic
  | IDENT "compute_done"
  | IDENT "case_bool_decide"; "as"; ident
  | IDENT "case_bool_decide"
  | IDENT "case_decide"; "as"; ident
  | IDENT "case_decide"
  | IDENT "destruct_decide"; constr; "as"; ident
  | IDENT "destruct_decide"; constr
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "at"; LIST0 int_or_var; "by"; ltac_expr
    LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "at"; LIST0 int_or_var; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr
  | IDENT "setoid_replace"; constr; "with"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "by";
    ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "at";
    LIST0 int_or_var; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "at";
    LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp
  | IDENT "setoid_replace"; constr; "with"; constr; "at"; LIST0 int_or_var;
    "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr
  | IDENT "reduce"; "in"; hyp
  | IDENT "xpsatz_R"; nat_or_var; tactic
  | IDENT "wpsatz_Q"; nat_or_var; ident; constr
  | IDENT "xpsatz_Q"; nat_or_var; tactic
  | IDENT "wpsatz_Z"; nat_or_var; ident; constr
  | IDENT "xpsatz_Z"; nat_or_var; tactic
  | IDENT "xsos_R"; tactic
  | IDENT "wsos_Q"; ident; constr
  | IDENT "xsos_Q"; tactic
  | IDENT "wsos_Z"; ident; constr
  | IDENT "xsos_Z"; tactic
  | IDENT "wnia"; ident; constr
  | IDENT "xnia"; tactic
  | IDENT "xnra_R"; tactic
  | IDENT "wnra_Q"; ident; constr
  | IDENT "xnra_Q"; tactic
  | IDENT "wlia"; ident; constr
  | IDENT "xlia"; tactic
  | IDENT "xlra_R"; tactic
  | IDENT "wlra_Q"; ident; constr
  | IDENT "xlra_Q"; tactic
  | IDENT "ring_simplify"; "["; LIST0 constr; "]"; LIST0 constr; "in"; hyp
  | IDENT "ring_simplify"; "["; LIST0 constr; "]"; LIST0 constr
  | IDENT "ring_simplify"; LIST0 constr; "in"; hyp
  | IDENT "ring_simplify"; LIST0 constr
  | IDENT "ring"; "["; LIST0 constr; "]"
  | IDENT "ring"
  | IDENT "field_lookup"; tactic; "["; LIST0 constr; "]"; LIST1 constr
  | IDENT "ring_lookup"; ltac_expr LEVEL "0"; "["; LIST0 constr; "]";
    LIST1 constr
  | IDENT "protect_fv"; string; "in"; ident
  | IDENT "protect_fv"; string
  | IDENT "set_solver"; "+"; LIST0 hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"; "+"; LIST0 hyp
  | IDENT "set_solver"; "-"; LIST0 hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"; "-"; LIST0 hyp
  | IDENT "set_solver"; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"
  | IDENT "set_unfold"; "in"; ident
  | IDENT "set_unfold"
  | IDENT "under"; ssrrwarg; IDENT "do"; ssrhint3arg
  | IDENT "under"; ssrrwarg; ssrintros_ne; IDENT "do"; ssrhint3arg
  | IDENT "under"; ssrrwarg; ssrintros_ne
  | IDENT "under"; ssrrwarg
  | IDENT "generally"; IDENT "have"; ssrclear; ssr_idcomma; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "gen"; IDENT "have"; ssrclear; ssr_idcomma; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "without"; IDENT "loss"; IDENT "suffices"; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "without"; IDENT "loss"; IDENT "suff"; ssrhpats_nobs; ssrwlogfwd;
    ssrhint
  | IDENT "without"; IDENT "loss"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; IDENT "suffices"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; IDENT "suff"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "suffices"; IDENT "have"; ssrhpats_nobs; ssrhavefwd
  | IDENT "suffices"; ssrsufffwd
  | IDENT "suff"; IDENT "have"; ssrhpats_nobs; ssrhavefwd
  | IDENT "suff"; ssrsufffwd
  | IDENT "have"; IDENT "suffices"; ssrhpats_nobs; ssrhavefwd
  | IDENT "have"; IDENT "suff"; ssrhpats_nobs; ssrhavefwd
  | IDENT "have"; ssrhavefwdwbinders
  | IDENT "unlock"; ssrunlockargs; ssrclauses
  | IDENT "ssrinstancesofruleR2L"; ssrterm
  | IDENT "ssrinstancesofruleL2R"; ssrterm
  | IDENT "congr"; ssrcongrarg
  | "by"; tactic
  | "by"; ssrhintarg
  | IDENT "multiset_solver"; "by"; ltac_expr LEVEL "3"
  | IDENT "multiset_solver"
  | IDENT "simplify_map_eq"; "/="; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_map_eq"; "/="
  | IDENT "simplify_map_eq"; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_map_eq"
  | IDENT "simpl_map"; "by"; ltac_expr LEVEL "3"
  | IDENT "simpl_map"
  | IDENT "firstorder"; OPT tactic; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using
  | IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "congruence"; OPT natural
  | IDENT "dintuition"; tactic
  | IDENT "dintuition"
  | IDENT "intuition"; tactic
  | IDENT "intuition"
  | IDENT "assert_fails"; ltac_expr LEVEL "3"
  | IDENT "inversion_sigma"; hyp; "as"; simple_intropattern
  | IDENT "inversion_sigma"; hyp
  | IDENT "inversion_sigma"
  | IDENT "now"; tactic
  | IDENT "rewrite_all"; "<-"; constr
  | IDENT "rewrite_all"; constr
  | IDENT "destruct_with_eqn"; ":"; ident; ident
  | IDENT "destruct_with_eqn"; ":"; ident; constr
  | IDENT "destruct_with_eqn"; ident
  | IDENT "destruct_with_eqn"; constr
  | IDENT "clearbody"; LIST1 hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp;
    hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp;
    hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp
  | IDENT "clear"; "-"; LIST1 hyp
  | IDENT "clear"; natural
  | IDENT "clear"; LIST0 hyp
  | IDENT "revert"; IDENT "select"; open_constr
  | IDENT "revert"; IDENT "dependent"; hyp
  | IDENT "revert"; LIST1 hyp
  | IDENT "rename"; IDENT "select"; open_constr; IDENT "into"; ident
  | IDENT "rename"; LIST1 rename SEP ","
  | IDENT "move"; ssrmovearg; ssrrpat
  | IDENT "move"; ssrmovearg; ssrclauses
  | IDENT "move"; ssrrpat
  | IDENT "move"; hyp; "at"; IDENT "top"
  | IDENT "move"; hyp; "at"; IDENT "bottom"
  | IDENT "move"; hyp; IDENT "after"; hyp
  | IDENT "move"; hyp; IDENT "before"; hyp
  | IDENT "move"
  | IDENT "intro"; "at"; IDENT "top"
  | IDENT "intro"; "at"; IDENT "bottom"
  | IDENT "intro"; IDENT "after"; hyp
  | IDENT "intro"; IDENT "before"; hyp
  | IDENT "intro"; ident; "at"; IDENT "top"
  | IDENT "intro"; ident; "at"; IDENT "bottom"
  | IDENT "intro"; ident; IDENT "after"; hyp
  | IDENT "intro"; ident; IDENT "before"; hyp
  | IDENT "intro"; ident
  | IDENT "intro"
  | IDENT "eexists"; LIST1 bindings SEP ","
  | IDENT "eexists"
  | "exists"; LIST1 bindings SEP ","
  | "exists"
  | IDENT "esplit"; "with"; bindings
  | IDENT "split"; "with"; bindings
  | IDENT "symmetry"; "in"; in_clause
  | IDENT "specialize"; constr_with_bindings; "as"; simple_intropattern
  | IDENT "specialize"; constr_with_bindings
  | IDENT "econstructor"; nat_or_var; "with"; bindings
  | IDENT "econstructor"; nat_or_var
  | IDENT "econstructor"
  | IDENT "constructor"; nat_or_var; "with"; bindings
  | IDENT "constructor"; nat_or_var
  | IDENT "constructor"
  | IDENT "eright"; "with"; bindings
  | IDENT "right"; "with"; bindings
  | IDENT "eleft"; "with"; bindings
  | IDENT "left"; "with"; bindings
  | IDENT "exact"; "<:"; lconstr
  | IDENT "exact"; ssrexactarg
  | IDENT "exact"; uconstr
  | IDENT "exact"
  | IDENT "with_strategy"; strategy_level_or_var; "["; LIST1 smart_global;
    "]"; ltac_expr LEVEL "3"
  | IDENT "guard"; test
  | IDENT "swap"; int_or_var; int_or_var
  | IDENT "cycle"; int_or_var
  | IDENT "unshelve"; ltac_expr LEVEL "1"
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"; "using"; ident
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"
  | IDENT "destauto"; "in"; hyp
  | IDENT "destauto"
  | IDENT "specialize_eqs"; hyp
  | IDENT "generalize_eqs_vars"; hyp
  | IDENT "generalize_eqs"; hyp
  | IDENT "stepr"; constr; "by"; tactic
  | IDENT "stepr"; constr
  | IDENT "stepl"; constr; "by"; tactic
  | IDENT "stepl"; constr
  | IDENT "instantiate"; "("; ident; ":="; lconstr; ")"
  | IDENT "instantiate"; "("; natural; ":="; lconstr; ")"; hloc
  | IDENT "evar"; test_lpar_id_colon; "("; ident; ":"; lconstr; ")"
  | IDENT "evar"; constr
  | IDENT "subst"; LIST1 hyp
  | IDENT "subst"
  | IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "refine"; uconstr
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause
  | IDENT "autorewrite"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "with"; LIST1 preident; clause
  | IDENT "contradiction"; OPT constr_with_bindings
  | IDENT "decompose"; "["; LIST1 constr; "]"; constr
  | IDENT "decompose"; IDENT "record"; constr
  | IDENT "decompose"; IDENT "sum"; constr
  | IDENT "einjection"; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg
  | IDENT "einjection"
  | IDENT "injection"; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg
  | IDENT "injection"
  | IDENT "ediscriminate"; destruction_arg
  | IDENT "ediscriminate"
  | IDENT "discriminate"; destruction_arg
  | IDENT "discriminate"
  | IDENT "esimplify_eq"; destruction_arg
  | IDENT "esimplify_eq"
  | IDENT "simplify_eq"; "/="
  | IDENT "simplify_eq"; destruction_arg
  | IDENT "simplify_eq"
  | IDENT "replace"; "<-"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "<-"; uconstr; clause
  | IDENT "replace"; "->"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "->"; uconstr; clause
  | IDENT "replace"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; uconstr; clause
  | IDENT "assert_succeeds"; ltac_expr LEVEL "3"
  | IDENT "unify"; constr; constr; "with"; preident
  | IDENT "unify"; constr; constr
  | IDENT "autounfold_one"; hintbases; "in"; hyp
  | IDENT "autounfold_one"; hintbases
  | IDENT "autounfold"; hintbases; clause
  | IDENT "info_eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "info_auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "trivial"; auto_using; hintbases
  | IDENT "info_trivial"; auto_using; hintbases
  | IDENT "trivial"; auto_using; hintbases
  | IDENT "autoapply"; constr; "with"; preident
  | IDENT "head_of_constr"; ident; constr
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var;
    "with"; LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var
  | IDENT "decide"; IDENT "equality"
  | IDENT "decide"; constr; "with"; constr
  | IDENT "setoid_transitivity"; constr
  | IDENT "setoid_etransitivity"
  | IDENT "setoid_symmetry"; "in"; hyp
  | IDENT "setoid_symmetry"
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences;
    "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp; "at";
    occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings
  | IDENT "substitute"; orient; constr_with_bindings
  | IDENT "rewrite_strat"; rewstrategy; "in"; hyp
  | IDENT "rewrite_strat"; rewstrategy
  | IDENT "rewrite_db"; preident; "in"; hyp
  | IDENT "rewrite_db"; preident
  | IDENT "finish_timing"; "("; string; ")"; OPT string
  | IDENT "finish_timing"; OPT string
  | IDENT "restart_timer"; OPT string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; IDENT "cutoff"; integer
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"
  | IDENT "reset"; IDENT "ltac"; IDENT "profile"
  | IDENT "stop"; IDENT "ltac"; IDENT "profiling"
  | IDENT "start"; IDENT "ltac"; IDENT "profiling"
  | IDENT "intros"; IDENT "until"; quantified_hypothesis
  | IDENT "intros"; ne_intropatterns
  | IDENT "intros"
  | IDENT "eintros"; ne_intropatterns
  | IDENT "eintros"
  | IDENT "apply"; "*"; constr
  | IDENT "apply"; "<-"; constr; "in"; hyp
  | IDENT "apply"; "<-"; constr
  | IDENT "apply"; "->"; constr; "in"; hyp
  | IDENT "apply"; "->"; constr
  | IDENT "apply"; ssrapplyarg
  | IDENT "apply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "apply"
  | IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "elim"; ssrarg; ssrclauses
  | IDENT "elim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "elim"
  | IDENT "eelim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "case"; ssrcasearg; ssrclauses
  | IDENT "case"; induction_clause_list
  | IDENT "case"
  | IDENT "ecase"; induction_clause_list
  | "fix"; ident; natural; "with"; LIST1 fixdecl
  | "fix"; ident; natural
  | "cofix"; ident; "with"; LIST1 cofixdecl
  | "cofix"; ident
  | IDENT "set"; ssrfwdid; ssrsetfwd; ssrclauses
  | IDENT "set"; bindings_with_parameters; clause
  | IDENT "set"; constr; as_name; clause
  | IDENT "eset"; bindings_with_parameters; clause
  | IDENT "eset"; constr; as_name; clause
  | IDENT "remember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "eremember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "assert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "assert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "assert"; constr; as_ipat; by_tactic
  | IDENT "eassert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "eassert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eassert"; constr; as_ipat; by_tactic
  | IDENT "pose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "pose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "pose"; ssrfixfwd
  | IDENT "pose"; ssrcofixfwd
  | IDENT "pose"; ssrfwdid; ssrposefwd
  | IDENT "pose"; bindings_with_parameters
  | IDENT "pose"; constr; as_name
  | IDENT "epose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "epose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "epose"; bindings_with_parameters
  | IDENT "epose"; constr; as_name
  | IDENT "enough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "enough"; constr; as_ipat; by_tactic
  | IDENT "eenough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eenough"; constr; as_ipat; by_tactic
  | IDENT "generalize"; IDENT "dependent"; constr
  | IDENT "generalize"; constr; LIST1 constr
  | IDENT "generalize"; constr; lookup_at_as_comma; occs; as_name;
    LIST0 [ ","; pattern_occ; as_name ]
  | IDENT "generalize"; constr
  | IDENT "induction"; induction_clause_list
  | IDENT "einduction"; induction_clause_list
  | IDENT "destruct"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "destruct"; IDENT "select"; open_constr
  | IDENT "destruct"; induction_clause_list
  | IDENT "edestruct"; induction_clause_list
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; "at"; occurrences;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; "in"; hyp;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; by_arg_tac
  | IDENT "rewrite"; ssrrwargs; ssrclauses
  | IDENT "rewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "erewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "dependent"; IDENT "destruction"; ident
  | IDENT "dependent"; IDENT "induction"; ident
  | IDENT "dependent"; IDENT "generalize_eqs_vars"; hyp
  | IDENT "dependent"; IDENT "generalize_eqs"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr; "in"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr
  | IDENT "dependent";
    [ IDENT "simple"; IDENT "inversion" | IDENT "inversion"
    | IDENT "inversion_clear" ]; quantified_hypothesis; as_or_and_ipat;
    OPT [ "with"; constr ]
  | IDENT "simple"; IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "simple"; IDENT "congruence"; OPT natural
  | IDENT "simple"; IDENT "destruct"; quantified_hypothesis
  | IDENT "simple"; IDENT "induction"; quantified_hypothesis
  | IDENT "simple"; IDENT "subst"
  | IDENT "simple"; IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "injection"; destruction_arg
  | IDENT "simple"; IDENT "injection"
  | IDENT "simple"; IDENT "apply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "inversion"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion_clear"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "inversion"; IDENT "select"; open_constr
  | IDENT "inversion"; quantified_hypothesis; "using"; constr; in_hyp_list
  | IDENT "inversion"; quantified_hypothesis; as_or_and_ipat; in_hyp_list
  | IDENT "red"; clause
  | IDENT "hnf"; clause
  | IDENT "simpl"; OPT [ IDENT "head" ]; delta_flag; OPT ref_or_pattern_occ;
    clause
  | IDENT "cbv"; strategy_flag; clause
  | IDENT "cbn"; strategy_flag; clause
  | IDENT "lazy"; strategy_flag; clause
  | IDENT "compute"; delta_flag; clause
  | IDENT "vm_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "native_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "unfold"; LIST1 unfold_occ SEP ","; clause
  | IDENT "fold"; LIST1 constr; clause
  | IDENT "pattern"; LIST1 pattern_occ SEP ","; clause
  | IDENT "change"; conversion; clause
  | IDENT "change_no_check"; conversion; clause ] ]

Entry tactic_value is
[ LEFTA
  [ IDENT "br_modifier"; ":"; "("; br_modifier; ")"
  | IDENT "br_value"; ":"; "("; br_value; ")"
  | IDENT "br_lemma"; ":"; "("; br_lemma; ")"
  | IDENT "br_with_db"; ":"; "("; br_with_db; ")"
  | IDENT "br_db_modifier"; ":"; "("; br_db_modifier; ")"
  | IDENT "br_opacity"; ":"; "("; br_opacity; ")"
  | IDENT "elpi_code_appArg"; ":"; "("; elpi_code_appArg; ")"
  | IDENT "ghost"; ":"; "("; ghost; ")"
  | IDENT "elpi_code"; ":"; "("; elpi_code; ")"
  | IDENT "ltac_attributes"; ":"; "("; ltac_attributes; ")"
  | IDENT "elpi_tactic_arg"; ":"; "("; elpi_tactic_arg; ")"
  | IDENT "elpi_cmd_arg"; ":"; "("; elpi_cmd_arg; ")"
  | IDENT "attributes"; ":"; "("; attributes; ")"
  | IDENT "elpi_loc"; ":"; "("; elpi_loc; ")"
  | IDENT "qualified_name"; ":"; "("; qualified_name; ")"
  | IDENT "elpi_string"; ":"; "("; elpi_string; ")"
  | IDENT "ltac2val"; ":"; "("; tac2expr_in_env; ")"
  | IDENT "ltac2"; ":"; "("; tac2expr_in_env; ")"
  | IDENT "ssr_idcomma"; ":"; "("; ssr_idcomma; ")"
  | IDENT "ssrwlogfwd"; ":"; "("; ssrwlogfwd; ")"
  | IDENT "ssrsufffwd"; ":"; "("; ssrsufffwd; ")"
  | IDENT "ssrunlockargs"; ":"; "("; ssrunlockargs; ")"
  | IDENT "ssrunlockarg"; ":"; "("; ssrunlockarg; ")"
  | IDENT "ssrrwargs"; ":"; "("; ssrrwargs; ")"
  | IDENT "ssrrwarg"; ":"; "("; ssrrwarg; ")"
  | IDENT "ssrpattern_ne_squarep"; ":"; "("; ssrpattern_ne_squarep; ")"
  | IDENT "ssrpattern_squarep"; ":"; "("; ssrpattern_squarep; ")"
  | IDENT "ssrrule"; ":"; "("; ssrrule; ")"
  | IDENT "ssrrule_ne"; ":"; "("; ssrrule_ne; ")"
  | IDENT "ssrrwocc"; ":"; "("; ssrrwocc; ")"
  | IDENT "ssrcongrarg"; ":"; "("; ssrcongrarg; ")"
  | IDENT "ssrexactarg"; ":"; "("; ssrexactarg; ")"
  | IDENT "ssrapplyarg"; ":"; "("; ssrapplyarg; ")"
  | IDENT "ssragens"; ":"; "("; ssragens; ")"
  | IDENT "ssragen"; ":"; "("; ssragen; ")"
  | IDENT "ssrcasearg"; ":"; "("; ssrcasearg; ")"
  | IDENT "ssrmovearg"; ":"; "("; ssrmovearg; ")"
  | IDENT "ssrarg"; ":"; "("; ssrarg; ")"
  | IDENT "ssreqid"; ":"; "("; ssreqid; ")"
  | IDENT "ssrdgens"; ":"; "("; ssrdgens; ")"
  | IDENT "ssrdgens_tl"; ":"; "("; ssrdgens_tl; ")"
  | IDENT "ssrgen"; ":"; "("; ssrgen; ")"
  | IDENT "ssrseqdir"; ":"; "("; ssrseqdir; ")"
  | IDENT "ssrseqarg"; ":"; "("; ssrseqarg; ")"
  | IDENT "ssrdoarg"; ":"; "("; ssrdoarg; ")"
  | IDENT "ssrhavefwdwbinders"; ":"; "("; ssrhavefwdwbinders; ")"
  | IDENT "ssrhavefwd"; ":"; "("; ssrhavefwd; ")"
  | IDENT "ssrsetfwd"; ":"; "("; ssrsetfwd; ")"
  | IDENT "ssrcofixfwd"; ":"; "("; ssrcofixfwd; ")"
  | IDENT "ssrfixfwd"; ":"; "("; ssrfixfwd; ")"
  | IDENT "ssrposefwd"; ":"; "("; ssrposefwd; ")"
  | IDENT "ssrstruct"; ":"; "("; ssrstruct; ")"
  | IDENT "ssrbinder"; ":"; "("; ssrbinder; ")"
  | IDENT "ssrbvar"; ":"; "("; ssrbvar; ")"
  | IDENT "ssrfwd"; ":"; "("; ssrfwd; ")"
  | IDENT "ssrclauses"; ":"; "("; ssrclauses; ")"
  | IDENT "ssrclausehyps"; ":"; "("; ssrclausehyps; ")"
  | IDENT "ssrwgen"; ":"; "("; ssrwgen; ")"
  | IDENT "ssrhint"; ":"; "("; ssrhint; ")"
  | IDENT "ssrortacarg"; ":"; "("; ssrortacarg; ")"
  | IDENT "ssrhint3arg"; ":"; "("; ssrhint3arg; ")"
  | IDENT "ssrhintarg"; ":"; "("; ssrhintarg; ")"
  | IDENT "ssrortacs"; ":"; "("; ssrortacs; ")"
  | IDENT "ssrfwdid"; ":"; "("; ssrfwdid; ")"
  | IDENT "ssrintrosarg"; ":"; "("; ssrintrosarg; ")"
  | IDENT "ssrintros"; ":"; "("; ssrintros; ")"
  | IDENT "ssrintros_ne"; ":"; "("; ssrintros_ne; ")"
  | IDENT "ssrrpat"; ":"; "("; ssrrpat; ")"
  | IDENT "ssrhpats_nobs"; ":"; "("; ssrhpats_nobs; ")"
  | IDENT "ssrhpats_wtransp"; ":"; "("; ssrhpats_wtransp; ")"
  | IDENT "ssrhpats"; ":"; "("; ssrhpats; ")"
  | IDENT "ssripats_ne"; ":"; "("; ssripats_ne; ")"
  | IDENT "ssrcpat"; ":"; "("; ssrcpat; ")"
  | IDENT "ssriorpat"; ":"; "("; ssriorpat; ")"
  | IDENT "ssripats"; ":"; "("; ssripats; ")"
  | IDENT "ssripat"; ":"; "("; ssripat; ")"
  | IDENT "ident_no_do"; ":"; "("; ident_no_do; ")"
  | IDENT "ssrfwdview"; ":"; "("; ssrfwdview; ")"
  | IDENT "ssrbwdview"; ":"; "("; ssrbwdview; ")"
  | IDENT "ast_closure_lterm"; ":"; "("; ast_closure_lterm; ")"
  | IDENT "ast_closure_term"; ":"; "("; ast_closure_term; ")"
  | IDENT "ssrterm"; ":"; "("; ssrterm; ")"
  | IDENT "ssrdocc"; ":"; "("; ssrdocc; ")"
  | IDENT "ssrmult"; ":"; "("; ssrmult; ")"
  | IDENT "ssrmult_ne"; ":"; "("; ssrmult_ne; ")"
  | IDENT "ssrocc"; ":"; "("; ssrocc; ")"
  | IDENT "ssrindex"; ":"; "("; ssrindex; ")"
  | IDENT "ssrclear"; ":"; "("; ssrclear; ")"
  | IDENT "ssrclear_ne"; ":"; "("; ssrclear_ne; ")"
  | IDENT "ssrsimpl_ne"; ":"; "("; ssrsimpl_ne; ")"
  | IDENT "ssrhoi_id"; ":"; "("; ssrhoi_id; ")"
  | IDENT "ssrhoi_hyp"; ":"; "("; ssrhoi_hyp; ")"
  | IDENT "ssrhyp"; ":"; "("; ssrhyp; ")"
  | IDENT "ssrtclarg"; ":"; "("; ssrtacarg; ")"
  | IDENT "ssrtac3arg"; ":"; "("; ssrtac3arg; ")"
  | IDENT "ssrtacarg"; ":"; "("; ssrtacarg; ")"
  | IDENT "ssrviewposspc"; ":"; "("; ssrviewpos; ")"
  | IDENT "ssrviewpos"; ":"; "("; ssrviewpos; ")"
  | IDENT "ssrhintref"; ":"; "("; ssrhintref; ")"
  | IDENT "ssrpatternarg"; ":"; "("; rpattern; ")"
  | IDENT "lcpattern"; ":"; "("; lcpattern; ")"
  | IDENT "cpattern"; ":"; "("; cpattern; ")"
  | IDENT "rpattern"; ":"; "("; rpattern; ")"
  | IDENT "firstorder_using"; ":"; "("; firstorder_using; ")"
  | IDENT "test"; ":"; "("; test; ")"
  | IDENT "comparison"; ":"; "("; comparison; ")"
  | IDENT "opthints"; ":"; "("; opthints; ")"
  | IDENT "auto_using"; ":"; "("; auto_using; ")"
  | IDENT "hintbases"; ":"; "("; hintbases; ")"
  | IDENT "eauto_search_strategy"; ":"; "("; eauto_search_strategy; ")"
  | IDENT "eauto_search_strategy_name"; ":"; "("; eauto_search_strategy_name;
    ")"
  | IDENT "debug"; ":"; "("; debug; ")"
  | IDENT "rewstrategy"; ":"; "("; rewstrategy; ")"
  | IDENT "glob_constr_with_bindings"; ":"; "("; constr_with_bindings; ")"
  | IDENT "strategy_level_or_var"; ":"; "("; strategy_level_or_var; ")"
  | IDENT "strategy_level"; ":"; "("; strategy_level; ")"
  | IDENT "test_lpar_id_colon"; ":"; "("; test_lpar_id_colon; ")"
  | IDENT "in_clause"; ":"; "("; in_clause; ")"
  | IDENT "by_arg_tac"; ":"; "("; by_arg_tac; ")"
  | IDENT "rename"; ":"; "("; rename; ")"
  | IDENT "hloc"; ":"; "("; hloc; ")"
  | IDENT "lglob"; ":"; "("; lconstr; ")"
  | IDENT "lconstr"; ":"; "("; lconstr; ")"
  | IDENT "glob"; ":"; "("; constr; ")"
  | IDENT "occurrences"; ":"; "("; occurrences; ")"
  | IDENT "natural"; ":"; "("; natural; ")"
  | IDENT "orient"; ":"; "("; orient; ")"
  | IDENT "ltac"; ":"; "("; ltac_expr LEVEL "5"; ")"
  | IDENT "open_constr"; ":"; "("; lconstr; ")"
  | IDENT "ipattern"; ":"; "("; simple_intropattern; ")"
  | IDENT "constr"; ":"; "("; lconstr; ")"
  | IDENT "uconstr"; ":"; "("; lconstr; ")"
  | IDENT "reference"; ":"; "("; reference; ")"
  | IDENT "ident"; ":"; "("; ident; ")"
  | IDENT "smart_global"; ":"; "("; smart_global; ")"
  | IDENT "string"; ":"; "("; string; ")"
  | IDENT "integer"; ":"; "("; integer; ")"
  | IDENT "fresh"; LIST0 fresh_id
  | IDENT "type_term"; uconstr
  | IDENT "numgoals"
  | constr_eval ] ]


<prompt>Rocq < 18 || 0 < </prompt>Timeout 1 Print LoadPath.
Logical Path / Physical path:
LF /home/abhishek/fv-workspace/BasicCoqTutorial
monad /home/abhishek/fv-workspace/_build/default/monad/monadproofs
monad.EVMOpSem /home/abhishek/fv-workspace/_build/default/monad/monadproofs/EVMOpSem
monad.EVMOpSem.Lem /home/abhishek/fv-workspace/_build/default/monad/monadproofs/EVMOpSem/Lem
monad.asts /home/abhishek/fv-workspace/_build/default/monad/monadproofs/asts
monad.fmai /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai
monad.fmai.driver /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/driver
monad.fmai.driver.ltac2 /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/driver/ltac2
monad.fmai.prompts /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/prompts
monad.proofs /home/abhishek/fv-workspace/_build/default/monad/monadproofs/proofs
monad.proofs.execproofs /home/abhishek/fv-workspace/_build/default/monad/monadproofs/proofs/execproofs
monad.tutorials /home/abhishek/fv-workspace/_build/default/monad/monadproofs/tutorials
monad /home/abhishek/fv-workspace/monad/monadproofs
monad.EVMOpSem /home/abhishek/fv-workspace/monad/monadproofs/EVMOpSem
monad.EVMOpSem.Lem /home/abhishek/fv-workspace/monad/monadproofs/EVMOpSem/Lem
monad.asts /home/abhishek/fv-workspace/monad/monadproofs/asts
monad.fmai /home/abhishek/fv-workspace/monad/monadproofs/fmai
monad.fmai.driver /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver
monad.fmai.driver.elisp /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver/elisp
monad.fmai.driver.ltac2 /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver/ltac2
monad.fmai.prompts /home/abhishek/fv-workspace/monad/monadproofs/fmai/prompts
monad.proofs /home/abhishek/fv-workspace/monad/monadproofs/proofs
monad.proofs.execproofs /home/abhishek/fv-workspace/monad/monadproofs/proofs/execproofs
monad.tutorials /home/abhishek/fv-workspace/monad/monadproofs/tutorials
bluerock.ltac2.llm /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm
bluerock.ltac2.llm.plugin /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/plugin
bluerock.ltac2.llm.theories /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/theories
bedrocktest /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/tests
Ltac2 /home/abhishek/fv-workspace/fmdeps/coq/user-contrib/Ltac2
Ltac2.Compat /home/abhishek/fv-workspace/fmdeps/coq/user-contrib/Ltac2/Compat
Corelib /home/abhishek/fv-workspace/fmdeps/coq/theories
Corelib.Array /home/abhishek/fv-workspace/fmdeps/coq/theories/Array
Corelib.BinNums /home/abhishek/fv-workspace/fmdeps/coq/theories/BinNums
Corelib.Classes /home/abhishek/fv-workspace/fmdeps/coq/theories/Classes
Corelib.Compat /home/abhishek/fv-workspace/fmdeps/coq/theories/Compat
Corelib.Floats /home/abhishek/fv-workspace/fmdeps/coq/theories/Floats
Corelib.Init /home/abhishek/fv-workspace/fmdeps/coq/theories/Init
Corelib.Lists /home/abhishek/fv-workspace/fmdeps/coq/theories/Lists
Corelib.Numbers /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers
Corelib.Numbers.Cyclic /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers/Cyclic
Corelib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers/Cyclic/Int63
Corelib.Program /home/abhishek/fv-workspace/fmdeps/coq/theories/Program
Corelib.Relations /home/abhishek/fv-workspace/fmdeps/coq/theories/Relations
Corelib.Setoids /home/abhishek/fv-workspace/fmdeps/coq/theories/Setoids
Corelib.Strings /home/abhishek/fv-workspace/fmdeps/coq/theories/Strings
Corelib.derive /home/abhishek/fv-workspace/fmdeps/coq/theories/derive
Corelib.extraction /home/abhishek/fv-workspace/fmdeps/coq/theories/extraction
Corelib.ssr /home/abhishek/fv-workspace/fmdeps/coq/theories/ssr
Corelib.ssrmatching /home/abhishek/fv-workspace/fmdeps/coq/theories/ssrmatching
Corelib /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories
Corelib.Array /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Array
Corelib.BinNums /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/BinNums
Corelib.Classes /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Classes
Corelib.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Compat
Corelib.Floats /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Floats
Corelib.Init /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Init
Corelib.Lists /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Lists
Corelib.Numbers /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers
Corelib.Numbers.Cyclic /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers/Cyclic
Corelib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers/Cyclic/Int63
Corelib.Program /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Program
Corelib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Relations
Corelib.Setoids /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Setoids
Corelib.Strings /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Strings
Corelib.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/derive
Corelib.extraction /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/extraction
Corelib.ssr /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/ssr
Corelib.ssrmatching /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/ssrmatching
stdpp /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp
stdpp /home/abhishek/fv-workspace/_build/default/fmdeps/stdpp/stdpp
stdpp.bitvector /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp_bitvector
stdpp.unstable /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp_unstable
Stdlib /home/abhishek/fv-workspace/fmdeps/stdlib/theories
Stdlib.All /home/abhishek/fv-workspace/fmdeps/stdlib/theories/All
Stdlib.Arith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Arith
Stdlib.Array /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Array
Stdlib.BinNums /home/abhishek/fv-workspace/fmdeps/stdlib/theories/BinNums
Stdlib.Bool /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Bool
Stdlib.Classes /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Classes
Stdlib.Compat /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Compat
Stdlib.FSets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/FSets
Stdlib.Floats /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Floats
Stdlib.Init /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Init
Stdlib.Lists /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Lists
Stdlib.Logic /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Logic
Stdlib.MSets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/MSets
Stdlib.NArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/NArith
Stdlib.Numbers /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers
Stdlib.Numbers.Cyclic /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic
Stdlib.Numbers.Cyclic.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic/Abstract
Stdlib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic/Int63
Stdlib.Numbers.Integer /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer
Stdlib.Numbers.Integer.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/Abstract
Stdlib.Numbers.Integer.Binary /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/Binary
Stdlib.Numbers.Integer.NatPairs /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/NatPairs
Stdlib.Numbers.NatInt /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/NatInt
Stdlib.Numbers.Natural /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural
Stdlib.Numbers.Natural.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural/Abstract
Stdlib.Numbers.Natural.Binary /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural/Binary
Stdlib.PArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/PArith
Stdlib.Program /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Program
Stdlib.QArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/QArith
Stdlib.Reals /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals
Stdlib.Reals.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals/Abstract
Stdlib.Reals.Cauchy /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals/Cauchy
Stdlib.Relations /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Relations
Stdlib.Setoids /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Setoids
Stdlib.Sets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Sets
Stdlib.Sorting /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Sorting
Stdlib.Streams /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Streams
Stdlib.Strings /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Strings
Stdlib.Structures /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Structures
Stdlib.Unicode /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Unicode
Stdlib.Vectors /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Vectors
Stdlib.Wellfounded /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Wellfounded
Stdlib.ZArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ZArith
Stdlib.btauto /home/abhishek/fv-workspace/fmdeps/stdlib/theories/btauto
Stdlib.derive /home/abhishek/fv-workspace/fmdeps/stdlib/theories/derive
Stdlib.extraction /home/abhishek/fv-workspace/fmdeps/stdlib/theories/extraction
Stdlib.funind /home/abhishek/fv-workspace/fmdeps/stdlib/theories/funind
Stdlib.micromega /home/abhishek/fv-workspace/fmdeps/stdlib/theories/micromega
Stdlib.nsatz /home/abhishek/fv-workspace/fmdeps/stdlib/theories/nsatz
Stdlib.omega /home/abhishek/fv-workspace/fmdeps/stdlib/theories/omega
Stdlib.rtauto /home/abhishek/fv-workspace/fmdeps/stdlib/theories/rtauto
Stdlib.setoid_ring /home/abhishek/fv-workspace/fmdeps/stdlib/theories/setoid_ring
Stdlib.ssr /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ssr
Stdlib.ssrmatching /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ssrmatching
Stdlib /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories
Stdlib.All /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/All
Stdlib.Arith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Arith
Stdlib.Array /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Array
Stdlib.BinNums /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/BinNums
Stdlib.Bool /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Bool
Stdlib.Classes /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Classes
Stdlib.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Compat
Stdlib.FSets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/FSets
Stdlib.Floats /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Floats
Stdlib.Init /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Init
Stdlib.Lists /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Lists
Stdlib.Logic /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Logic
Stdlib.MSets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/MSets
Stdlib.NArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/NArith
Stdlib.Numbers /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers
Stdlib.Numbers.Cyclic /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic
Stdlib.Numbers.Cyclic.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic/Abstract
Stdlib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic/Int63
Stdlib.Numbers.Integer /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer
Stdlib.Numbers.Integer.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/Abstract
Stdlib.Numbers.Integer.Binary /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/Binary
Stdlib.Numbers.Integer.NatPairs /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/NatPairs
Stdlib.Numbers.NatInt /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/NatInt
Stdlib.Numbers.Natural /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural
Stdlib.Numbers.Natural.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural/Abstract
Stdlib.Numbers.Natural.Binary /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural/Binary
Stdlib.PArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/PArith
Stdlib.Program /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Program
Stdlib.QArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/QArith
Stdlib.Reals /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals
Stdlib.Reals.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals/Abstract
Stdlib.Reals.Cauchy /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals/Cauchy
Stdlib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Relations
Stdlib.Setoids /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Setoids
Stdlib.Sets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Sets
Stdlib.Sorting /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Sorting
Stdlib.Streams /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Streams
Stdlib.Strings /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Strings
Stdlib.Structures /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Structures
Stdlib.Unicode /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Unicode
Stdlib.Vectors /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Vectors
Stdlib.Wellfounded /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Wellfounded
Stdlib.ZArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ZArith
Stdlib.btauto /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/btauto
Stdlib.derive /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/derive
Stdlib.extraction /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/extraction
Stdlib.funind /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/funind
Stdlib.micromega /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/micromega
Stdlib.nsatz /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/nsatz
Stdlib.omega /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/omega
Stdlib.rtauto /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/rtauto
Stdlib.setoid_ring /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/setoid_ring
Stdlib.ssr /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ssr
Stdlib.ssrmatching /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ssrmatching
bluerock.nova_interface /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories
bluerock.nova_interface.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64
bluerock.nova_interface.aarch64.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/opsem
bluerock.nova_interface.aarch64.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/wp_nova
bluerock.nova_interface.hypercall /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/hypercall
bluerock.nova_interface.machine_logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/machine_logic
bluerock.nova_interface.model /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/model
bluerock.nova_interface.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/opsem
bluerock.nova_interface.predicates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/predicates
bluerock.nova_interface.upstream /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/upstream
bluerock.nova_interface.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/wp_nova
bluerock.nova_interface.x86_64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64
bluerock.nova_interface.x86_64.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/opsem
bluerock.nova_interface.x86_64.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/wp_nova
bluerock.elpi.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp
bluerock.elpi.cpp.Command /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Command
bluerock.elpi.cpp.Program /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Program
bluerock.elpi.cpp.Program.interp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Program/interp
bluerock.elpi.cpp.Tactic /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Tactic
bluerock.elpi.cpp.internal /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/internal
bluerock.elpi.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp
bluerock.elpi.cpp.Command /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Command
bluerock.elpi.cpp.Program /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Program
bluerock.elpi.cpp.Program.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Program/interp
bluerock.elpi.cpp.Tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Tactic
bluerock.elpi.cpp.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/internal
bluerock_tests.elpi.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/tests
bluerock /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories
bluerock.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/algebra
bluerock.auto /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto
bluerock.auto.big_sep /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/big_sep
bluerock.auto.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp
bluerock.auto.cpp.auto_frac /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/auto_frac
bluerock.auto.cpp.database /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/database
bluerock.auto.cpp.default_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/default_spec
bluerock.auto.cpp.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi
bluerock.auto.cpp.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/derive
bluerock.auto.cpp.elpi.enum /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum
bluerock.auto.cpp.elpi.enum.variant /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum/variant
bluerock.auto.cpp.elpi.synth /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth
bluerock.auto.cpp.elpi.synth.both /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/both
bluerock.auto.cpp.elpi.synth.interp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp
bluerock.auto.cpp.elpi.synth.interp.model
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/model
bluerock.auto.cpp.elpi.synth.interp.rep
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/rep
bluerock.auto.cpp.elpi.synth.synterp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp
bluerock.auto.cpp.elpi.synth.synterp.rep
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp/rep
bluerock.auto.cpp.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints
bluerock.auto.cpp.hints.ptrs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints/ptrs
bluerock.auto.cpp.pretty /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/pretty
bluerock.auto.cpp.specs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/specs
bluerock.auto.cpp.templates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates
bluerock.auto.cpp.templates.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/hints
bluerock.auto.cpp.templates.logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/logic
bluerock.auto.cpp.templates.semantics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/semantics
bluerock.auto.cpp.templates.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/spec
bluerock.auto.cpp.templates.syntax /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/syntax
bluerock.auto.cpp.templates.upstream /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream
bluerock.auto.cpp.templates.upstream.ast
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/ast
bluerock.auto.cpp.templates.upstream.bi
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/bi
bluerock.auto.cpp.templates.upstream.brick
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/brick
bluerock.auto.cpp.templates.upstream.prelude
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/prelude
bluerock.auto.cpp.templates.verif /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/verif
bluerock.auto.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi
bluerock.auto.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi/derive
bluerock.auto.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/hints
bluerock.auto.lemmas /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/lemmas
bluerock.auto.pure /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/pure
bluerock.auto.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/tactics
bluerock.base_logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic
bluerock.base_logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic/lib
bluerock.bi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/bi
bluerock.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp
bluerock.cpp.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp/spec
bluerock.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/lib
bluerock.micromega /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/micromega
bluerock.prelude /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude
bluerock.prelude.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/elpi
bluerock.prelude.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics
bluerock.prelude.tactics.ltac2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics/ltac2
bluerock.proofmode /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode
bluerock.proofmode.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode/cpp
bluerock /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories
bluerock.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/algebra
bluerock.auto /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto
bluerock.auto.big_sep /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/big_sep
bluerock.auto.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp
bluerock.auto.cpp.auto_frac /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/auto_frac
bluerock.auto.cpp.database /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/database
bluerock.auto.cpp.default_spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/default_spec
bluerock.auto.cpp.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi
bluerock.auto.cpp.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/derive
bluerock.auto.cpp.elpi.enum /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum
bluerock.auto.cpp.elpi.enum.variant
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum/variant
bluerock.auto.cpp.elpi.synth /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth
bluerock.auto.cpp.elpi.synth.both
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/both
bluerock.auto.cpp.elpi.synth.interp
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp
bluerock.auto.cpp.elpi.synth.interp.model
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/model
bluerock.auto.cpp.elpi.synth.interp.rep
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/rep
bluerock.auto.cpp.elpi.synth.synterp
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp
bluerock.auto.cpp.elpi.synth.synterp.rep
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp/rep
bluerock.auto.cpp.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints
bluerock.auto.cpp.hints.ptrs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints/ptrs
bluerock.auto.cpp.pretty /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/pretty
bluerock.auto.cpp.specs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/specs
bluerock.auto.cpp.templates /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates
bluerock.auto.cpp.templates.hints
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/hints
bluerock.auto.cpp.templates.logic
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/logic
bluerock.auto.cpp.templates.semantics
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/semantics
bluerock.auto.cpp.templates.spec
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/spec
bluerock.auto.cpp.templates.syntax
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/syntax
bluerock.auto.cpp.templates.upstream
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream
bluerock.auto.cpp.templates.upstream.ast
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/ast
bluerock.auto.cpp.templates.upstream.bi
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/bi
bluerock.auto.cpp.templates.upstream.brick
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/brick
bluerock.auto.cpp.templates.upstream.prelude
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/prelude
bluerock.auto.cpp.templates.verif
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/verif
bluerock.auto.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi
bluerock.auto.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi/derive
bluerock.auto.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/hints
bluerock.auto.lemmas /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/lemmas
bluerock.auto.pure /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/pure
bluerock.auto.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/tactics
bluerock.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic
bluerock.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic/lib
bluerock.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/bi
bluerock.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp
bluerock.cpp.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp/spec
bluerock.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/lib
bluerock.micromega /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/micromega
bluerock.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude
bluerock.prelude.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/elpi
bluerock.prelude.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics
bluerock.prelude.tactics.ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics/ltac2
bluerock.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode
bluerock.proofmode.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode/cpp
bluerock_auto.tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests
bluerock_auto.tests.anonymous_union /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/anonymous_union
bluerock_auto.tests.arch_indep /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep
bluerock_auto.tests.arch_indep.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep/aarch64
bluerock_auto.tests.arch_indep.x86_64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep/x86_64
bluerock_auto.tests.arith /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arith
bluerock_auto.tests.array /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/array
bluerock_auto.tests.ast /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/ast
bluerock_auto.tests.brick_eval /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/brick_eval
bluerock_auto.tests.brick_eval.bad /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/brick_eval/bad
bluerock_auto.tests.casts /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/casts
bluerock_auto.tests.const /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/const
bluerock_auto.tests.constants /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/constants
bluerock_auto.tests.control_flow /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/control_flow
bluerock_auto.tests.cpp_proof /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/cpp_proof
bluerock_auto.tests.cpp_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/cpp_spec
bluerock_auto.tests.data_class /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/data_class
bluerock_auto.tests.dataclass_demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/dataclass_demo
bluerock_auto.tests.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/derive
bluerock_auto.tests.duck_types /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/duck_types
bluerock_auto.tests.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi
bluerock_auto.tests.elpi.enums /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi/enums
bluerock_auto.tests.elpi.specifications /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi/specifications
bluerock_auto.tests.fields /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/fields
bluerock_auto.tests.fupd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/fupd
bluerock_auto.tests.inc /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inc
bluerock_auto.tests.includes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/includes
bluerock_auto.tests.inheritence /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inheritence
bluerock_auto.tests.inits /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inits
bluerock_auto.tests.io /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/io
bluerock_auto.tests.lambda /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lambda
bluerock_auto.tests.lazy_unfold /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lazy_unfold
bluerock_auto.tests.lib_alloc /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lib_alloc
bluerock_auto.tests.llist /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/llist
bluerock_auto.tests.llist_cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/llist_cpp
bluerock_auto.tests.local_scope /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/local_scope
bluerock_auto.tests.micromega /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/micromega
bluerock_auto.tests.misc_tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/misc_tests
bluerock_auto.tests.new_delete /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/new_delete
bluerock_auto.tests.operator_auto /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/operator_auto
bluerock_auto.tests.params /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/params
bluerock_auto.tests.perf /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/perf
bluerock_auto.tests.pretty /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/pretty
bluerock_auto.tests.read_prim /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/read_prim
bluerock_auto.tests.reps /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/reps
bluerock_auto.tests.return_void /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/return_void
bluerock_auto.tests.simple /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/simple
bluerock_auto.tests.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/spec
bluerock_auto.tests.specify /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify
bluerock_auto.tests.specify.challenge /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify/challenge
bluerock_auto.tests.specify.copymove /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify/copymove
bluerock_auto.tests.specify_cmd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify_cmd
bluerock_auto.tests.static_methods /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/static_methods
bluerock_auto.tests.synth_names /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/synth_names
bluerock_auto.tests.tactics4 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/tactics4
bluerock_auto.tests.templates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/templates
bluerock_auto.tests.union /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/union
bluerock_auto.tests.universes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/universes
bluerock_auto.tests.unlocked /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/unlocked
bluerock_auto.tests.val_cat /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/val_cat
bluerock_auto.tests.validate_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/validate_spec
bluerock_auto.tests.var_args /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/var_args
bluerock_auto.tests.virtual /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/virtual
bluerock_auto.tests.virtual.mdc_noimpl /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/virtual/mdc_noimpl
bluerock.hw_models.gic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/gic
bluerock.hw_models.cpu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu
bluerock.hw_models.cpu.inst /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/inst
bluerock.hw_models.cpu.inst.sail /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/inst/sail
bluerock.hw_models.cpu.msr /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/msr
bluerock.hw_models.core /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core
bluerock.hw_models.core.ip /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core/ip
bluerock_auto_core.examples /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples
bluerock_auto_core.examples.classes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples/classes
bluerock_auto_core.examples.tutorial /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples/tutorial
bluerock.auto.core /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories
bluerock.auto.core.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints
bluerock.auto.core.hints.classes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/classes
bluerock.auto.core.hints.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/lib
bluerock.auto.core.internal /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal
bluerock.auto.core.internal.VM /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/VM
bluerock.auto.core.internal.instr /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/instr
bluerock.auto.core.internal.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/lib
bluerock.auto.core.internal.ltac2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/ltac2
bluerock.auto.core.internal.plib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plib
bluerock.auto.core.internal.plugins /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plugins
bluerock.auto.core.internal.syntactic_bi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi
bluerock.auto.core.internal.syntactic_bi.forced
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi/forced
bluerock.auto.core.internal.tactic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/tactic
bluerock.auto.core /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories
bluerock.auto.core.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints
bluerock.auto.core.hints.classes /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/classes
bluerock.auto.core.hints.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/lib
bluerock.auto.core.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal
bluerock.auto.core.internal.VM /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/VM
bluerock.auto.core.internal.instr /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/instr
bluerock.auto.core.internal.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/lib
bluerock.auto.core.internal.ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/ltac2
bluerock.auto.core.internal.plib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plib
bluerock.auto.core.internal.plugins /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plugins
bluerock.auto.core.internal.syntactic_bi
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi
bluerock.auto.core.internal.syntactic_bi.forced
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi/forced
bluerock.auto.core.internal.tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/tactic
bluerock_auto_core.tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests
bluerock_auto_core.tests.cancelx /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/cancelx
bluerock_auto_core.tests.fwd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/fwd
bluerock_auto_core.tests.id /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/id
bluerock_auto_core.tests.learn /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/learn
bluerock_auto_core.tests.observe /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/observe
bluerock.cpp.demo /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof
bluerock.cpp.demo.aggregate01 /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/aggregate01
bluerock.cpp.demo.basic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/basic
bluerock.cpp.demo.data_class /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/data_class
bluerock.cpp.demo.inline /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/inline
bluerock.cpp.demo.loops /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/loops
bluerock.lts_adequacy_demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories
bluerock.lts_adequacy_demo.example /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example
bluerock.lts_adequacy_demo.example.apps /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/apps
bluerock.lts_adequacy_demo.example.languages /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/languages
bluerock.lts_adequacy_demo.example.logics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/logics
bluerock.lts_adequacy_demo.example.lts /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/lts
bluerock.lts_adequacy_demo.example.programs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/programs
bluerock.lts_adequacy_demo.iris /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/iris
bluerock.lts_adequacy_demo.refinement /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/refinement
bluerock.cpp.stdlib /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories
bluerock.cpp.stdlib.allocator /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/allocator
bluerock.cpp.stdlib.atomic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/atomic
bluerock.cpp.stdlib.cassert /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/cassert
bluerock.cpp.stdlib.concepts /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/concepts
bluerock.cpp.stdlib.exception /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/exception
bluerock.cpp.stdlib.new /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/new
bluerock.cpp.stdlib.vector /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/vector
bluerock.cpp.stdlib.test /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests
bluerock.cpp.stdlib.test.atomic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/atomic
bluerock.cpp.stdlib.test.concepts /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/concepts
bluerock.cpp.stdlib.test.vector /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/vector
bluerock.hw_models /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories
bluerock.hw_models.computer2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/computer2
bluerock.hw_models.demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/demo
bluerock.hw_models.mmu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/mmu
bluerock.hw_models.smmu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/smmu
bluerock.hw_models.smmu.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/smmu/aarch64
Equations.TestSuite /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite
Equations.TestSuite.HoTT /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/HoTT
Equations.TestSuite.disabled /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/disabled
Equations.TestSuite.issues /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/issues
Equations.Examples /home/abhishek/fv-workspace/fmdeps/coq-equations/examples
Equations.Examples.disabled /home/abhishek/fv-workspace/fmdeps/coq-equations/examples/disabled
Equations /home/abhishek/fv-workspace/fmdeps/coq-equations/theories
Equations.HoTT /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/HoTT
Equations.Type /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/Type
Equations /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories
Equations.Type /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories/Type
Equations.Prop /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/Prop
Equations.Prop /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories/Prop
elpi.apps.coercion /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/coercion/theories
elpi.apps.coercion.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/coercion/tests
elpi.apps.locker.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/elpi
elpi.apps.locker /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/locker/theories
elpi.apps.locker /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/theories
elpi.apps.locker.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/locker/tests
elpi.apps.derive.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/elpi
elpi.apps.derive.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/examples
elpi.apps.derive /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/theories
elpi.apps.derive.derive /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/theories/derive
elpi.apps.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/theories
elpi.apps.derive.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/theories/derive
elpi.apps.derive.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/tests
elpi.apps.tc /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/theories
elpi.apps.tc.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests
elpi.apps.tc.tests.WIP /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/WIP
elpi.apps.tc.tests.WIP.premisesSort /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/WIP/premisesSort
elpi.apps.tc.tests.importOrder /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/importOrder
elpi.apps.tc.tests.register /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/register
elpi.apps.cs /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/cs/theories
elpi.apps.eltac.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/examples
elpi.apps.eltac /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/theories
elpi.apps.eltac.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/tests
elpi.apps.NES.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/elpi
elpi.apps.NES.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/examples
elpi.apps.NES /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/theories
elpi.apps.NES /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/theories
elpi.apps.NES.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/tests
elpi_elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/elpi
elpi_examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/examples
elpi /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories
elpi.attic /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/attic
elpi.core /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/core
elpi.wip /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/wip
elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/theories
elpi.core /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/theories/core
elpi.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/tests
iris.unstable /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable
iris.unstable.algebra /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/algebra
iris.unstable.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/base_logic
iris.unstable.heap_lang /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/heap_lang
iris.deprecated /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated
iris.deprecated.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated/base_logic
iris.deprecated.program_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated/program_logic
iris.heap_lang /home/abhishek/fv-workspace/fmdeps/iris/iris_heap_lang
iris.heap_lang.lib /home/abhishek/fv-workspace/fmdeps/iris/iris_heap_lang/lib
iris /home/abhishek/fv-workspace/fmdeps/iris/iris
iris.algebra /home/abhishek/fv-workspace/fmdeps/iris/iris/algebra
iris.algebra.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/algebra/lib
iris.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/base_logic
iris.base_logic.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/base_logic/lib
iris.bi /home/abhishek/fv-workspace/fmdeps/iris/iris/bi
iris.bi.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/bi/lib
iris.prelude /home/abhishek/fv-workspace/fmdeps/iris/iris/prelude
iris.program_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/program_logic
iris.proofmode /home/abhishek/fv-workspace/fmdeps/iris/iris/proofmode
iris.si_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/si_logic
iris /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris
iris.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/algebra
iris.algebra.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/algebra/lib
iris.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/base_logic
iris.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/base_logic/lib
iris.bi /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/bi
iris.bi.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/bi/lib
iris.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/prelude
iris.program_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/program_logic
iris.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/proofmode
iris.si_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/si_logic
AAC_tactics /home/abhishek/fv-workspace/fmdeps/aac-tactics/theories
AAC_tactics /home/abhishek/fv-workspace/_build/default/fmdeps/aac-tactics/theories
ExtLibExamples /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/examples
ExtLib /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories
ExtLib.Core /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Core
ExtLib.Data /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data
ExtLib.Data.Eq /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Eq
ExtLib.Data.Graph /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Graph
ExtLib.Data.Map /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Map
ExtLib.Data.Monads /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Monads
ExtLib.Data.Set /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Set
ExtLib.Generic /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Generic
ExtLib.Programming /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Programming
ExtLib.Recur /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Recur
ExtLib.Relations /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Relations
ExtLib.Structures /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Structures
ExtLib.Tactics /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Tactics
ExtLib /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories
ExtLib.Core /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Core
ExtLib.Data /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data
ExtLib.Data.Eq /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Eq
ExtLib.Data.Graph /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Graph
ExtLib.Data.Map /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Map
ExtLib.Data.Monads /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Monads
ExtLib.Data.Set /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Set
ExtLib.Generic /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Generic
ExtLib.Programming /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Programming
ExtLib.Recur /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Recur
ExtLib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Relations
ExtLib.Structures /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Structures
ExtLib.Tactics /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Tactics
bluerock.prelude /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories
bluerock.prelude.arith /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/arith
bluerock.prelude.axioms /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/axioms
bluerock.prelude.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi
bluerock.prelude.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi/derive
bluerock.prelude.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/tactics
bluerock.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories
bluerock.prelude.arith /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/arith
bluerock.prelude.axioms /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/axioms
bluerock.prelude.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi
bluerock.prelude.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi/derive
bluerock.prelude.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/tactics
Lens /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-lens/Lens
Lens.Elpi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-lens/Lens/Elpi
Lens /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-lens/Lens
Lens.Elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-lens/Lens/Elpi
bluerock.ltac2.llm /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-llm/theories
bluerock.ltac2.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/theories
bluerock.ltac2.extra.internal /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/theories/internal
bluerock.ltac2.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/theories
bluerock.ltac2.extra.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/theories/internal
bluerock_tests.ltac2.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/tests
bluerock_tests.ltac2.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/tests
bluerock.iris.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories
bluerock.iris.extra.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/algebra
bluerock.iris.extra.base_logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic
bluerock.iris.extra.base_logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic/lib
bluerock.iris.extra.bi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi
bluerock.iris.extra.bi.spec /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi/spec
bluerock.iris.extra.proofmode /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/proofmode
bluerock.iris.extra.si_logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/si_logic
bluerock.iris.extra.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/tactics
bluerock.iris.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories
bluerock.iris.extra.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/algebra
bluerock.iris.extra.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic
bluerock.iris.extra.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic/lib
bluerock.iris.extra.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi
bluerock.iris.extra.bi.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi/spec
bluerock.iris.extra.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/proofmode
bluerock.iris.extra.si_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/si_logic
bluerock.iris.extra.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/tactics
bluerock.ltac2.logger /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-logger/theories
bluerock.ltac2.logger /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-logger/theories
accumulate_bug /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/accumulate_bug
accumulate_bug /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/accumulate_bug
bluerock.elpi.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra
bluerock.elpi.extra.Command /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Command
bluerock.elpi.extra.Command.both /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Command/both
bluerock.elpi.extra.Program /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program
bluerock.elpi.extra.Program.both /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program/both
bluerock.elpi.extra.Program.interp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program/interp
bluerock.elpi.extra.Tactic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Tactic
bluerock.elpi.extra.TacticCommand /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand
bluerock.elpi.extra.TacticCommand.interp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand/interp
bluerock.elpi.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra
bluerock.elpi.extra.Command /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Command
bluerock.elpi.extra.Command.both /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Command/both
bluerock.elpi.extra.Program /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program
bluerock.elpi.extra.Program.both /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program/both
bluerock.elpi.extra.Program.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program/interp
bluerock.elpi.extra.Tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Tactic
bluerock.elpi.extra.TacticCommand /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand
bluerock.elpi.extra.TacticCommand.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand/interp
bluerock_tests.elpi.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/tests
bluerock_tests.elpi.extra.NES /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/tests/NES
bluerock_tests.elpi.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/tests
bluerock_tests.elpi.extra.NES /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/tests/NES
bluerock.noimport /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport
bluerock.noimport.doc /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc
bluerock.noimport.doc.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc/cpp
bluerock.noimport /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport
bluerock.noimport.doc /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc
bluerock.noimport.doc.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc/cpp
bluerock.lang.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp
bluerock.lang.cpp.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/algebra
bluerock.lang.cpp.bi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi
bluerock.lang.cpp.bi.spec /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi/spec
bluerock.lang.cpp.logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic
bluerock.lang.cpp.logic.heap_pred /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/heap_pred
bluerock.lang.cpp.logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/lib
bluerock.lang.cpp.model /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/model
bluerock.lang.cpp.mparser /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/mparser
bluerock.lang.cpp.parser /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser
bluerock.lang.cpp.parser.plugin /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser/plugin
bluerock.lang.cpp.semantics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/semantics
bluerock.lang.cpp.specs /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/specs
bluerock.lang.cpp.syntax /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax
bluerock.lang.cpp.syntax.name_notation
  /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax/name_notation
bluerock.lang.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp
bluerock.lang.cpp.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/algebra
bluerock.lang.cpp.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi
bluerock.lang.cpp.bi.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi/spec
bluerock.lang.cpp.logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic
bluerock.lang.cpp.logic.heap_pred
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/heap_pred
bluerock.lang.cpp.logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/lib
bluerock.lang.cpp.model /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/model
bluerock.lang.cpp.mparser /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/mparser
bluerock.lang.cpp.parser /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser
bluerock.lang.cpp.parser.plugin
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser/plugin
bluerock.lang.cpp.semantics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/semantics
bluerock.lang.cpp.specs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/specs
bluerock.lang.cpp.syntax /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax
bluerock.lang.cpp.syntax.name_notation
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax/name_notation
tc_db_info /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-tc-db-info/theories
tc_db_info /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-tc-db-info/theories
bluerock.upoly /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-upoly/upoly
bluerock.upoly /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-upoly/upoly
<> /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib
Ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib/Ltac2
Ltac2.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib/Ltac2/Compat

<prompt>Rocq < 19 || 0 < </prompt>Print Stmt.
Notation Stmt := Stmt

Inductive name' : Set :=
    Ninst : name → list temp_arg → name
  | Nglobal : atomic_name → name
  | Ndependent : type → name
  | Nscoped : name → atomic_name → name
  | Nunsupported : string → name
  with temp_arg' : Set :=
    Atype : type → temp_arg
  | Avalue : Expr → temp_arg
  | Apack : list temp_arg → temp_arg
  | Atemplate : name → temp_arg
  | Aunsupported : string → temp_arg
  with type' : Set :=
    Tparam : ident → type
  | Tresult_param : ident → type
  | Tresult_global : name → type
  | Tresult_unop : RUnOp → type → type
  | Tresult_binop : RBinOp → type → type → type
  | Tresult_call : name → list type → type
  | Tresult_member_call : name → type → list type → type
  | Tresult_parenlist : type → list type → type
  | Tresult_member : type → name → type
  | Tptr : type → type
  | Tref : type → type
  | Trv_ref : type → type
  | Tnum : int_rank → signed → type
  | Tchar_ : char_type → type
  | Tvoid : type
  | Tarray : type → N → type
  | Tincomplete_array : type → type
  | Tvariable_array : type → Expr → type
  | Tnamed : name → type
  | Tenum : name → type
  | Tfunction : function_type_ type → type
  | Tbool : type
  | Tmember_pointer : type → type → type
  | Tfloat_ : float_type.t → type
  | Tqualified : type_qualifiers → type → type
  | Tnullptr : type
  | Tarch : option bitsize → string → type
  | Tdecltype : Expr → type
  | Texprtype : Expr → type
  | Tunsupported : string → type
  with Expr' : Set :=
    Eparam : ident → Expr
  | Eunresolved_global : name → Expr
  | Eunresolved_unop : RUnOp → Expr → Expr
  | Eunresolved_binop : RBinOp → Expr → Expr → Expr
  | Eunresolved_call : name → list Expr → Expr
  | Eunresolved_member_call : name → Expr → list Expr → Expr
  | Eunresolved_parenlist : option type → list Expr → Expr
  | Eunresolved_member : Expr → name → Expr
  | Evar : localname → type → Expr
  | Eenum_const : name → ident → Expr
  | Eglobal : name → type → Expr
  | Eglobal_member : name → type → Expr
  | Echar : N → type → Expr
  | Estring : literal_string.t → type → Expr
  | Eint : Z → type → Expr
  | Ebool : bool → Expr
  | Eunop : UnOp → Expr → type → Expr
  | Ebinop : BinOp → Expr → Expr → type → Expr
  | Ederef : Expr → type → Expr
  | Eaddrof : Expr → Expr
  | Eassign : Expr → Expr → type → Expr
  | Eassign_op : BinOp → Expr → Expr → type → Expr
  | Epreinc : Expr → type → Expr
  | Epostinc : Expr → type → Expr
  | Epredec : Expr → type → Expr
  | Epostdec : Expr → type → Expr
  | Eseqand : Expr → Expr → Expr
  | Eseqor : Expr → Expr → Expr
  | Ecomma : Expr → Expr → Expr
  | Ecall : Expr → list Expr → Expr
  | Eexplicit_cast : cast_style.t → type → Expr → Expr
  | Ecast : Cast → Expr → Expr
  | Emember : bool → Expr → atomic_name → bool → type → Expr
  | Emember_ignore : bool → Expr → Expr → Expr
  | Emember_call : bool → MethodRef_ name type Expr → Expr → list Expr → Expr
  | Eoperator_call : OverloadableOperator → operator_impl.t name type → list Expr → Expr
  | Esubscript : Expr → Expr → type → Expr
  | Esizeof : type + Expr → type → Expr
  | Ealignof : type + Expr → type → Expr
  | Eoffsetof : type → ident → type → Expr
  | Econstructor : name → list Expr → type → Expr
  | Elambda : name → list Expr → Expr
  | Eimplicit : Expr → Expr
  | Eimplicit_init : type → Expr
  | Eif : Expr → Expr → Expr → type → Expr
  | Eif2 : N → Expr → Expr → Expr → Expr → type → Expr
  | Ethis : type → Expr
  | Enull : Expr
  | Einitlist : list Expr → option Expr → type → Expr
  | Einitlist_union : atomic_name → option Expr → type → Expr
  | Enew : name * type → list Expr → new_form → type → option Expr → option Expr → Expr
  | Edelete : bool → name → Expr → type → Expr
  | Eandclean : Expr → Expr
  | Ematerialize_temp : Expr → ValCat → Expr
  | Eatomic : AtomicOp → list Expr → type → Expr
  | Estmt : Stmt → type → Expr
  | Eva_arg : Expr → type → Expr
  | Epseudo_destructor : bool → type → Expr → Expr
  | Earrayloop_init : N → Expr → N → N → Expr → type → Expr
  | Earrayloop_index : N → type → Expr
  | Eopaque_ref : N → type → Expr
  | Eunsupported : string → type → Expr
  with Stmt' : Set :=
    Sseq : list Stmt → Stmt
  | Sdecl : list VarDecl → Stmt
  | Sif : option VarDecl → Expr → Stmt → Stmt → Stmt
  | Sif_consteval : Stmt → Stmt → Stmt
  | Swhile : option VarDecl → Expr → Stmt → Stmt
  | Sfor : option Stmt → option Expr → option Expr → Stmt → Stmt
  | Sdo : Stmt → Expr → Stmt
  | Sswitch : option VarDecl → Expr → Stmt → Stmt
  | Scase : SwitchBranch → Stmt
  | Sdefault : Stmt
  | Sbreak : Stmt
  | Scontinue : Stmt
  | Sreturn : option Expr → Stmt
  | Sexpr : Expr → Stmt
  | Sattr : list ident → Stmt → Stmt
  | Sasm : string → bool → list (ident * Expr) → list (ident * Expr) → list ident → Stmt
  | Slabeled : ident → Stmt → Stmt
  | Sgoto : ident → Stmt
  | Sunsupported : string → Stmt
  with VarDecl' : Set :=
    Dvar : localname → type → option Expr → VarDecl
  | Ddecompose : Expr → ident → list BindingDecl → VarDecl
  | Dinit : bool → name → type → option Expr → VarDecl
  with BindingDecl' : Set :=
    Bvar : localname → type → Expr → BindingDecl | Bbind : localname → type → Expr → BindingDecl
  with Cast' : Set :=
    Cdependent : type → Cast
  | Cbitcast : type → Cast
  | Clvaluebitcast : type → Cast
  | Cl2r : Cast
  | Cl2r_bitcast : type → Cast
  | Cnoop : type → Cast
  | Carray2ptr : Cast
  | Cfun2ptr : Cast
  | Cint2ptr : type → Cast
  | Cptr2int : type → Cast
  | Cptr2bool : Cast
  | Cintegral : type → Cast
  | Cint2bool : Cast
  | Cfloat2int : type → Cast
  | Cint2float : type → Cast
  | Cfloat : type → Cast
  | Cnull2ptr : type → Cast
  | Cnull2memberptr : type → Cast
  | Cbuiltin2fun : type → Cast
  | C2void : Cast
  | Cctor : type → Cast
  | Cuser : Cast
  | Cdynamic : type → Cast
  | Cderived2base : list type → type → Cast
  | Cbase2derived : list type → type → Cast
  | Cunsupported : bs → type → Cast.

Arguments Ninst c%_cpp_name_scope _%_list_scope
Arguments Nglobal c
Arguments Ndependent t%_cpp_type_scope
Arguments Nscoped n%_cpp_name_scope c
Arguments Nunsupported _%_pstring_scope
Arguments Atype _%_cpp_type_scope
Arguments Avalue _%_CPP_expr_scope
Arguments Apack _%_list_scope
Arguments Atemplate _%_cpp_name_scope
Arguments Aunsupported _%_pstring_scope
Arguments Tparam _%_pstring_scope
Arguments Tresult_param _%_pstring_scope
Arguments Tresult_global on%_cpp_name_scope
Arguments Tresult_unop _ _%_cpp_type_scope
Arguments Tresult_binop _ (_ _)%_cpp_type_scope
Arguments Tresult_call on%_cpp_name_scope _%_list_scope
Arguments Tresult_member_call on%_cpp_name_scope _%_cpp_type_scope _%_list_scope
Arguments Tresult_parenlist _%_cpp_type_scope _%_list_scope
Arguments Tresult_member _%_cpp_type_scope _%_cpp_name_scope
Arguments Tptr t%_cpp_type_scope
Arguments Tref t%_cpp_type_scope
Arguments Trv_ref t%_cpp_type_scope
Arguments Tnum sz sgn
Arguments Tarray t%_cpp_type_scope n%_N_scope
Arguments Tincomplete_array t%_cpp_type_scope
Arguments Tvariable_array t%_cpp_type_scope e%_CPP_expr_scope
Arguments Tnamed gn%_cpp_name_scope
Arguments Tenum gn%_cpp_name_scope
Arguments Tfunction t
Arguments Tmember_pointer (gn t)%_cpp_type_scope
Arguments Tqualified (q t)%_cpp_type_scope
Arguments Tarch osz name%_pstring_scope
Arguments Tdecltype _%_CPP_expr_scope
Arguments Texprtype _%_CPP_expr_scope
Arguments Tunsupported _%_pstring_scope
Arguments Eparam _%_pstring_scope
Arguments Eunresolved_global _%_cpp_name_scope
Arguments Eunresolved_unop _ e%_CPP_expr_scope
Arguments Eunresolved_binop _ (l r)%_CPP_expr_scope
Arguments Eunresolved_call on%_cpp_name_scope _%_list_scope
Arguments Eunresolved_member_call on%_cpp_name_scope _%_CPP_expr_scope _%_list_scope
Arguments Eunresolved_parenlist _ _%_list_scope
Arguments Eunresolved_member _%_CPP_expr_scope _%_cpp_name_scope
Arguments Evar _%_pstring_scope _%_cpp_type_scope
Arguments Eenum_const gn%_cpp_name_scope _%_pstring_scope
Arguments Eglobal on%_cpp_name_scope _%_cpp_type_scope
Arguments Eglobal_member gn%_cpp_name_scope ty%_cpp_type_scope
Arguments Echar c%_N_scope t%_cpp_type_scope
Arguments Estring s t%_cpp_type_scope
Arguments Eint n%_Z_scope t%_cpp_type_scope
Arguments Ebool b%_bool_scope
Arguments Eunop (op e)%_CPP_expr_scope t%_cpp_type_scope
Arguments Ebinop (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Ederef e%_CPP_expr_scope t%_cpp_type_scope
Arguments Eaddrof e%_CPP_expr_scope
Arguments Eassign (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eassign_op (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Epreinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epostinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epredec e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epostdec e%_CPP_expr_scope t%_cpp_type_scope
Arguments Eseqand (e1 e2)%_CPP_expr_scope
Arguments Eseqor (e1 e2)%_CPP_expr_scope
Arguments Ecomma (e1 e2)%_CPP_expr_scope
Arguments Ecall f%_CPP_expr_scope es%_list_scope
Arguments Eexplicit_cast c _%_cpp_type_scope e%_CPP_expr_scope
Arguments Ecast c e%_CPP_expr_scope
Arguments Emember arrow%_bool_scope obj%_CPP_expr_scope f mut%_bool_scope t%_cpp_type_scope
Arguments Emember_ignore arrow%_bool_scope (obj res)%_CPP_expr_scope
Arguments Emember_call arrow%_bool_scope method obj%_CPP_expr_scope args%_list_scope
Arguments Eoperator_call _ _ _%_list_scope
Arguments Esubscript (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Esizeof _ t%_cpp_type_scope
Arguments Ealignof _ t%_cpp_type_scope
Arguments Eoffsetof gn%_cpp_type_scope _%_pstring_scope t%_cpp_type_scope
Arguments Econstructor on%_cpp_name_scope args%_list_scope t%_cpp_type_scope
Arguments Elambda _%_cpp_name_scope captures%_list_scope
Arguments Eimplicit e%_CPP_expr_scope
Arguments Eimplicit_init t%_cpp_type_scope
Arguments Eif (e1 e2 e3)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eif2 n%_N_scope (common cond thn els)%_CPP_expr_scope _%_cpp_type_scope
Arguments Ethis t%_cpp_type_scope
Arguments Einitlist args%_list_scope default t%_cpp_type_scope
Arguments Einitlist_union _ _ t%_cpp_type_scope
Arguments Enew new_fn new_args%_list_scope pass_align alloc_ty%_cpp_type_scope array_size init
Arguments Edelete is_array%_bool_scope del_fn%_cpp_name_scope arg%_CPP_expr_scope deleted_type%_cpp_type_scope
Arguments Eandclean e%_CPP_expr_scope
Arguments Ematerialize_temp e%_CPP_expr_scope vc
Arguments Eatomic op%_pstring_scope args%_list_scope t%_cpp_type_scope
Arguments Estmt _%_CPP_stmt_scope _%_cpp_type_scope
Arguments Eva_arg e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epseudo_destructor is_arrow%_bool_scope t%_cpp_type_scope e%_CPP_expr_scope
Arguments Earrayloop_init oname%_N_scope src%_CPP_expr_scope (level length)%_N_scope init%_CPP_expr_scope t%_cpp_type_scope
Arguments Earrayloop_index level%_N_scope t%_cpp_type_scope
Arguments Eopaque_ref name%_N_scope t%_cpp_type_scope
Arguments Eunsupported s%_pstring_scope t%_cpp_type_scope
Arguments Sseq _%_list_scope
Arguments Sdecl _%_list_scope
Arguments Sif _ _%_CPP_expr_scope (_ _)%_CPP_stmt_scope
Arguments Sif_consteval (_ _)%_CPP_stmt_scope
Arguments Swhile _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments Sfor _ _ _ _%_CPP_stmt_scope
Arguments Sdo _%_CPP_stmt_scope _%_CPP_expr_scope
Arguments Sswitch _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments Sexpr _%_CPP_expr_scope
Arguments Sattr _%_list_scope _%_CPP_stmt_scope
Arguments Sasm _%_pstring_scope volatile%_bool_scope (inputs outputs clobbers)%_list_scope
Arguments Slabeled _%_pstring_scope _%_CPP_stmt_scope
Arguments Sgoto _%_pstring_scope
Arguments Sunsupported _%_pstring_scope
Arguments Dvar name%_pstring_scope _%_cpp_type_scope init
Arguments Ddecompose _%_CPP_expr_scope anon_var%_pstring_scope _%_list_scope
Arguments Dinit thread_safe%_bool_scope name%_cpp_name_scope _%_cpp_type_scope init
Arguments Bvar name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments Bbind name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments Cdependent _%_cpp_type_scope
Arguments Cbitcast _%_cpp_type_scope
Arguments Clvaluebitcast _%_cpp_type_scope
Arguments Cl2r_bitcast _%_cpp_type_scope
Arguments Cnoop _%_cpp_type_scope
Arguments Cint2ptr _%_cpp_type_scope
Arguments Cptr2int _%_cpp_type_scope
Arguments Cintegral _%_cpp_type_scope
Arguments Cfloat2int _%_cpp_type_scope
Arguments Cint2float _%_cpp_type_scope
Arguments Cfloat _%_cpp_type_scope
Arguments Cnull2ptr _%_cpp_type_scope
Arguments Cnull2memberptr _%_cpp_type_scope
Arguments Cbuiltin2fun _%_cpp_type_scope
Arguments Cctor _%_cpp_type_scope
Arguments Cdynamic to%_cpp_type_scope
Arguments Cderived2base path%_list_scope END%_cpp_type_scope
Arguments Cbase2derived path%_list_scope END%_cpp_type_scope
Arguments Cunsupported _%_bs_scope _%_cpp_type_scope

<prompt>Rocq < 20 || 0 < </prompt>Set Silent.

<prompt>Rocq < 21 || 0 < </prompt>Require Import Coq.Strings.String.
Toplevel input, characters 0-34:
> Require Import Coq.Strings.String.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
<warning>Warning: "From Coq" has been replaced by "From Stdlib". [deprecated-from-Coq,deprecated-since-9.0,deprecated,default]</warning>

<prompt>Rocq < 22 || 0 < </prompt>Require Import Coq.Lists.List.
Toplevel input, characters 0-30:
> Require Import Coq.Lists.List.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
<warning>Warning: "From Coq" has been replaced by "From Stdlib". [deprecated-from-Coq,deprecated-since-9.0,deprecated,default]</warning>

<prompt>Rocq < 23 || 0 < </prompt>Import ListNotations.

<prompt>Rocq < 24 || 0 < </prompt>Definition intercalate (sep : string) (l : list string) : string.

<prompt>intercalate < 25 |intercalate| 0 < </prompt>Admitted.

<prompt>Rocq < 26 || 0 < </prompt>Definition pprint_expr (e : Expr) : string.

<prompt>pprint_expr < 27 |pprint_expr| 0 < </prompt>Admitted.

<prompt>Rocq < 28 || 0 < </prompt>Definition pprint_vardecl (d : VarDecl) : string.

<prompt>pprint_vardecl < 29 |pprint_vardecl| 0 < </prompt>Admitted.

<prompt>Rocq < 30 || 0 < </prompt>Definition pprint_switchbranch (br : SwitchBranch) : string.

<prompt>pprint_switchbranch < 31 |pprint_switchbranch| 0 < </prompt>Admitted.

<prompt>Rocq < 32 || 0 < </prompt>Unset Silent.

<prompt>Rocq < 33 || 0 < </prompt>Fixpoint pprint_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      "(" ++ intercalate ";" (map pprint_stmt ss) ++ ")"
  | Sdecl ds =>
      "decl " ++ intercalate "," (map pprint_vardecl ds)
  | Sif dv e thn els =>
      "if " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " then " ++ pprint_stmt thn ++
      " else " ++ pprint_stmt els
  | Sif_consteval thn els =>
      "if_consteval " ++ pprint_stmt thn ++ " else_consteval " ++ pprint_stmt els
  | Swhile dv e body =>
      "while " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " do " ++ pprint_stmt body
  | Sfor init cond step body =>
      "for (" ++
      match init with Some st => pprint_stmt st | None => "" end ++ "; " ++
      match cond with Some e => pprint_expr e | None => "" end ++ "; " ++
      match step with Some e => pprint_expr e | None => "" end ++
      ") " ++ pprint_stmt body
  | Sdo body e =>
      "do " ++ pprint_stmt body ++ " while " ++ pprint_expr e
  | Sswitch dv e body =>
      "switch " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++ " { " ++ pprint_stmt body ++ " }"
  | Scase br =>
      "case " ++ pprint_switchbranch br
  | Sdefault => "default"
  | Sbreak => "break"
  | Scontinue => "continue"
  | Sreturn eo =>
      "return" ++
      match eo with Some e => " " ++ pprint_expr e | None => "" end
  | Sexpr e =>
      pprint_expr e
  | Sattr attrs st =>
      "attr[" ++ intercalate "," attrs ++ "] " ++ pprint_stmt st
  | Sasm s vol inputs outputs clobs =>
      "asm(" ++ s ++
      if vol then ",volatile" else "" ++
      ", in{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) inputs) ++
      "}, out{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) outputs) ++
      "}, clob{" ++ intercalate "," clobs ++ "})"
  | Slabeled lbl st =>
      lbl ++ ": " ++ pprint_stmt st
  | Sgoto lbl =>
      "goto " ++ lbl
  | Sunsupported s =>
      "unsupported(" ++ s ++ ")"
  end.
Toplevel input, characters 1574-1579:
>       "attr[" ++ intercalate "," attrs ++ "] " ++ pprint_stmt st
>                                  ^^^^^
Error:
In environment
pprint_stmt : Stmt → string
s : Stmt
attrs : list ident
st : Stmt
The term "attrs" has type "list ident" while it is expected to have type "list string".

<prompt>Rocq < 33 || 0 < </prompt>BackTo 20 .

<prompt>Rocq < 20 || 0 < </prompt>Unset Silent.

<prompt>Rocq < 35 || 0 < </prompt>Set Diffs "off".

<prompt>Rocq < 36 || 0 < </prompt>Set Printing Width 141.

<prompt>Rocq < 37 || 0 < </prompt>Set Silent.

<prompt>Rocq < 38 || 0 < </prompt>Require Import Coq.Strings.String.
Toplevel input, characters 0-34:
> Require Import Coq.Strings.String.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
<warning>Warning: "From Coq" has been replaced by "From Stdlib". [deprecated-from-Coq,deprecated-since-9.0,deprecated,default]</warning>

<prompt>Rocq < 39 || 0 < </prompt>Require Import Coq.Lists.List.
Toplevel input, characters 0-30:
> Require Import Coq.Lists.List.
> ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
<warning>Warning: "From Coq" has been replaced by "From Stdlib". [deprecated-from-Coq,deprecated-since-9.0,deprecated,default]</warning>

<prompt>Rocq < 40 || 0 < </prompt>Import ListNotations.

<prompt>Rocq < 41 || 0 < </prompt>Open Scope string_scope.

<prompt>Rocq < 42 || 0 < </prompt>Definition intercalate (sep : string) (l : list string) : string.

<prompt>intercalate < 43 |intercalate| 0 < </prompt>Admitted.

<prompt>Rocq < 44 || 0 < </prompt>Definition ident_to_string (i : ident) : string.

<prompt>ident_to_string < 45 |ident_to_string| 0 < </prompt>Admitted.

<prompt>Rocq < 46 || 0 < </prompt>Definition pprint_expr (e : Expr) : string.

<prompt>pprint_expr < 47 |pprint_expr| 0 < </prompt>Admitted.

<prompt>Rocq < 48 || 0 < </prompt>Definition pprint_vardecl (d : VarDecl) : string.

<prompt>pprint_vardecl < 49 |pprint_vardecl| 0 < </prompt>Admitted.

<prompt>Rocq < 50 || 0 < </prompt>Definition pprint_switchbranch (br : SwitchBranch) : string.

<prompt>pprint_switchbranch < 51 |pprint_switchbranch| 0 < </prompt>Admitted.

<prompt>Rocq < 52 || 0 < </prompt>Unset Silent.

<prompt>Rocq < 53 || 0 < </prompt>Fixpoint pprint_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      "(" ++ intercalate ";" (map pprint_stmt ss) ++ ")"
  | Sdecl ds =>
      "decl " ++ intercalate "," (map pprint_vardecl ds)
  | Sif dv e thn els =>
      "if " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " then " ++ pprint_stmt thn ++
      " else " ++ pprint_stmt els
  | Sif_consteval thn els =>
      "if_consteval " ++ pprint_stmt thn ++ " else_consteval " ++ pprint_stmt els
  | Swhile dv e body =>
      "while " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " do " ++ pprint_stmt body
  | Sfor init cond step body =>
      "for (" ++
      match init with Some st => pprint_stmt st | None => "" end ++ "; " ++
      match cond with Some e => pprint_expr e | None => "" end ++ "; " ++
      match step with Some e => pprint_expr e | None => "" end ++
      ") " ++ pprint_stmt body
  | Sdo body e =>
      "do " ++ pprint_stmt body ++ " while " ++ pprint_expr e
  | Sswitch dv e body =>
      "switch " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++ " { " ++ pprint_stmt body ++ " }"
  | Scase br =>
      "case " ++ pprint_switchbranch br
  | Sdefault => "default"
  | Sbreak => "break"
  | Scontinue => "continue"
  | Sreturn eo =>
      "return" ++
      match eo with Some e => " " ++ pprint_expr e | None => "" end
  | Sexpr e =>
      pprint_expr e
  | Sattr attrs st =>
      "attr[" ++ intercalate "," (map ident_to_string attrs) ++ "] " ++ pprint_stmt st
  | Sasm s vol inputs outputs clobs =>
      "asm(" ++ s ++
      if vol then ",volatile" else "" ++
      ", in{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) inputs) ++
      "}, out{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) outputs) ++
      "}, clob{" ++ intercalate "," (map ident_to_string clobs) ++ "})"
  | Slabeled lbl st =>
      ident_to_string lbl ++ ": " ++ pprint_stmt st
  | Sgoto lbl =>
      "goto " ++ ident_to_string lbl
  | Sunsupported s =>
      "unsupported(" ++ s ++ ")"
  end.
Toplevel input, characters 1683-1684:
>       "asm(" ++ s ++
>                 ^
Error:
In environment
pprint_stmt : Stmt → string
s : Stmt
s0 : PrimString.string
vol : bool
inputs : list (ident * Expr)
outputs : list (ident * Expr)
clobs : list ident
The term "s0" has type "PrimString.string" while it is expected to have type "string".

<prompt>Rocq < 53 || 0 < </prompt>Redirect "/tmp/coqGljrvW" Print Ltac Signatures.

<prompt>Rocq < 55 || 0 < </prompt>Timeout 1 Print Grammar tactic.
Entry ltac_expr is
[ "5" RIGHTA
  [  ]
| "4" LEFTA
  [ SELF; ";"; IDENT "first"; ssr_first_else
  | SELF; ";"; IDENT "first"; ssrseqarg
  | SELF; ";"; IDENT "last"; ssrseqarg
  | SELF; ";"; SELF
  | SELF; ";"; tactic_then_locality; for_each_goal; "]"
  | SELF; ssrintros_ne ]
| "3" RIGHTA
  [ SELF; ssrintros_ne
  | IDENT "try"; SELF
  | IDENT "do"; ssrmmod; ssrdotac; ssrclauses
  | IDENT "do"; ssrortacarg; ssrclauses
  | IDENT "do"; nat_or_var; ssrmmod; ssrdotac; ssrclauses
  | IDENT "do"; nat_or_var; SELF
  | IDENT "timeout"; nat_or_var; SELF
  | IDENT "time"; OPT string; SELF
  | IDENT "repeat"; SELF
  | IDENT "progress"; SELF
  | IDENT "once"; SELF
  | IDENT "exactly_once"; SELF
  | IDENT "abstract"; ssrdgens
  | IDENT "abstract"; NEXT; "using"; ident
  | IDENT "abstract"; NEXT
  | IDENT "only"; goal_selector; ":"; SELF ]
| "2" RIGHTA
  [ SELF; "+"; SELF
  | SELF; "||"; SELF
  | IDENT "tryif"; SELF; "then"; SELF; "else"; SELF ]
| "1" RIGHTA
  [ "fun"; LIST1 input_fun; "=>"; ltac_expr LEVEL "5"
  | "let"; [ IDENT "rec" |  ]; LIST1 let_clause SEP "with"; "in"; ltac_expr
    LEVEL "5"
  | IDENT "first"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "solve"; "["; LIST0 ltac_expr SEP "|"; "]"
  | IDENT "idtac"; LIST0 message_token
  | match_key; IDENT "goal"; "with"; match_context_list; "end"
  | match_key; IDENT "reverse"; IDENT "goal"; "with"; match_context_list;
    "end"
  | match_key; SELF; "with"; match_list; "end"
  | failkw; [ nat_or_var |  ]; LIST0 message_token
  | simple_tactic
  | tactic_value
  | reference; LIST0 tactic_arg ]
| "0" LEFTA
  [ "("; SELF; ")"
  | "["; ">"; for_each_goal; "]"
  | ssrparentacarg
  | tactic_atom ] ]

Entry simple_tactic is
[ LEFTA
  [ IDENT "hint_label"; reference
  | IDENT "wthrough"; open_constr; ltac_expr LEVEL "3"; ltac_expr LEVEL "3"
  | IDENT "wthrough"; open_constr; ltac_expr LEVEL "3"
  | IDENT "wthrough"; open_constr
  | IDENT "wuntil"; open_constr; ltac_expr LEVEL "3"
  | IDENT "unBP2"; open_constr
  | IDENT "BP"; open_constr
  | IDENT "wmod_"; uconstr
  | IDENT "wmod"; uconstr
  | IDENT "gc"; "-"; LIST1 ident
  | IDENT "step"; LIST0 br_modifier
  | IDENT "learn_exist"; LIST0 br_modifier
  | IDENT "pgo1"; LIST0 br_modifier
  | IDENT "ego1"; LIST0 br_modifier
  | IDENT "go1"; LIST0 br_modifier
  | IDENT "pgo"; LIST0 br_modifier
  | IDENT "ego"; LIST0 br_modifier
  | IDENT "go"; LIST0 br_modifier
  | IDENT "prun1"; LIST0 br_modifier
  | IDENT "erun1"; LIST0 br_modifier
  | IDENT "run1"; LIST0 br_modifier
  | IDENT "prun"; LIST0 br_modifier
  | IDENT "erun"; LIST0 br_modifier
  | IDENT "run"; LIST0 br_modifier
  | IDENT "pwork"; LIST0 br_modifier
  | IDENT "ework"; LIST0 br_modifier
  | IDENT "work"; LIST0 br_modifier
  | IDENT "wgc"; LIST0 br_modifier
  | IDENT "learner"; LIST0 br_modifier
  | IDENT "psep"; LIST0 br_modifier
  | IDENT "esep"; LIST0 br_modifier
  | IDENT "sep"; LIST0 br_modifier
  | "with_log_tmp_file!"; constr; tactic
  | IDENT "with_log_tmp_file"; constr; tactic
  | IDENT "with_log_tmp"; constr; constr; tactic
  | "output_log_tmp_file!"; constr
  | IDENT "output_log_tmp_file"; constr
  | IDENT "output_log_tmp"; constr; constr
  | "with_log_file!"; constr; tactic
  | IDENT "with_log_file"; constr; tactic
  | "with_log!"; tactic
  | IDENT "with_log"; tactic
  | IDENT "with_log_generic"; constr; constr; tactic
  | "output_log_file!"; constr
  | IDENT "output_log_file"; constr
  | "output_log!"
  | IDENT "output_log"
  | IDENT "output_log_generic"; constr; constr
  | IDENT "pop_all_spans"
  | IDENT "reset_log"
  | IDENT "with_unsealed_bi"; tactic
  | IDENT "vc_split"; rpattern
  | IDENT "vc_split"
  | IDENT "iAaccIntro1"; "with"; constr
  | IDENT "iAuIntro1"
  | IDENT "icancel"; open_constr
  | IDENT "wrename"; "["; rpattern; "]"; constr
  | IDENT "wname"; "["; rpattern; "]"; constr
  | IDENT "cut_pure"; open_constr
  | IDENT "wsplit_matchL"; open_constr
  | IDENT "wsplit_matchR"; open_constr
  | IDENT "wfocus"; open_constr; "-"; constr
  | IDENT "wfocus"; open_constr; constr
  | IDENT "ren_hyp"; ident; open_constr
  | IDENT "bind_ren"; ident; "["; rpattern; "]"
  | IDENT "shadow_rename"; ident; IDENT "into"; ident
  | IDENT "bind"; "["; rpattern; "]"; ltac_expr LEVEL "3"
  | IDENT "wexists"; open_constr
  | IDENT "use_protectb"; open_constr
  | IDENT "use_protect"; open_constr
  | IDENT "useb"; open_constr
  | IDENT "use"; open_constr
  | IDENT "ren_evar"; open_constr; ident
  | IDENT "solve_proper"; "using"; uconstr; ","; uconstr; ","; uconstr; ",";
    uconstr
  | IDENT "solve_proper"; "using"; uconstr; ","; uconstr; ","; uconstr
  | IDENT "solve_proper"; "using"; uconstr; ","; uconstr
  | IDENT "solve_proper"; "using"; uconstr
  | IDENT "destruct_tele"; "/="
  | IDENT "pclean"
  | IDENT "punfold"; hyp
  | IDENT "punfold"
  | IDENT "pinst"; hyp; open_constr
  | IDENT "ipExists"; ident
  | IDENT "ipExists"
  | IDENT "pexists"; ident
  | IDENT "pexists"
  | IDENT "iAccu"
  | IDENT "iInv"; constr; "as"; "("; LIST1 simple_intropattern; ")"; constr;
    constr
  | IDENT "iInv"; constr; "as"; "("; LIST1 simple_intropattern; ")"; constr
  | IDENT "iInv"; constr; "as"; constr; constr
  | IDENT "iInv"; constr; "as"; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; constr; constr
  | IDENT "iInv"; constr; "with"; constr; "as"; constr
  | IDENT "iInvCore"; constr; "in"; ltac_expr LEVEL "3"
  | IDENT "iInvCore"; constr; "as"; constr; "in"; ltac_expr LEVEL "3"
  | IDENT "iInvCore"; constr; "with"; constr; "in"; ltac_expr LEVEL "3"
  | IDENT "iInvCore"; constr; "with"; constr; "as"; open_constr; "in";
    ltac_expr LEVEL "3"
  | IDENT "iAssumptionInv"; constr
  | IDENT "iMod"; open_constr; "as"; "%"; simple_intropattern
  | IDENT "iMod"; open_constr; "as"; "("; LIST1 simple_intropattern; ")";
    constr
  | IDENT "iMod"; open_constr; "as"; constr
  | IDENT "iMod"; open_constr
  | IDENT "iRewrite"; "-"; open_constr; "in"; constr
  | IDENT "iRewrite"; "-"; open_constr
  | IDENT "iRewrite"; open_constr; "in"; constr
  | IDENT "iRewrite"; open_constr
  | IDENT "iAssert"; open_constr; "as"; "%"; simple_intropattern
  | IDENT "iAssert"; open_constr; "as"; "("; LIST1 simple_intropattern; ")";
    constr
  | IDENT "iAssert"; open_constr; "as"; constr
  | IDENT "iAssert"; open_constr; "with"; constr; "as"; "%";
    simple_intropattern
  | IDENT "iAssert"; open_constr; "with"; constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr
  | IDENT "iAssert"; open_constr; "with"; constr; "as"; constr
  | IDENT "iAssertCore"; open_constr; "as"; constr; ltac_expr LEVEL "3"
  | IDENT "iAssertCore"; open_constr; "with"; constr; "as"; constr; ltac_expr
    LEVEL "3"
  | IDENT "iLöb"; "as"; constr; "forall"; "("; LIST1 ident; ")"; constr
  | IDENT "iLöb"; "as"; constr; "forall"; "("; LIST1 ident; ")"
  | IDENT "iLöb"; "as"; constr; "forall"; constr
  | IDENT "iLöb"; "as"; constr
  | IDENT "iLöbCore"; "as"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr;
    "forall"; "("; LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr;
    "forall"; "("; LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr;
    "forall"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "using"; uconstr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "forall"; "(";
    LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "forall"; "(";
    LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; "forall"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr; "forall"; "("; LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr; "forall"; "("; LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr; "forall"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "using";
    uconstr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "forall";
    "("; LIST1 ident; ")"; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "forall";
    "("; LIST1 ident; ")"
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr; "forall";
    constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern; constr
  | IDENT "iInduction"; constr; "as"; simple_intropattern
  | IDENT "iInductionCore"; ltac_expr LEVEL "3"; "as"; constr
  | IDENT "iPoseProof"; open_constr; "as"; "("; LIST1 simple_intropattern;
    ")"; constr
  | IDENT "iPoseProof"; open_constr; "as"; constr
  | IDENT "iDestruct"; IDENT "select"; open_constr; "as"; "%";
    simple_intropattern
  | IDENT "iDestruct"; IDENT "select"; open_constr; "as"; "(";
    LIST1 simple_intropattern; ")"; constr
  | IDENT "iDestruct"; IDENT "select"; open_constr; "as"; constr
  | IDENT "iDestruct"; open_constr; "as"; "%"; simple_intropattern
  | IDENT "iDestruct"; open_constr; "as"; "("; LIST1 simple_intropattern;
    ")"; constr
  | IDENT "iDestruct"; open_constr; "as"; constr
  | IDENT "iDestructCore"; open_constr; "as"; constr; ltac_expr LEVEL "3"
  | IDENT "iRevertIntros"; "with"; ltac_expr LEVEL "3"
  | IDENT "iRevertIntros"; "("; LIST1 ident; ")"; "with"; ltac_expr LEVEL "3"
  | IDENT "iRevertIntros"; "("; LIST1 ident; ")"; constr; "with"; ltac_expr
    LEVEL "3"
  | IDENT "iRevertIntros"; constr; "with"; ltac_expr LEVEL "3"
  | IDENT "iIntros"; "("; LIST1 simple_intropattern; ")"; constr
  | IDENT "iIntros"; "("; LIST1 simple_intropattern; ")"
  | IDENT "iIntros"; constr; "("; LIST1 simple_intropattern; ")"; constr
  | IDENT "iIntros"; constr; "("; LIST1 simple_intropattern; ")"
  | IDENT "iIntros"; constr
  | IDENT "iIntros"
  | IDENT "iCombineAsGivesCore"; constr; "as"; constr; IDENT "gives";
    ltac_expr LEVEL "3"
  | IDENT "iCombineGivesCore"; constr; IDENT "gives"; ltac_expr LEVEL "3"
  | IDENT "iCombine"; constr; IDENT "gives"; "%"; simple_intropattern
  | IDENT "iCombine"; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; "as"; constr; IDENT "gives"; "%";
    simple_intropattern
  | IDENT "iCombine"; constr; "as"; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; "as"; constr
  | IDENT "iCombine"; constr; constr; IDENT "gives"; "%"; simple_intropattern
  | IDENT "iCombine"; constr; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; constr; "as"; constr; IDENT "gives"; "%";
    simple_intropattern
  | IDENT "iCombine"; constr; constr; "as"; constr; IDENT "gives"; constr
  | IDENT "iCombine"; constr; constr; "as"; constr
  | IDENT "iDestructHyp"; constr; "as"; "("; LIST1 simple_intropattern; ")";
    constr
  | IDENT "iDestructHyp"; constr; "as"; constr
  | IDENT "iModCore"; constr; "as"; constr
  | IDENT "iNext"; open_constr
  | IDENT "iNext"
  | IDENT "iAlways"
  | IDENT "iModIntro"; uconstr
  | IDENT "iModIntro"
  | IDENT "iExists"; LIST1 uconstr SEP ","
  | IDENT "iSplitR"; constr
  | IDENT "iSplitR"
  | IDENT "iSplitL"; constr
  | IDENT "iSplitL"
  | IDENT "iSplit"
  | IDENT "iOrDestruct"; constr; "as"; constr; constr
  | IDENT "iRight"
  | IDENT "iLeft"
  | IDENT "iApply"; open_constr
  | IDENT "iApplyHyp"; constr
  | IDENT "iPoseProofCore"; open_constr; "as"; constr; ltac_expr LEVEL "3"
  | IDENT "iSpecialize"; open_constr; "as"; "#"
  | IDENT "iSpecialize"; open_constr
  | IDENT "iSpecializeCore"; open_constr; "as"; constr
  | IDENT "iSpecializeCore"; open_constr; "with"; open_constr; open_constr;
    "as"; constr
  | IDENT "iPoseProofCoreLem"; open_constr; "as"; ltac_expr LEVEL "3"
  | IDENT "iPoseProofCoreHyp"; constr; "as"; constr
  | IDENT "iRevert"; IDENT "select"; open_constr
  | IDENT "iRevert"; "("; LIST1 ident; ")"; constr
  | IDENT "iRevert"; "("; LIST1 ident; ")"
  | IDENT "iRevert"; constr
  | IDENT "iRevertHyp"; constr; "with"; ltac_expr LEVEL "1"
  | IDENT "iRevertHyp"; constr
  | IDENT "iFrame"; IDENT "select"; open_constr
  | IDENT "iFrame"; "("; LIST1 constr; ")"; constr
  | IDENT "iFrame"; "("; LIST1 constr; ")"
  | IDENT "iFrame"; constr
  | IDENT "iFrame"
  | IDENT "iPureIntro"
  | IDENT "iEmpIntro"
  | IDENT "iPure"; constr; "as"; simple_intropattern
  | IDENT "iExFalso"
  | IDENT "iAssumption"
  | IDENT "iAssumptionCoq"
  | IDENT "iAssumptionCore"
  | IDENT "iExact"; constr
  | IDENT "iUnfold"; LIST1 reference SEP ","; "in"; constr
  | IDENT "iUnfold"; LIST1 reference SEP ","
  | IDENT "iSimpl"; "in"; constr
  | IDENT "iSimpl"
  | IDENT "iEval"; ltac_expr LEVEL "3"; "in"; constr
  | IDENT "iEval"; ltac_expr LEVEL "3"
  | IDENT "iClear"; IDENT "select"; open_constr
  | IDENT "iClear"; "("; LIST0 ident; ")"; constr
  | IDENT "iClear"; constr
  | IDENT "iRename"; IDENT "select"; open_constr; IDENT "into"; constr
  | IDENT "iRename"; constr; IDENT "into"; constr
  | IDENT "iStopProof"
  | IDENT "iStartProof"; uconstr
  | IDENT "iStartProof"
  | IDENT "iSelect"; open_constr; ltac_expr LEVEL "1"
  | IDENT "iMatchHyp"; ltac_expr LEVEL "1"
  | IDENT "wmod_base"; ltac_expr LEVEL "3"; uconstr
  | IDENT "wpose_with_mask_change"; uconstr
  | IDENT "wpose"; uconstr
  | IDENT "wassert"; open_constr
  | IDENT "wapply"; open_constr
  | IDENT "wp_for_"; uconstr
  | IDENT "wp_for"; uconstr
  | IDENT "wp_do_while_"; uconstr
  | IDENT "wp_do_while"; uconstr
  | IDENT "wp_while_"; uconstr
  | IDENT "wp_while"; uconstr
  | IDENT "wp_switch_"; uconstr
  | IDENT "wp_switch"; uconstr
  | IDENT "wp_switch"
  | IDENT "wpe_spec"; uconstr
  | "wpe_spec["; open_constr; "]"; uconstr
  | IDENT "wpe_if"; uconstr
  | IDENT "wpe_if"
  | "wpe_if["; open_constr; "]"; uconstr
  | IDENT "wp_if_"; uconstr
  | IDENT "wp_if"; uconstr
  | IDENT "wp_if"
  | IDENT "updateGll"; open_constr; open_constr
  | IDENT "mk_obs_fwd"; uconstr
  | IDENT "ltac_attributes"; ":"; "("; ltac_attributes; ")"; IDENT "elpi";
    qualified_name; LIST0 elpi_tactic_arg
  | "#["; attributes; "]"; IDENT "elpi"; qualified_name;
    LIST0 elpi_tactic_arg
  | IDENT "elpi"; IDENT "query"; ghost; elpi_string
  | IDENT "elpi"; IDENT "query"; qualified_name; elpi_string
  | IDENT "elpi"; qualified_name; LIST0 elpi_tactic_arg
  | IDENT "iCaccIntro"; "with"; constr
  | IDENT "iAcIntro"
  | IDENT "iAaccIntro"; "with"; constr
  | IDENT "iAuIntro"
  | IDENT "solve_ne_proper"; "using"; constr
  | IDENT "field_simplify_eq"; "in"; hyp
  | IDENT "field_simplify_eq"; "["; LIST0 constr; "]"; "in"; hyp
  | IDENT "field_simplify_eq"; "["; LIST0 constr; "]"
  | IDENT "field_simplify_eq"
  | IDENT "field"; "["; LIST0 constr; "]"
  | IDENT "field"
  | IDENT "field_simplify"; "["; LIST0 constr; "]"; LIST0 constr; "in"; hyp
  | IDENT "field_simplify"; "["; LIST0 constr; "]"; LIST0 constr
  | IDENT "field_simplify"; LIST0 constr; "in"; hyp
  | IDENT "field_simplify"; LIST0 constr
  | IDENT "f_contractive_fin"
  | IDENT "f_contractive"; "as"; ident; ident
  | IDENT "f_contractive"
  | IDENT "dist_later_intro"; "as"; ident; ident
  | IDENT "dist_later_intro"
  | IDENT "ofe_subst"; ident
  | IDENT "ofe_subst"
  | IDENT "discriminate_list"; hyp
  | IDENT "discriminate_list"
  | IDENT "simplify_option_eq"; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_option_eq"
  | IDENT "simpl_option"; "by"; ltac_expr LEVEL "3"
  | IDENT "naive_solver"; tactic
  | IDENT "naive_solver"
  | IDENT "select"; open_constr; ltac_expr LEVEL "3"
  | IDENT "learn_hyp"; constr; "as"; ident
  | IDENT "learn_hyp"; constr
  | IDENT "ospecialize"; "*"; uconstr
  | IDENT "ospecialize"; uconstr
  | IDENT "oinv"; integer; "as"; simple_intropattern
  | IDENT "oinv"; integer
  | IDENT "oinv"; uconstr; "as"; simple_intropattern
  | IDENT "oinv"; uconstr
  | IDENT "oinversion"; uconstr; "as"; simple_intropattern
  | IDENT "oinversion"; uconstr
  | IDENT "odestruct"; uconstr; "as"; simple_intropattern
  | IDENT "odestruct"; uconstr
  | IDENT "ogeneralize"; "*"; uconstr
  | IDENT "ogeneralize"; uconstr
  | IDENT "opose"; IDENT "proof"; "*"; uconstr; "as"; simple_intropattern
  | IDENT "opose"; IDENT "proof"; "*"; uconstr
  | IDENT "opose"; IDENT "proof"; uconstr; "as"; simple_intropattern
  | IDENT "opose"; IDENT "proof"; uconstr
  | IDENT "inv"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "inv"; IDENT "select"; open_constr
  | IDENT "inv"; integer; "as"; simple_intropattern
  | IDENT "inv"; integer
  | IDENT "inv"; ident; "as"; simple_intropattern
  | IDENT "inv"; ident
  | IDENT "iter"; tactic; tactic
  | IDENT "f_equiv"; "/="
  | IDENT "f_equal"; "/="
  | IDENT "csimpl"; "in"; "*"
  | IDENT "csimpl"; "in"; hyp
  | IDENT "csimpl"
  | IDENT "eunify"; open_constr; open_constr
  | IDENT "is_non_dependent"; constr
  | IDENT "repeat_on_hyps"; ltac_expr LEVEL "3"
  | IDENT "unless"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "case_guard"; "as"; ident
  | IDENT "case_guard"
  | IDENT "case_match"; IDENT "eqn"; ":"; ident
  | IDENT "destruct_or"; "!"; ident
  | IDENT "destruct_or"; "!"
  | IDENT "destruct_or"; "?"; ident
  | IDENT "destruct_or"; "?"
  | IDENT "destruct_and"; "!"; ident
  | IDENT "destruct_and"; "!"
  | IDENT "destruct_and"; "?"; ident
  | IDENT "destruct_and"; "?"
  | IDENT "split_and"; "!"
  | IDENT "split_and"; "?"
  | IDENT "split_and"
  | IDENT "etrans"
  | IDENT "trans"; constr
  | IDENT "fast_by"; tactic
  | IDENT "compute_by"; tactic
  | IDENT "compute_done"
  | IDENT "case_bool_decide"; "as"; ident
  | IDENT "case_bool_decide"
  | IDENT "case_decide"; "as"; ident
  | IDENT "case_decide"
  | IDENT "destruct_decide"; constr; "as"; ident
  | IDENT "destruct_decide"; constr
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "at"; LIST0 int_or_var; "by"; ltac_expr
    LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "in"; hyp
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "at"; LIST0 int_or_var; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "using"; IDENT
    "relation"; constr
  | IDENT "setoid_replace"; constr; "with"; constr; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "by";
    ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "at";
    LIST0 int_or_var; "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp; "at";
    LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr; "in"; hyp
  | IDENT "setoid_replace"; constr; "with"; constr; "at"; LIST0 int_or_var;
    "by"; ltac_expr LEVEL "3"
  | IDENT "setoid_replace"; constr; "with"; constr; "at"; LIST0 int_or_var
  | IDENT "setoid_replace"; constr; "with"; constr
  | IDENT "reduce"; "in"; hyp
  | IDENT "xpsatz_R"; nat_or_var; tactic
  | IDENT "wpsatz_Q"; nat_or_var; ident; constr
  | IDENT "xpsatz_Q"; nat_or_var; tactic
  | IDENT "wpsatz_Z"; nat_or_var; ident; constr
  | IDENT "xpsatz_Z"; nat_or_var; tactic
  | IDENT "xsos_R"; tactic
  | IDENT "wsos_Q"; ident; constr
  | IDENT "xsos_Q"; tactic
  | IDENT "wsos_Z"; ident; constr
  | IDENT "xsos_Z"; tactic
  | IDENT "wnia"; ident; constr
  | IDENT "xnia"; tactic
  | IDENT "xnra_R"; tactic
  | IDENT "wnra_Q"; ident; constr
  | IDENT "xnra_Q"; tactic
  | IDENT "wlia"; ident; constr
  | IDENT "xlia"; tactic
  | IDENT "xlra_R"; tactic
  | IDENT "wlra_Q"; ident; constr
  | IDENT "xlra_Q"; tactic
  | IDENT "ring_simplify"; "["; LIST0 constr; "]"; LIST0 constr; "in"; hyp
  | IDENT "ring_simplify"; "["; LIST0 constr; "]"; LIST0 constr
  | IDENT "ring_simplify"; LIST0 constr; "in"; hyp
  | IDENT "ring_simplify"; LIST0 constr
  | IDENT "ring"; "["; LIST0 constr; "]"
  | IDENT "ring"
  | IDENT "field_lookup"; tactic; "["; LIST0 constr; "]"; LIST1 constr
  | IDENT "ring_lookup"; ltac_expr LEVEL "0"; "["; LIST0 constr; "]";
    LIST1 constr
  | IDENT "protect_fv"; string; "in"; ident
  | IDENT "protect_fv"; string
  | IDENT "set_solver"; "+"; LIST0 hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"; "+"; LIST0 hyp
  | IDENT "set_solver"; "-"; LIST0 hyp; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"; "-"; LIST0 hyp
  | IDENT "set_solver"; "by"; ltac_expr LEVEL "3"
  | IDENT "set_solver"
  | IDENT "set_unfold"; "in"; ident
  | IDENT "set_unfold"
  | IDENT "under"; ssrrwarg; IDENT "do"; ssrhint3arg
  | IDENT "under"; ssrrwarg; ssrintros_ne; IDENT "do"; ssrhint3arg
  | IDENT "under"; ssrrwarg; ssrintros_ne
  | IDENT "under"; ssrrwarg
  | IDENT "generally"; IDENT "have"; ssrclear; ssr_idcomma; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "gen"; IDENT "have"; ssrclear; ssr_idcomma; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "without"; IDENT "loss"; IDENT "suffices"; ssrhpats_nobs;
    ssrwlogfwd; ssrhint
  | IDENT "without"; IDENT "loss"; IDENT "suff"; ssrhpats_nobs; ssrwlogfwd;
    ssrhint
  | IDENT "without"; IDENT "loss"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; IDENT "suffices"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; IDENT "suff"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "wlog"; ssrhpats_nobs; ssrwlogfwd; ssrhint
  | IDENT "suffices"; IDENT "have"; ssrhpats_nobs; ssrhavefwd
  | IDENT "suffices"; ssrsufffwd
  | IDENT "suff"; IDENT "have"; ssrhpats_nobs; ssrhavefwd
  | IDENT "suff"; ssrsufffwd
  | IDENT "have"; IDENT "suffices"; ssrhpats_nobs; ssrhavefwd
  | IDENT "have"; IDENT "suff"; ssrhpats_nobs; ssrhavefwd
  | IDENT "have"; ssrhavefwdwbinders
  | IDENT "unlock"; ssrunlockargs; ssrclauses
  | IDENT "ssrinstancesofruleR2L"; ssrterm
  | IDENT "ssrinstancesofruleL2R"; ssrterm
  | IDENT "congr"; ssrcongrarg
  | "by"; tactic
  | "by"; ssrhintarg
  | IDENT "multiset_solver"; "by"; ltac_expr LEVEL "3"
  | IDENT "multiset_solver"
  | IDENT "simplify_map_eq"; "/="; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_map_eq"; "/="
  | IDENT "simplify_map_eq"; "by"; ltac_expr LEVEL "3"
  | IDENT "simplify_map_eq"
  | IDENT "simpl_map"; "by"; ltac_expr LEVEL "3"
  | IDENT "simpl_map"
  | IDENT "firstorder"; OPT tactic; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using; "with"; LIST1 preident
  | IDENT "firstorder"; OPT tactic; firstorder_using
  | IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "congruence"; OPT natural
  | IDENT "dintuition"; tactic
  | IDENT "dintuition"
  | IDENT "intuition"; tactic
  | IDENT "intuition"
  | IDENT "assert_fails"; ltac_expr LEVEL "3"
  | IDENT "inversion_sigma"; hyp; "as"; simple_intropattern
  | IDENT "inversion_sigma"; hyp
  | IDENT "inversion_sigma"
  | IDENT "now"; tactic
  | IDENT "rewrite_all"; "<-"; constr
  | IDENT "rewrite_all"; constr
  | IDENT "destruct_with_eqn"; ":"; ident; ident
  | IDENT "destruct_with_eqn"; ":"; ident; constr
  | IDENT "destruct_with_eqn"; ident
  | IDENT "destruct_with_eqn"; constr
  | IDENT "clearbody"; LIST1 hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp;
    hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp;
    hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp; hyp
  | IDENT "clear"; IDENT "dependent"; hyp
  | IDENT "clear"; "-"; LIST1 hyp
  | IDENT "clear"; natural
  | IDENT "clear"; LIST0 hyp
  | IDENT "revert"; IDENT "select"; open_constr
  | IDENT "revert"; IDENT "dependent"; hyp
  | IDENT "revert"; LIST1 hyp
  | IDENT "rename"; IDENT "select"; open_constr; IDENT "into"; ident
  | IDENT "rename"; LIST1 rename SEP ","
  | IDENT "move"; ssrmovearg; ssrrpat
  | IDENT "move"; ssrmovearg; ssrclauses
  | IDENT "move"; ssrrpat
  | IDENT "move"; hyp; "at"; IDENT "top"
  | IDENT "move"; hyp; "at"; IDENT "bottom"
  | IDENT "move"; hyp; IDENT "after"; hyp
  | IDENT "move"; hyp; IDENT "before"; hyp
  | IDENT "move"
  | IDENT "intro"; "at"; IDENT "top"
  | IDENT "intro"; "at"; IDENT "bottom"
  | IDENT "intro"; IDENT "after"; hyp
  | IDENT "intro"; IDENT "before"; hyp
  | IDENT "intro"; ident; "at"; IDENT "top"
  | IDENT "intro"; ident; "at"; IDENT "bottom"
  | IDENT "intro"; ident; IDENT "after"; hyp
  | IDENT "intro"; ident; IDENT "before"; hyp
  | IDENT "intro"; ident
  | IDENT "intro"
  | IDENT "eexists"; LIST1 bindings SEP ","
  | IDENT "eexists"
  | "exists"; LIST1 bindings SEP ","
  | "exists"
  | IDENT "esplit"; "with"; bindings
  | IDENT "split"; "with"; bindings
  | IDENT "symmetry"; "in"; in_clause
  | IDENT "specialize"; constr_with_bindings; "as"; simple_intropattern
  | IDENT "specialize"; constr_with_bindings
  | IDENT "econstructor"; nat_or_var; "with"; bindings
  | IDENT "econstructor"; nat_or_var
  | IDENT "econstructor"
  | IDENT "constructor"; nat_or_var; "with"; bindings
  | IDENT "constructor"; nat_or_var
  | IDENT "constructor"
  | IDENT "eright"; "with"; bindings
  | IDENT "right"; "with"; bindings
  | IDENT "eleft"; "with"; bindings
  | IDENT "left"; "with"; bindings
  | IDENT "exact"; "<:"; lconstr
  | IDENT "exact"; ssrexactarg
  | IDENT "exact"; uconstr
  | IDENT "exact"
  | IDENT "with_strategy"; strategy_level_or_var; "["; LIST1 smart_global;
    "]"; ltac_expr LEVEL "3"
  | IDENT "guard"; test
  | IDENT "swap"; int_or_var; int_or_var
  | IDENT "cycle"; int_or_var
  | IDENT "unshelve"; ltac_expr LEVEL "1"
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"; "using"; ident
  | IDENT "transparent_abstract"; ltac_expr LEVEL "3"
  | IDENT "destauto"; "in"; hyp
  | IDENT "destauto"
  | IDENT "specialize_eqs"; hyp
  | IDENT "generalize_eqs_vars"; hyp
  | IDENT "generalize_eqs"; hyp
  | IDENT "stepr"; constr; "by"; tactic
  | IDENT "stepr"; constr
  | IDENT "stepl"; constr; "by"; tactic
  | IDENT "stepl"; constr
  | IDENT "instantiate"; "("; ident; ":="; lconstr; ")"
  | IDENT "instantiate"; "("; natural; ":="; lconstr; ")"; hloc
  | IDENT "evar"; test_lpar_id_colon; "("; ident; ":"; lconstr; ")"
  | IDENT "evar"; constr
  | IDENT "subst"; LIST1 hyp
  | IDENT "subst"
  | IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "refine"; uconstr
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "*"; "with"; LIST1 preident; clause
  | IDENT "autorewrite"; "with"; LIST1 preident; clause; "using"; tactic
  | IDENT "autorewrite"; "with"; LIST1 preident; clause
  | IDENT "contradiction"; OPT constr_with_bindings
  | IDENT "decompose"; "["; LIST1 constr; "]"; constr
  | IDENT "decompose"; IDENT "record"; constr
  | IDENT "decompose"; IDENT "sum"; constr
  | IDENT "einjection"; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "einjection"; destruction_arg
  | IDENT "einjection"
  | IDENT "injection"; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg; "as"; LIST0 simple_intropattern
  | IDENT "injection"; destruction_arg
  | IDENT "injection"
  | IDENT "ediscriminate"; destruction_arg
  | IDENT "ediscriminate"
  | IDENT "discriminate"; destruction_arg
  | IDENT "discriminate"
  | IDENT "esimplify_eq"; destruction_arg
  | IDENT "esimplify_eq"
  | IDENT "simplify_eq"; "/="
  | IDENT "simplify_eq"; destruction_arg
  | IDENT "simplify_eq"
  | IDENT "replace"; "<-"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "<-"; uconstr; clause
  | IDENT "replace"; "->"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; "->"; uconstr; clause
  | IDENT "replace"; uconstr; "with"; constr; clause; by_arg_tac
  | IDENT "replace"; uconstr; clause
  | IDENT "assert_succeeds"; ltac_expr LEVEL "3"
  | IDENT "unify"; constr; constr; "with"; preident
  | IDENT "unify"; constr; constr
  | IDENT "autounfold_one"; hintbases; "in"; hyp
  | IDENT "autounfold_one"; hintbases
  | IDENT "autounfold"; hintbases; clause
  | IDENT "info_eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "info_auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "eauto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "auto"; OPT nat_or_var; auto_using; hintbases
  | IDENT "debug"; IDENT "trivial"; auto_using; hintbases
  | IDENT "info_trivial"; auto_using; hintbases
  | IDENT "trivial"; auto_using; hintbases
  | IDENT "autoapply"; constr; "with"; preident
  | IDENT "head_of_constr"; ident; constr
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "bfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "dfs"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var;
    "with"; LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; IDENT "best_effort"; OPT nat_or_var
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var; "with";
    LIST1 preident
  | IDENT "typeclasses"; IDENT "eauto"; OPT nat_or_var
  | IDENT "decide"; IDENT "equality"
  | IDENT "decide"; constr; "with"; constr
  | IDENT "setoid_transitivity"; constr
  | IDENT "setoid_etransitivity"
  | IDENT "setoid_symmetry"; "in"; hyp
  | IDENT "setoid_symmetry"
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences;
    "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "at"; occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp; "at";
    occurrences
  | IDENT "setoid_rewrite"; orient; constr_with_bindings; "in"; hyp
  | IDENT "setoid_rewrite"; orient; constr_with_bindings
  | IDENT "substitute"; orient; constr_with_bindings
  | IDENT "rewrite_strat"; rewstrategy; "in"; hyp
  | IDENT "rewrite_strat"; rewstrategy
  | IDENT "rewrite_db"; preident; "in"; hyp
  | IDENT "rewrite_db"; preident
  | IDENT "finish_timing"; "("; string; ")"; OPT string
  | IDENT "finish_timing"; OPT string
  | IDENT "restart_timer"; OPT string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; IDENT "cutoff"; integer
  | IDENT "show"; IDENT "ltac"; IDENT "profile"; string
  | IDENT "show"; IDENT "ltac"; IDENT "profile"
  | IDENT "reset"; IDENT "ltac"; IDENT "profile"
  | IDENT "stop"; IDENT "ltac"; IDENT "profiling"
  | IDENT "start"; IDENT "ltac"; IDENT "profiling"
  | IDENT "intros"; IDENT "until"; quantified_hypothesis
  | IDENT "intros"; ne_intropatterns
  | IDENT "intros"
  | IDENT "eintros"; ne_intropatterns
  | IDENT "eintros"
  | IDENT "apply"; "*"; constr
  | IDENT "apply"; "<-"; constr; "in"; hyp
  | IDENT "apply"; "<-"; constr
  | IDENT "apply"; "->"; constr; "in"; hyp
  | IDENT "apply"; "->"; constr
  | IDENT "apply"; ssrapplyarg
  | IDENT "apply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "apply"
  | IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ","; in_hyp_as
  | IDENT "elim"; ssrarg; ssrclauses
  | IDENT "elim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "elim"
  | IDENT "eelim"; constr_with_bindings_arg; OPT eliminator
  | IDENT "case"; ssrcasearg; ssrclauses
  | IDENT "case"; induction_clause_list
  | IDENT "case"
  | IDENT "ecase"; induction_clause_list
  | "fix"; ident; natural; "with"; LIST1 fixdecl
  | "fix"; ident; natural
  | "cofix"; ident; "with"; LIST1 cofixdecl
  | "cofix"; ident
  | IDENT "set"; ssrfwdid; ssrsetfwd; ssrclauses
  | IDENT "set"; bindings_with_parameters; clause
  | IDENT "set"; constr; as_name; clause
  | IDENT "eset"; bindings_with_parameters; clause
  | IDENT "eset"; constr; as_name; clause
  | IDENT "remember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "eremember"; constr; as_name; eqn_ipat; clause_dft_all
  | IDENT "assert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "assert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "assert"; constr; as_ipat; by_tactic
  | IDENT "eassert"; lpar_id_coloneq; "("; identref; ":="; lconstr; ")"
  | IDENT "eassert"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eassert"; constr; as_ipat; by_tactic
  | IDENT "pose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "pose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "pose"; ssrfixfwd
  | IDENT "pose"; ssrcofixfwd
  | IDENT "pose"; ssrfwdid; ssrposefwd
  | IDENT "pose"; bindings_with_parameters
  | IDENT "pose"; constr; as_name
  | IDENT "epose"; IDENT "proof"; lpar_id_coloneq; "("; identref; ":=";
    lconstr; ")"
  | IDENT "epose"; IDENT "proof"; lconstr; as_ipat
  | IDENT "epose"; bindings_with_parameters
  | IDENT "epose"; constr; as_name
  | IDENT "enough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "enough"; constr; as_ipat; by_tactic
  | IDENT "eenough"; test_lpar_id_colon; "("; identref; ":"; lconstr; ")";
    by_tactic
  | IDENT "eenough"; constr; as_ipat; by_tactic
  | IDENT "generalize"; IDENT "dependent"; constr
  | IDENT "generalize"; constr; LIST1 constr
  | IDENT "generalize"; constr; lookup_at_as_comma; occs; as_name;
    LIST0 [ ","; pattern_occ; as_name ]
  | IDENT "generalize"; constr
  | IDENT "induction"; induction_clause_list
  | IDENT "einduction"; induction_clause_list
  | IDENT "destruct"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "destruct"; IDENT "select"; open_constr
  | IDENT "destruct"; induction_clause_list
  | IDENT "edestruct"; induction_clause_list
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; "at"; occurrences;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "in"; hyp; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; "in"; hyp;
    by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; "at"; occurrences; by_arg_tac
  | IDENT "rewrite"; "*"; orient; uconstr; by_arg_tac
  | IDENT "rewrite"; ssrrwargs; ssrclauses
  | IDENT "rewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "erewrite"; LIST1 oriented_rewriter SEP ","; clause; by_tactic
  | IDENT "dependent"; IDENT "destruction"; ident
  | IDENT "dependent"; IDENT "induction"; ident
  | IDENT "dependent"; IDENT "generalize_eqs_vars"; hyp
  | IDENT "dependent"; IDENT "generalize_eqs"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr; "in"; hyp
  | IDENT "dependent"; IDENT "rewrite"; orient; constr
  | IDENT "dependent";
    [ IDENT "simple"; IDENT "inversion" | IDENT "inversion"
    | IDENT "inversion_clear" ]; quantified_hypothesis; as_or_and_ipat;
    OPT [ "with"; constr ]
  | IDENT "simple"; IDENT "congruence"; OPT natural; "with"; LIST1 constr
  | IDENT "simple"; IDENT "congruence"; OPT natural
  | IDENT "simple"; IDENT "destruct"; quantified_hypothesis
  | IDENT "simple"; IDENT "induction"; quantified_hypothesis
  | IDENT "simple"; IDENT "subst"
  | IDENT "simple"; IDENT "notypeclasses"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "refine"; uconstr
  | IDENT "simple"; IDENT "injection"; destruction_arg
  | IDENT "simple"; IDENT "injection"
  | IDENT "simple"; IDENT "apply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "eapply"; LIST1 constr_with_bindings_arg SEP ",";
    in_hyp_as
  | IDENT "simple"; IDENT "inversion"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion_clear"; quantified_hypothesis; as_or_and_ipat;
    in_hyp_list
  | IDENT "inversion"; IDENT "select"; open_constr; "as"; simple_intropattern
  | IDENT "inversion"; IDENT "select"; open_constr
  | IDENT "inversion"; quantified_hypothesis; "using"; constr; in_hyp_list
  | IDENT "inversion"; quantified_hypothesis; as_or_and_ipat; in_hyp_list
  | IDENT "red"; clause
  | IDENT "hnf"; clause
  | IDENT "simpl"; OPT [ IDENT "head" ]; delta_flag; OPT ref_or_pattern_occ;
    clause
  | IDENT "cbv"; strategy_flag; clause
  | IDENT "cbn"; strategy_flag; clause
  | IDENT "lazy"; strategy_flag; clause
  | IDENT "compute"; delta_flag; clause
  | IDENT "vm_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "native_compute"; OPT ref_or_pattern_occ; clause
  | IDENT "unfold"; LIST1 unfold_occ SEP ","; clause
  | IDENT "fold"; LIST1 constr; clause
  | IDENT "pattern"; LIST1 pattern_occ SEP ","; clause
  | IDENT "change"; conversion; clause
  | IDENT "change_no_check"; conversion; clause ] ]

Entry tactic_value is
[ LEFTA
  [ IDENT "br_modifier"; ":"; "("; br_modifier; ")"
  | IDENT "br_value"; ":"; "("; br_value; ")"
  | IDENT "br_lemma"; ":"; "("; br_lemma; ")"
  | IDENT "br_with_db"; ":"; "("; br_with_db; ")"
  | IDENT "br_db_modifier"; ":"; "("; br_db_modifier; ")"
  | IDENT "br_opacity"; ":"; "("; br_opacity; ")"
  | IDENT "elpi_code_appArg"; ":"; "("; elpi_code_appArg; ")"
  | IDENT "ghost"; ":"; "("; ghost; ")"
  | IDENT "elpi_code"; ":"; "("; elpi_code; ")"
  | IDENT "ltac_attributes"; ":"; "("; ltac_attributes; ")"
  | IDENT "elpi_tactic_arg"; ":"; "("; elpi_tactic_arg; ")"
  | IDENT "elpi_cmd_arg"; ":"; "("; elpi_cmd_arg; ")"
  | IDENT "attributes"; ":"; "("; attributes; ")"
  | IDENT "elpi_loc"; ":"; "("; elpi_loc; ")"
  | IDENT "qualified_name"; ":"; "("; qualified_name; ")"
  | IDENT "elpi_string"; ":"; "("; elpi_string; ")"
  | IDENT "ltac2val"; ":"; "("; tac2expr_in_env; ")"
  | IDENT "ltac2"; ":"; "("; tac2expr_in_env; ")"
  | IDENT "ssr_idcomma"; ":"; "("; ssr_idcomma; ")"
  | IDENT "ssrwlogfwd"; ":"; "("; ssrwlogfwd; ")"
  | IDENT "ssrsufffwd"; ":"; "("; ssrsufffwd; ")"
  | IDENT "ssrunlockargs"; ":"; "("; ssrunlockargs; ")"
  | IDENT "ssrunlockarg"; ":"; "("; ssrunlockarg; ")"
  | IDENT "ssrrwargs"; ":"; "("; ssrrwargs; ")"
  | IDENT "ssrrwarg"; ":"; "("; ssrrwarg; ")"
  | IDENT "ssrpattern_ne_squarep"; ":"; "("; ssrpattern_ne_squarep; ")"
  | IDENT "ssrpattern_squarep"; ":"; "("; ssrpattern_squarep; ")"
  | IDENT "ssrrule"; ":"; "("; ssrrule; ")"
  | IDENT "ssrrule_ne"; ":"; "("; ssrrule_ne; ")"
  | IDENT "ssrrwocc"; ":"; "("; ssrrwocc; ")"
  | IDENT "ssrcongrarg"; ":"; "("; ssrcongrarg; ")"
  | IDENT "ssrexactarg"; ":"; "("; ssrexactarg; ")"
  | IDENT "ssrapplyarg"; ":"; "("; ssrapplyarg; ")"
  | IDENT "ssragens"; ":"; "("; ssragens; ")"
  | IDENT "ssragen"; ":"; "("; ssragen; ")"
  | IDENT "ssrcasearg"; ":"; "("; ssrcasearg; ")"
  | IDENT "ssrmovearg"; ":"; "("; ssrmovearg; ")"
  | IDENT "ssrarg"; ":"; "("; ssrarg; ")"
  | IDENT "ssreqid"; ":"; "("; ssreqid; ")"
  | IDENT "ssrdgens"; ":"; "("; ssrdgens; ")"
  | IDENT "ssrdgens_tl"; ":"; "("; ssrdgens_tl; ")"
  | IDENT "ssrgen"; ":"; "("; ssrgen; ")"
  | IDENT "ssrseqdir"; ":"; "("; ssrseqdir; ")"
  | IDENT "ssrseqarg"; ":"; "("; ssrseqarg; ")"
  | IDENT "ssrdoarg"; ":"; "("; ssrdoarg; ")"
  | IDENT "ssrhavefwdwbinders"; ":"; "("; ssrhavefwdwbinders; ")"
  | IDENT "ssrhavefwd"; ":"; "("; ssrhavefwd; ")"
  | IDENT "ssrsetfwd"; ":"; "("; ssrsetfwd; ")"
  | IDENT "ssrcofixfwd"; ":"; "("; ssrcofixfwd; ")"
  | IDENT "ssrfixfwd"; ":"; "("; ssrfixfwd; ")"
  | IDENT "ssrposefwd"; ":"; "("; ssrposefwd; ")"
  | IDENT "ssrstruct"; ":"; "("; ssrstruct; ")"
  | IDENT "ssrbinder"; ":"; "("; ssrbinder; ")"
  | IDENT "ssrbvar"; ":"; "("; ssrbvar; ")"
  | IDENT "ssrfwd"; ":"; "("; ssrfwd; ")"
  | IDENT "ssrclauses"; ":"; "("; ssrclauses; ")"
  | IDENT "ssrclausehyps"; ":"; "("; ssrclausehyps; ")"
  | IDENT "ssrwgen"; ":"; "("; ssrwgen; ")"
  | IDENT "ssrhint"; ":"; "("; ssrhint; ")"
  | IDENT "ssrortacarg"; ":"; "("; ssrortacarg; ")"
  | IDENT "ssrhint3arg"; ":"; "("; ssrhint3arg; ")"
  | IDENT "ssrhintarg"; ":"; "("; ssrhintarg; ")"
  | IDENT "ssrortacs"; ":"; "("; ssrortacs; ")"
  | IDENT "ssrfwdid"; ":"; "("; ssrfwdid; ")"
  | IDENT "ssrintrosarg"; ":"; "("; ssrintrosarg; ")"
  | IDENT "ssrintros"; ":"; "("; ssrintros; ")"
  | IDENT "ssrintros_ne"; ":"; "("; ssrintros_ne; ")"
  | IDENT "ssrrpat"; ":"; "("; ssrrpat; ")"
  | IDENT "ssrhpats_nobs"; ":"; "("; ssrhpats_nobs; ")"
  | IDENT "ssrhpats_wtransp"; ":"; "("; ssrhpats_wtransp; ")"
  | IDENT "ssrhpats"; ":"; "("; ssrhpats; ")"
  | IDENT "ssripats_ne"; ":"; "("; ssripats_ne; ")"
  | IDENT "ssrcpat"; ":"; "("; ssrcpat; ")"
  | IDENT "ssriorpat"; ":"; "("; ssriorpat; ")"
  | IDENT "ssripats"; ":"; "("; ssripats; ")"
  | IDENT "ssripat"; ":"; "("; ssripat; ")"
  | IDENT "ident_no_do"; ":"; "("; ident_no_do; ")"
  | IDENT "ssrfwdview"; ":"; "("; ssrfwdview; ")"
  | IDENT "ssrbwdview"; ":"; "("; ssrbwdview; ")"
  | IDENT "ast_closure_lterm"; ":"; "("; ast_closure_lterm; ")"
  | IDENT "ast_closure_term"; ":"; "("; ast_closure_term; ")"
  | IDENT "ssrterm"; ":"; "("; ssrterm; ")"
  | IDENT "ssrdocc"; ":"; "("; ssrdocc; ")"
  | IDENT "ssrmult"; ":"; "("; ssrmult; ")"
  | IDENT "ssrmult_ne"; ":"; "("; ssrmult_ne; ")"
  | IDENT "ssrocc"; ":"; "("; ssrocc; ")"
  | IDENT "ssrindex"; ":"; "("; ssrindex; ")"
  | IDENT "ssrclear"; ":"; "("; ssrclear; ")"
  | IDENT "ssrclear_ne"; ":"; "("; ssrclear_ne; ")"
  | IDENT "ssrsimpl_ne"; ":"; "("; ssrsimpl_ne; ")"
  | IDENT "ssrhoi_id"; ":"; "("; ssrhoi_id; ")"
  | IDENT "ssrhoi_hyp"; ":"; "("; ssrhoi_hyp; ")"
  | IDENT "ssrhyp"; ":"; "("; ssrhyp; ")"
  | IDENT "ssrtclarg"; ":"; "("; ssrtacarg; ")"
  | IDENT "ssrtac3arg"; ":"; "("; ssrtac3arg; ")"
  | IDENT "ssrtacarg"; ":"; "("; ssrtacarg; ")"
  | IDENT "ssrviewposspc"; ":"; "("; ssrviewpos; ")"
  | IDENT "ssrviewpos"; ":"; "("; ssrviewpos; ")"
  | IDENT "ssrhintref"; ":"; "("; ssrhintref; ")"
  | IDENT "ssrpatternarg"; ":"; "("; rpattern; ")"
  | IDENT "lcpattern"; ":"; "("; lcpattern; ")"
  | IDENT "cpattern"; ":"; "("; cpattern; ")"
  | IDENT "rpattern"; ":"; "("; rpattern; ")"
  | IDENT "firstorder_using"; ":"; "("; firstorder_using; ")"
  | IDENT "test"; ":"; "("; test; ")"
  | IDENT "comparison"; ":"; "("; comparison; ")"
  | IDENT "opthints"; ":"; "("; opthints; ")"
  | IDENT "auto_using"; ":"; "("; auto_using; ")"
  | IDENT "hintbases"; ":"; "("; hintbases; ")"
  | IDENT "eauto_search_strategy"; ":"; "("; eauto_search_strategy; ")"
  | IDENT "eauto_search_strategy_name"; ":"; "("; eauto_search_strategy_name;
    ")"
  | IDENT "debug"; ":"; "("; debug; ")"
  | IDENT "rewstrategy"; ":"; "("; rewstrategy; ")"
  | IDENT "glob_constr_with_bindings"; ":"; "("; constr_with_bindings; ")"
  | IDENT "strategy_level_or_var"; ":"; "("; strategy_level_or_var; ")"
  | IDENT "strategy_level"; ":"; "("; strategy_level; ")"
  | IDENT "test_lpar_id_colon"; ":"; "("; test_lpar_id_colon; ")"
  | IDENT "in_clause"; ":"; "("; in_clause; ")"
  | IDENT "by_arg_tac"; ":"; "("; by_arg_tac; ")"
  | IDENT "rename"; ":"; "("; rename; ")"
  | IDENT "hloc"; ":"; "("; hloc; ")"
  | IDENT "lglob"; ":"; "("; lconstr; ")"
  | IDENT "lconstr"; ":"; "("; lconstr; ")"
  | IDENT "glob"; ":"; "("; constr; ")"
  | IDENT "occurrences"; ":"; "("; occurrences; ")"
  | IDENT "natural"; ":"; "("; natural; ")"
  | IDENT "orient"; ":"; "("; orient; ")"
  | IDENT "ltac"; ":"; "("; ltac_expr LEVEL "5"; ")"
  | IDENT "open_constr"; ":"; "("; lconstr; ")"
  | IDENT "ipattern"; ":"; "("; simple_intropattern; ")"
  | IDENT "constr"; ":"; "("; lconstr; ")"
  | IDENT "uconstr"; ":"; "("; lconstr; ")"
  | IDENT "reference"; ":"; "("; reference; ")"
  | IDENT "ident"; ":"; "("; ident; ")"
  | IDENT "smart_global"; ":"; "("; smart_global; ")"
  | IDENT "string"; ":"; "("; string; ")"
  | IDENT "integer"; ":"; "("; integer; ")"
  | IDENT "fresh"; LIST0 fresh_id
  | IDENT "type_term"; uconstr
  | IDENT "numgoals"
  | constr_eval ] ]


<prompt>Rocq < 56 || 0 < </prompt>Timeout 1 Print LoadPath.
Logical Path / Physical path:
LF /home/abhishek/fv-workspace/BasicCoqTutorial
monad /home/abhishek/fv-workspace/_build/default/monad/monadproofs
monad.EVMOpSem /home/abhishek/fv-workspace/_build/default/monad/monadproofs/EVMOpSem
monad.EVMOpSem.Lem /home/abhishek/fv-workspace/_build/default/monad/monadproofs/EVMOpSem/Lem
monad.asts /home/abhishek/fv-workspace/_build/default/monad/monadproofs/asts
monad.fmai /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai
monad.fmai.driver /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/driver
monad.fmai.driver.ltac2 /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/driver/ltac2
monad.fmai.prompts /home/abhishek/fv-workspace/_build/default/monad/monadproofs/fmai/prompts
monad.proofs /home/abhishek/fv-workspace/_build/default/monad/monadproofs/proofs
monad.proofs.execproofs /home/abhishek/fv-workspace/_build/default/monad/monadproofs/proofs/execproofs
monad.tutorials /home/abhishek/fv-workspace/_build/default/monad/monadproofs/tutorials
monad /home/abhishek/fv-workspace/monad/monadproofs
monad.EVMOpSem /home/abhishek/fv-workspace/monad/monadproofs/EVMOpSem
monad.EVMOpSem.Lem /home/abhishek/fv-workspace/monad/monadproofs/EVMOpSem/Lem
monad.asts /home/abhishek/fv-workspace/monad/monadproofs/asts
monad.fmai /home/abhishek/fv-workspace/monad/monadproofs/fmai
monad.fmai.driver /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver
monad.fmai.driver.elisp /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver/elisp
monad.fmai.driver.ltac2 /home/abhishek/fv-workspace/monad/monadproofs/fmai/driver/ltac2
monad.fmai.prompts /home/abhishek/fv-workspace/monad/monadproofs/fmai/prompts
monad.proofs /home/abhishek/fv-workspace/monad/monadproofs/proofs
monad.proofs.execproofs /home/abhishek/fv-workspace/monad/monadproofs/proofs/execproofs
monad.tutorials /home/abhishek/fv-workspace/monad/monadproofs/tutorials
bluerock.ltac2.llm /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm
bluerock.ltac2.llm.plugin /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/plugin
bluerock.ltac2.llm.theories /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-llm/theories
bedrocktest /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/tests
Ltac2 /home/abhishek/fv-workspace/fmdeps/coq/user-contrib/Ltac2
Ltac2.Compat /home/abhishek/fv-workspace/fmdeps/coq/user-contrib/Ltac2/Compat
Corelib /home/abhishek/fv-workspace/fmdeps/coq/theories
Corelib.Array /home/abhishek/fv-workspace/fmdeps/coq/theories/Array
Corelib.BinNums /home/abhishek/fv-workspace/fmdeps/coq/theories/BinNums
Corelib.Classes /home/abhishek/fv-workspace/fmdeps/coq/theories/Classes
Corelib.Compat /home/abhishek/fv-workspace/fmdeps/coq/theories/Compat
Corelib.Floats /home/abhishek/fv-workspace/fmdeps/coq/theories/Floats
Corelib.Init /home/abhishek/fv-workspace/fmdeps/coq/theories/Init
Corelib.Lists /home/abhishek/fv-workspace/fmdeps/coq/theories/Lists
Corelib.Numbers /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers
Corelib.Numbers.Cyclic /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers/Cyclic
Corelib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/fmdeps/coq/theories/Numbers/Cyclic/Int63
Corelib.Program /home/abhishek/fv-workspace/fmdeps/coq/theories/Program
Corelib.Relations /home/abhishek/fv-workspace/fmdeps/coq/theories/Relations
Corelib.Setoids /home/abhishek/fv-workspace/fmdeps/coq/theories/Setoids
Corelib.Strings /home/abhishek/fv-workspace/fmdeps/coq/theories/Strings
Corelib.derive /home/abhishek/fv-workspace/fmdeps/coq/theories/derive
Corelib.extraction /home/abhishek/fv-workspace/fmdeps/coq/theories/extraction
Corelib.ssr /home/abhishek/fv-workspace/fmdeps/coq/theories/ssr
Corelib.ssrmatching /home/abhishek/fv-workspace/fmdeps/coq/theories/ssrmatching
Corelib /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories
Corelib.Array /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Array
Corelib.BinNums /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/BinNums
Corelib.Classes /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Classes
Corelib.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Compat
Corelib.Floats /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Floats
Corelib.Init /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Init
Corelib.Lists /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Lists
Corelib.Numbers /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers
Corelib.Numbers.Cyclic /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers/Cyclic
Corelib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Numbers/Cyclic/Int63
Corelib.Program /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Program
Corelib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Relations
Corelib.Setoids /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Setoids
Corelib.Strings /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/Strings
Corelib.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/derive
Corelib.extraction /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/extraction
Corelib.ssr /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/ssr
Corelib.ssrmatching /home/abhishek/fv-workspace/_build/default/fmdeps/coq/theories/ssrmatching
stdpp /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp
stdpp /home/abhishek/fv-workspace/_build/default/fmdeps/stdpp/stdpp
stdpp.bitvector /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp_bitvector
stdpp.unstable /home/abhishek/fv-workspace/fmdeps/stdpp/stdpp_unstable
Stdlib /home/abhishek/fv-workspace/fmdeps/stdlib/theories
Stdlib.All /home/abhishek/fv-workspace/fmdeps/stdlib/theories/All
Stdlib.Arith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Arith
Stdlib.Array /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Array
Stdlib.BinNums /home/abhishek/fv-workspace/fmdeps/stdlib/theories/BinNums
Stdlib.Bool /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Bool
Stdlib.Classes /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Classes
Stdlib.Compat /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Compat
Stdlib.FSets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/FSets
Stdlib.Floats /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Floats
Stdlib.Init /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Init
Stdlib.Lists /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Lists
Stdlib.Logic /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Logic
Stdlib.MSets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/MSets
Stdlib.NArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/NArith
Stdlib.Numbers /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers
Stdlib.Numbers.Cyclic /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic
Stdlib.Numbers.Cyclic.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic/Abstract
Stdlib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Cyclic/Int63
Stdlib.Numbers.Integer /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer
Stdlib.Numbers.Integer.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/Abstract
Stdlib.Numbers.Integer.Binary /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/Binary
Stdlib.Numbers.Integer.NatPairs /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Integer/NatPairs
Stdlib.Numbers.NatInt /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/NatInt
Stdlib.Numbers.Natural /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural
Stdlib.Numbers.Natural.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural/Abstract
Stdlib.Numbers.Natural.Binary /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Numbers/Natural/Binary
Stdlib.PArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/PArith
Stdlib.Program /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Program
Stdlib.QArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/QArith
Stdlib.Reals /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals
Stdlib.Reals.Abstract /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals/Abstract
Stdlib.Reals.Cauchy /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Reals/Cauchy
Stdlib.Relations /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Relations
Stdlib.Setoids /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Setoids
Stdlib.Sets /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Sets
Stdlib.Sorting /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Sorting
Stdlib.Streams /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Streams
Stdlib.Strings /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Strings
Stdlib.Structures /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Structures
Stdlib.Unicode /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Unicode
Stdlib.Vectors /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Vectors
Stdlib.Wellfounded /home/abhishek/fv-workspace/fmdeps/stdlib/theories/Wellfounded
Stdlib.ZArith /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ZArith
Stdlib.btauto /home/abhishek/fv-workspace/fmdeps/stdlib/theories/btauto
Stdlib.derive /home/abhishek/fv-workspace/fmdeps/stdlib/theories/derive
Stdlib.extraction /home/abhishek/fv-workspace/fmdeps/stdlib/theories/extraction
Stdlib.funind /home/abhishek/fv-workspace/fmdeps/stdlib/theories/funind
Stdlib.micromega /home/abhishek/fv-workspace/fmdeps/stdlib/theories/micromega
Stdlib.nsatz /home/abhishek/fv-workspace/fmdeps/stdlib/theories/nsatz
Stdlib.omega /home/abhishek/fv-workspace/fmdeps/stdlib/theories/omega
Stdlib.rtauto /home/abhishek/fv-workspace/fmdeps/stdlib/theories/rtauto
Stdlib.setoid_ring /home/abhishek/fv-workspace/fmdeps/stdlib/theories/setoid_ring
Stdlib.ssr /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ssr
Stdlib.ssrmatching /home/abhishek/fv-workspace/fmdeps/stdlib/theories/ssrmatching
Stdlib /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories
Stdlib.All /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/All
Stdlib.Arith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Arith
Stdlib.Array /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Array
Stdlib.BinNums /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/BinNums
Stdlib.Bool /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Bool
Stdlib.Classes /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Classes
Stdlib.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Compat
Stdlib.FSets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/FSets
Stdlib.Floats /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Floats
Stdlib.Init /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Init
Stdlib.Lists /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Lists
Stdlib.Logic /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Logic
Stdlib.MSets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/MSets
Stdlib.NArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/NArith
Stdlib.Numbers /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers
Stdlib.Numbers.Cyclic /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic
Stdlib.Numbers.Cyclic.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic/Abstract
Stdlib.Numbers.Cyclic.Int63 /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Cyclic/Int63
Stdlib.Numbers.Integer /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer
Stdlib.Numbers.Integer.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/Abstract
Stdlib.Numbers.Integer.Binary /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/Binary
Stdlib.Numbers.Integer.NatPairs /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Integer/NatPairs
Stdlib.Numbers.NatInt /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/NatInt
Stdlib.Numbers.Natural /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural
Stdlib.Numbers.Natural.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural/Abstract
Stdlib.Numbers.Natural.Binary /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Numbers/Natural/Binary
Stdlib.PArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/PArith
Stdlib.Program /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Program
Stdlib.QArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/QArith
Stdlib.Reals /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals
Stdlib.Reals.Abstract /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals/Abstract
Stdlib.Reals.Cauchy /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Reals/Cauchy
Stdlib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Relations
Stdlib.Setoids /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Setoids
Stdlib.Sets /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Sets
Stdlib.Sorting /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Sorting
Stdlib.Streams /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Streams
Stdlib.Strings /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Strings
Stdlib.Structures /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Structures
Stdlib.Unicode /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Unicode
Stdlib.Vectors /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Vectors
Stdlib.Wellfounded /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/Wellfounded
Stdlib.ZArith /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ZArith
Stdlib.btauto /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/btauto
Stdlib.derive /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/derive
Stdlib.extraction /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/extraction
Stdlib.funind /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/funind
Stdlib.micromega /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/micromega
Stdlib.nsatz /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/nsatz
Stdlib.omega /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/omega
Stdlib.rtauto /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/rtauto
Stdlib.setoid_ring /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/setoid_ring
Stdlib.ssr /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ssr
Stdlib.ssrmatching /home/abhishek/fv-workspace/_build/default/fmdeps/stdlib/theories/ssrmatching
bluerock.nova_interface /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories
bluerock.nova_interface.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64
bluerock.nova_interface.aarch64.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/opsem
bluerock.nova_interface.aarch64.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/aarch64/wp_nova
bluerock.nova_interface.hypercall /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/hypercall
bluerock.nova_interface.machine_logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/machine_logic
bluerock.nova_interface.model /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/model
bluerock.nova_interface.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/opsem
bluerock.nova_interface.predicates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/predicates
bluerock.nova_interface.upstream /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/upstream
bluerock.nova_interface.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/wp_nova
bluerock.nova_interface.x86_64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64
bluerock.nova_interface.x86_64.opsem /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/opsem
bluerock.nova_interface.x86_64.wp_nova /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-nova-interface/theories/x86_64/wp_nova
bluerock.elpi.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp
bluerock.elpi.cpp.Command /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Command
bluerock.elpi.cpp.Program /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Program
bluerock.elpi.cpp.Program.interp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Program/interp
bluerock.elpi.cpp.Tactic /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/Tactic
bluerock.elpi.cpp.internal /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/cpp/internal
bluerock.elpi.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp
bluerock.elpi.cpp.Command /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Command
bluerock.elpi.cpp.Program /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Program
bluerock.elpi.cpp.Program.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Program/interp
bluerock.elpi.cpp.Tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/Tactic
bluerock.elpi.cpp.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/elpi-cpp/cpp/internal
bluerock_tests.elpi.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/elpi-cpp/tests
bluerock /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories
bluerock.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/algebra
bluerock.auto /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto
bluerock.auto.big_sep /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/big_sep
bluerock.auto.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp
bluerock.auto.cpp.auto_frac /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/auto_frac
bluerock.auto.cpp.database /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/database
bluerock.auto.cpp.default_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/default_spec
bluerock.auto.cpp.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi
bluerock.auto.cpp.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/derive
bluerock.auto.cpp.elpi.enum /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum
bluerock.auto.cpp.elpi.enum.variant /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum/variant
bluerock.auto.cpp.elpi.synth /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth
bluerock.auto.cpp.elpi.synth.both /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/both
bluerock.auto.cpp.elpi.synth.interp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp
bluerock.auto.cpp.elpi.synth.interp.model
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/model
bluerock.auto.cpp.elpi.synth.interp.rep
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/rep
bluerock.auto.cpp.elpi.synth.synterp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp
bluerock.auto.cpp.elpi.synth.synterp.rep
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp/rep
bluerock.auto.cpp.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints
bluerock.auto.cpp.hints.ptrs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints/ptrs
bluerock.auto.cpp.pretty /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/pretty
bluerock.auto.cpp.specs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/specs
bluerock.auto.cpp.templates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates
bluerock.auto.cpp.templates.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/hints
bluerock.auto.cpp.templates.logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/logic
bluerock.auto.cpp.templates.semantics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/semantics
bluerock.auto.cpp.templates.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/spec
bluerock.auto.cpp.templates.syntax /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/syntax
bluerock.auto.cpp.templates.upstream /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream
bluerock.auto.cpp.templates.upstream.ast
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/ast
bluerock.auto.cpp.templates.upstream.bi
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/bi
bluerock.auto.cpp.templates.upstream.brick
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/brick
bluerock.auto.cpp.templates.upstream.prelude
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/prelude
bluerock.auto.cpp.templates.verif /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/verif
bluerock.auto.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi
bluerock.auto.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi/derive
bluerock.auto.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/hints
bluerock.auto.lemmas /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/lemmas
bluerock.auto.pure /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/pure
bluerock.auto.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/tactics
bluerock.base_logic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic
bluerock.base_logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic/lib
bluerock.bi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/bi
bluerock.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp
bluerock.cpp.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp/spec
bluerock.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/lib
bluerock.micromega /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/micromega
bluerock.prelude /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude
bluerock.prelude.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/elpi
bluerock.prelude.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics
bluerock.prelude.tactics.ltac2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics/ltac2
bluerock.proofmode /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode
bluerock.proofmode.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode/cpp
bluerock /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories
bluerock.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/algebra
bluerock.auto /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto
bluerock.auto.big_sep /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/big_sep
bluerock.auto.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp
bluerock.auto.cpp.auto_frac /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/auto_frac
bluerock.auto.cpp.database /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/database
bluerock.auto.cpp.default_spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/default_spec
bluerock.auto.cpp.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi
bluerock.auto.cpp.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/derive
bluerock.auto.cpp.elpi.enum /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum
bluerock.auto.cpp.elpi.enum.variant
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/enum/variant
bluerock.auto.cpp.elpi.synth /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth
bluerock.auto.cpp.elpi.synth.both
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/both
bluerock.auto.cpp.elpi.synth.interp
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp
bluerock.auto.cpp.elpi.synth.interp.model
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/model
bluerock.auto.cpp.elpi.synth.interp.rep
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/interp/rep
bluerock.auto.cpp.elpi.synth.synterp
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp
bluerock.auto.cpp.elpi.synth.synterp.rep
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/elpi/synth/synterp/rep
bluerock.auto.cpp.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints
bluerock.auto.cpp.hints.ptrs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/hints/ptrs
bluerock.auto.cpp.pretty /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/pretty
bluerock.auto.cpp.specs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/specs
bluerock.auto.cpp.templates /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates
bluerock.auto.cpp.templates.hints
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/hints
bluerock.auto.cpp.templates.logic
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/logic
bluerock.auto.cpp.templates.semantics
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/semantics
bluerock.auto.cpp.templates.spec
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/spec
bluerock.auto.cpp.templates.syntax
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/syntax
bluerock.auto.cpp.templates.upstream
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream
bluerock.auto.cpp.templates.upstream.ast
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/ast
bluerock.auto.cpp.templates.upstream.bi
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/bi
bluerock.auto.cpp.templates.upstream.brick
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/brick
bluerock.auto.cpp.templates.upstream.prelude
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/upstream/prelude
bluerock.auto.cpp.templates.verif
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/cpp/templates/verif
bluerock.auto.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi
bluerock.auto.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/elpi/derive
bluerock.auto.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/hints
bluerock.auto.lemmas /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/lemmas
bluerock.auto.pure /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/pure
bluerock.auto.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/auto/tactics
bluerock.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic
bluerock.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/base_logic/lib
bluerock.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/bi
bluerock.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp
bluerock.cpp.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/cpp/spec
bluerock.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/lib
bluerock.micromega /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/micromega
bluerock.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude
bluerock.prelude.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/elpi
bluerock.prelude.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics
bluerock.prelude.tactics.ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/prelude/tactics/ltac2
bluerock.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode
bluerock.proofmode.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-cpp/theories/proofmode/cpp
bluerock_auto.tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests
bluerock_auto.tests.anonymous_union /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/anonymous_union
bluerock_auto.tests.arch_indep /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep
bluerock_auto.tests.arch_indep.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep/aarch64
bluerock_auto.tests.arch_indep.x86_64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arch_indep/x86_64
bluerock_auto.tests.arith /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/arith
bluerock_auto.tests.array /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/array
bluerock_auto.tests.ast /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/ast
bluerock_auto.tests.brick_eval /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/brick_eval
bluerock_auto.tests.brick_eval.bad /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/brick_eval/bad
bluerock_auto.tests.casts /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/casts
bluerock_auto.tests.const /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/const
bluerock_auto.tests.constants /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/constants
bluerock_auto.tests.control_flow /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/control_flow
bluerock_auto.tests.cpp_proof /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/cpp_proof
bluerock_auto.tests.cpp_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/cpp_spec
bluerock_auto.tests.data_class /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/data_class
bluerock_auto.tests.dataclass_demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/dataclass_demo
bluerock_auto.tests.derive /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/derive
bluerock_auto.tests.duck_types /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/duck_types
bluerock_auto.tests.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi
bluerock_auto.tests.elpi.enums /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi/enums
bluerock_auto.tests.elpi.specifications /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/elpi/specifications
bluerock_auto.tests.fields /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/fields
bluerock_auto.tests.fupd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/fupd
bluerock_auto.tests.inc /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inc
bluerock_auto.tests.includes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/includes
bluerock_auto.tests.inheritence /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inheritence
bluerock_auto.tests.inits /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/inits
bluerock_auto.tests.io /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/io
bluerock_auto.tests.lambda /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lambda
bluerock_auto.tests.lazy_unfold /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lazy_unfold
bluerock_auto.tests.lib_alloc /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/lib_alloc
bluerock_auto.tests.llist /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/llist
bluerock_auto.tests.llist_cpp /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/llist_cpp
bluerock_auto.tests.local_scope /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/local_scope
bluerock_auto.tests.micromega /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/micromega
bluerock_auto.tests.misc_tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/misc_tests
bluerock_auto.tests.new_delete /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/new_delete
bluerock_auto.tests.operator_auto /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/operator_auto
bluerock_auto.tests.params /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/params
bluerock_auto.tests.perf /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/perf
bluerock_auto.tests.pretty /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/pretty
bluerock_auto.tests.read_prim /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/read_prim
bluerock_auto.tests.reps /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/reps
bluerock_auto.tests.return_void /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/return_void
bluerock_auto.tests.simple /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/simple
bluerock_auto.tests.spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/spec
bluerock_auto.tests.specify /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify
bluerock_auto.tests.specify.challenge /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify/challenge
bluerock_auto.tests.specify.copymove /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify/copymove
bluerock_auto.tests.specify_cmd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/specify_cmd
bluerock_auto.tests.static_methods /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/static_methods
bluerock_auto.tests.synth_names /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/synth_names
bluerock_auto.tests.tactics4 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/tactics4
bluerock_auto.tests.templates /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/templates
bluerock_auto.tests.union /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/union
bluerock_auto.tests.universes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/universes
bluerock_auto.tests.unlocked /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/unlocked
bluerock_auto.tests.val_cat /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/val_cat
bluerock_auto.tests.validate_spec /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/validate_spec
bluerock_auto.tests.var_args /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/var_args
bluerock_auto.tests.virtual /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/virtual
bluerock_auto.tests.virtual.mdc_noimpl /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-cpp/tests/virtual/mdc_noimpl
bluerock.hw_models.gic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/gic
bluerock.hw_models.cpu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu
bluerock.hw_models.cpu.inst /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/inst
bluerock.hw_models.cpu.inst.sail /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/inst/sail
bluerock.hw_models.cpu.msr /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/cpu/msr
bluerock.hw_models.core /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core
bluerock.hw_models.core.ip /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models/theories/core/ip
bluerock_auto_core.examples /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples
bluerock_auto_core.examples.classes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples/classes
bluerock_auto_core.examples.tutorial /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/examples/tutorial
bluerock.auto.core /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories
bluerock.auto.core.hints /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints
bluerock.auto.core.hints.classes /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/classes
bluerock.auto.core.hints.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/lib
bluerock.auto.core.internal /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal
bluerock.auto.core.internal.VM /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/VM
bluerock.auto.core.internal.instr /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/instr
bluerock.auto.core.internal.lib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/lib
bluerock.auto.core.internal.ltac2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/ltac2
bluerock.auto.core.internal.plib /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plib
bluerock.auto.core.internal.plugins /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plugins
bluerock.auto.core.internal.syntactic_bi /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi
bluerock.auto.core.internal.syntactic_bi.forced
  /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi/forced
bluerock.auto.core.internal.tactic /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/tactic
bluerock.auto.core /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories
bluerock.auto.core.hints /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints
bluerock.auto.core.hints.classes /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/classes
bluerock.auto.core.hints.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/hints/lib
bluerock.auto.core.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal
bluerock.auto.core.internal.VM /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/VM
bluerock.auto.core.internal.instr /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/instr
bluerock.auto.core.internal.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/lib
bluerock.auto.core.internal.ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/ltac2
bluerock.auto.core.internal.plib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plib
bluerock.auto.core.internal.plugins /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/plugins
bluerock.auto.core.internal.syntactic_bi
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi
bluerock.auto.core.internal.syntactic_bi.forced
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/syntactic_bi/forced
bluerock.auto.core.internal.tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v/coq-bluerock-auto-core/theories/internal/tactic
bluerock_auto_core.tests /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests
bluerock_auto_core.tests.cancelx /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/cancelx
bluerock_auto_core.tests.fwd /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/fwd
bluerock_auto_core.tests.id /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/id
bluerock_auto_core.tests.learn /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/learn
bluerock_auto_core.tests.observe /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-auto-core/tests/observe
bluerock.cpp.demo /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof
bluerock.cpp.demo.aggregate01 /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/aggregate01
bluerock.cpp.demo.basic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/basic
bluerock.cpp.demo.data_class /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/data_class
bluerock.cpp.demo.inline /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/inline
bluerock.cpp.demo.loops /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-demo/proof/loops
bluerock.lts_adequacy_demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories
bluerock.lts_adequacy_demo.example /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example
bluerock.lts_adequacy_demo.example.apps /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/apps
bluerock.lts_adequacy_demo.example.languages /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/languages
bluerock.lts_adequacy_demo.example.logics /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/logics
bluerock.lts_adequacy_demo.example.lts /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/lts
bluerock.lts_adequacy_demo.example.programs /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/example/programs
bluerock.lts_adequacy_demo.iris /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/iris
bluerock.lts_adequacy_demo.refinement /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-lts-adequacy/theories/refinement
bluerock.cpp.stdlib /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories
bluerock.cpp.stdlib.allocator /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/allocator
bluerock.cpp.stdlib.atomic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/atomic
bluerock.cpp.stdlib.cassert /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/cassert
bluerock.cpp.stdlib.concepts /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/concepts
bluerock.cpp.stdlib.exception /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/exception
bluerock.cpp.stdlib.new /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/new
bluerock.cpp.stdlib.vector /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/theories/vector
bluerock.cpp.stdlib.test /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests
bluerock.cpp.stdlib.test.atomic /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/atomic
bluerock.cpp.stdlib.test.concepts /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/concepts
bluerock.cpp.stdlib.test.vector /home/abhishek/fv-workspace/fmdeps/cpp2v/rocq-bluerock-cpp-stdlib/tests/vector
bluerock.hw_models /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories
bluerock.hw_models.computer2 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/computer2
bluerock.hw_models.demo /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/demo
bluerock.hw_models.mmu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/mmu
bluerock.hw_models.smmu /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/smmu
bluerock.hw_models.smmu.aarch64 /home/abhishek/fv-workspace/fmdeps/cpp2v/coq-bluerock-hw-models-extra/theories/smmu/aarch64
Equations.TestSuite /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite
Equations.TestSuite.HoTT /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/HoTT
Equations.TestSuite.disabled /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/disabled
Equations.TestSuite.issues /home/abhishek/fv-workspace/fmdeps/coq-equations/test-suite/issues
Equations.Examples /home/abhishek/fv-workspace/fmdeps/coq-equations/examples
Equations.Examples.disabled /home/abhishek/fv-workspace/fmdeps/coq-equations/examples/disabled
Equations /home/abhishek/fv-workspace/fmdeps/coq-equations/theories
Equations.HoTT /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/HoTT
Equations.Type /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/Type
Equations /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories
Equations.Type /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories/Type
Equations.Prop /home/abhishek/fv-workspace/fmdeps/coq-equations/theories/Prop
Equations.Prop /home/abhishek/fv-workspace/_build/default/fmdeps/coq-equations/theories/Prop
elpi.apps.coercion /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/coercion/theories
elpi.apps.coercion.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/coercion/tests
elpi.apps.locker.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/elpi
elpi.apps.locker /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/locker/theories
elpi.apps.locker /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/locker/theories
elpi.apps.locker.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/locker/tests
elpi.apps.derive.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/elpi
elpi.apps.derive.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/examples
elpi.apps.derive /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/theories
elpi.apps.derive.derive /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/theories/derive
elpi.apps.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/theories
elpi.apps.derive.derive /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/derive/theories/derive
elpi.apps.derive.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/derive/tests
elpi.apps.tc /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/theories
elpi.apps.tc.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests
elpi.apps.tc.tests.WIP /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/WIP
elpi.apps.tc.tests.WIP.premisesSort /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/WIP/premisesSort
elpi.apps.tc.tests.importOrder /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/importOrder
elpi.apps.tc.tests.register /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/tc/tests/register
elpi.apps.cs /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/cs/theories
elpi.apps.eltac.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/examples
elpi.apps.eltac /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/theories
elpi.apps.eltac.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/eltac/tests
elpi.apps.NES.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/elpi
elpi.apps.NES.examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/examples
elpi.apps.NES /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/theories
elpi.apps.NES /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/apps/NES/theories
elpi.apps.NES.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/apps/NES/tests
elpi_elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/elpi
elpi_examples /home/abhishek/fv-workspace/fmdeps/coq-elpi/examples
elpi /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories
elpi.attic /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/attic
elpi.core /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/core
elpi.wip /home/abhishek/fv-workspace/fmdeps/coq-elpi/theories/wip
elpi /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/theories
elpi.core /home/abhishek/fv-workspace/_build/default/fmdeps/coq-elpi/theories/core
elpi.tests /home/abhishek/fv-workspace/fmdeps/coq-elpi/tests
iris.unstable /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable
iris.unstable.algebra /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/algebra
iris.unstable.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/base_logic
iris.unstable.heap_lang /home/abhishek/fv-workspace/fmdeps/iris/iris_unstable/heap_lang
iris.deprecated /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated
iris.deprecated.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated/base_logic
iris.deprecated.program_logic /home/abhishek/fv-workspace/fmdeps/iris/iris_deprecated/program_logic
iris.heap_lang /home/abhishek/fv-workspace/fmdeps/iris/iris_heap_lang
iris.heap_lang.lib /home/abhishek/fv-workspace/fmdeps/iris/iris_heap_lang/lib
iris /home/abhishek/fv-workspace/fmdeps/iris/iris
iris.algebra /home/abhishek/fv-workspace/fmdeps/iris/iris/algebra
iris.algebra.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/algebra/lib
iris.base_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/base_logic
iris.base_logic.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/base_logic/lib
iris.bi /home/abhishek/fv-workspace/fmdeps/iris/iris/bi
iris.bi.lib /home/abhishek/fv-workspace/fmdeps/iris/iris/bi/lib
iris.prelude /home/abhishek/fv-workspace/fmdeps/iris/iris/prelude
iris.program_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/program_logic
iris.proofmode /home/abhishek/fv-workspace/fmdeps/iris/iris/proofmode
iris.si_logic /home/abhishek/fv-workspace/fmdeps/iris/iris/si_logic
iris /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris
iris.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/algebra
iris.algebra.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/algebra/lib
iris.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/base_logic
iris.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/base_logic/lib
iris.bi /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/bi
iris.bi.lib /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/bi/lib
iris.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/prelude
iris.program_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/program_logic
iris.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/proofmode
iris.si_logic /home/abhishek/fv-workspace/_build/default/fmdeps/iris/iris/si_logic
AAC_tactics /home/abhishek/fv-workspace/fmdeps/aac-tactics/theories
AAC_tactics /home/abhishek/fv-workspace/_build/default/fmdeps/aac-tactics/theories
ExtLibExamples /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/examples
ExtLib /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories
ExtLib.Core /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Core
ExtLib.Data /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data
ExtLib.Data.Eq /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Eq
ExtLib.Data.Graph /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Graph
ExtLib.Data.Map /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Map
ExtLib.Data.Monads /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Monads
ExtLib.Data.Set /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Data/Set
ExtLib.Generic /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Generic
ExtLib.Programming /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Programming
ExtLib.Recur /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Recur
ExtLib.Relations /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Relations
ExtLib.Structures /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Structures
ExtLib.Tactics /home/abhishek/fv-workspace/fmdeps/coq-ext-lib/theories/Tactics
ExtLib /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories
ExtLib.Core /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Core
ExtLib.Data /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data
ExtLib.Data.Eq /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Eq
ExtLib.Data.Graph /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Graph
ExtLib.Data.Map /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Map
ExtLib.Data.Monads /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Monads
ExtLib.Data.Set /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Data/Set
ExtLib.Generic /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Generic
ExtLib.Programming /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Programming
ExtLib.Recur /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Recur
ExtLib.Relations /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Relations
ExtLib.Structures /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Structures
ExtLib.Tactics /home/abhishek/fv-workspace/_build/default/fmdeps/coq-ext-lib/theories/Tactics
bluerock.prelude /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories
bluerock.prelude.arith /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/arith
bluerock.prelude.axioms /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/axioms
bluerock.prelude.elpi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi
bluerock.prelude.elpi.derive /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi/derive
bluerock.prelude.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/tactics
bluerock.prelude /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories
bluerock.prelude.arith /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/arith
bluerock.prelude.axioms /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/axioms
bluerock.prelude.elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi
bluerock.prelude.elpi.derive /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/elpi/derive
bluerock.prelude.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-prelude/theories/tactics
Lens /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-lens/Lens
Lens.Elpi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-lens/Lens/Elpi
Lens /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-lens/Lens
Lens.Elpi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-lens/Lens/Elpi
bluerock.ltac2.llm /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-llm/theories
bluerock.ltac2.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/theories
bluerock.ltac2.extra.internal /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/theories/internal
bluerock.ltac2.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/theories
bluerock.ltac2.extra.internal /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/theories/internal
bluerock_tests.ltac2.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-extra/tests
bluerock_tests.ltac2.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-extra/tests
bluerock.iris.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories
bluerock.iris.extra.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/algebra
bluerock.iris.extra.base_logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic
bluerock.iris.extra.base_logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic/lib
bluerock.iris.extra.bi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi
bluerock.iris.extra.bi.spec /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi/spec
bluerock.iris.extra.proofmode /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/proofmode
bluerock.iris.extra.si_logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/si_logic
bluerock.iris.extra.tactics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/tactics
bluerock.iris.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories
bluerock.iris.extra.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/algebra
bluerock.iris.extra.base_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic
bluerock.iris.extra.base_logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/base_logic/lib
bluerock.iris.extra.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi
bluerock.iris.extra.bi.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/bi/spec
bluerock.iris.extra.proofmode /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/proofmode
bluerock.iris.extra.si_logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/si_logic
bluerock.iris.extra.tactics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-iris/theories/tactics
bluerock.ltac2.logger /home/abhishek/fv-workspace/fmdeps/cpp2v-core/ltac2-logger/theories
bluerock.ltac2.logger /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/ltac2-logger/theories
accumulate_bug /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/accumulate_bug
accumulate_bug /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/accumulate_bug
bluerock.elpi.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra
bluerock.elpi.extra.Command /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Command
bluerock.elpi.extra.Command.both /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Command/both
bluerock.elpi.extra.Program /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program
bluerock.elpi.extra.Program.both /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program/both
bluerock.elpi.extra.Program.interp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Program/interp
bluerock.elpi.extra.Tactic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/Tactic
bluerock.elpi.extra.TacticCommand /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand
bluerock.elpi.extra.TacticCommand.interp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand/interp
bluerock.elpi.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra
bluerock.elpi.extra.Command /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Command
bluerock.elpi.extra.Command.both /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Command/both
bluerock.elpi.extra.Program /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program
bluerock.elpi.extra.Program.both /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program/both
bluerock.elpi.extra.Program.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Program/interp
bluerock.elpi.extra.Tactic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/Tactic
bluerock.elpi.extra.TacticCommand /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand
bluerock.elpi.extra.TacticCommand.interp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/extra/TacticCommand/interp
bluerock_tests.elpi.extra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/tests
bluerock_tests.elpi.extra.NES /home/abhishek/fv-workspace/fmdeps/cpp2v-core/elpi-extra/tests/NES
bluerock_tests.elpi.extra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/tests
bluerock_tests.elpi.extra.NES /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/elpi-extra/tests/NES
bluerock.noimport /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport
bluerock.noimport.doc /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc
bluerock.noimport.doc.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc/cpp
bluerock.noimport /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport
bluerock.noimport.doc /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc
bluerock.noimport.doc.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/noimport/doc/cpp
bluerock.lang.cpp /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp
bluerock.lang.cpp.algebra /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/algebra
bluerock.lang.cpp.bi /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi
bluerock.lang.cpp.bi.spec /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi/spec
bluerock.lang.cpp.logic /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic
bluerock.lang.cpp.logic.heap_pred /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/heap_pred
bluerock.lang.cpp.logic.lib /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/lib
bluerock.lang.cpp.model /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/model
bluerock.lang.cpp.mparser /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/mparser
bluerock.lang.cpp.parser /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser
bluerock.lang.cpp.parser.plugin /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser/plugin
bluerock.lang.cpp.semantics /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/semantics
bluerock.lang.cpp.specs /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/specs
bluerock.lang.cpp.syntax /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax
bluerock.lang.cpp.syntax.name_notation
  /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax/name_notation
bluerock.lang.cpp /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp
bluerock.lang.cpp.algebra /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/algebra
bluerock.lang.cpp.bi /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi
bluerock.lang.cpp.bi.spec /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/bi/spec
bluerock.lang.cpp.logic /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic
bluerock.lang.cpp.logic.heap_pred
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/heap_pred
bluerock.lang.cpp.logic.lib /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/logic/lib
bluerock.lang.cpp.model /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/model
bluerock.lang.cpp.mparser /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/mparser
bluerock.lang.cpp.parser /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser
bluerock.lang.cpp.parser.plugin
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/parser/plugin
bluerock.lang.cpp.semantics /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/semantics
bluerock.lang.cpp.specs /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/specs
bluerock.lang.cpp.syntax /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax
bluerock.lang.cpp.syntax.name_notation
  /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-bluerock-brick/theories/lang/cpp/syntax/name_notation
tc_db_info /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-tc-db-info/theories
tc_db_info /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-tc-db-info/theories
bluerock.upoly /home/abhishek/fv-workspace/fmdeps/cpp2v-core/rocq-upoly/upoly
bluerock.upoly /home/abhishek/fv-workspace/_build/default/fmdeps/cpp2v-core/rocq-upoly/upoly
<> /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib
Ltac2 /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib/Ltac2
Ltac2.Compat /home/abhishek/fv-workspace/_build/default/fmdeps/coq/user-contrib/Ltac2/Compat

<prompt>Rocq < 57 || 0 < </prompt>
 *)



(*
User: # General Background
This is a Coq programming task. First, some general guidelines about Coq programming tasks.

## Admitting holes (defer less critical/important parts)
Complex Coq programs are often written in multiple steps. 
Coq allows us to "admit" helper functions temporarily so that they can be defined later.
However, in that case, you need to come up with the type of the helper function. 
For example, you admit a helper function to convert a Z to a String.string, as follows"

```coq
Definition Ztostring (z: Z) : String.string. Admitted.
```
This mechanism allows you to get the higher-level details right before implementing the low-level obvious details.

## Error Messages
You are talking to an automated bot that will process your responses. If the Coq program you emit has errors, this bot will respond with the errors emitted by Coq.
Here are some general tips to avoid errors:
1) Use qualified names to avoid conflicts
2) Do not make any assumptions about the open notation scopes. For example, if you mean `Z.add 1 2`, write `(1+2)%Z` instead.

## Coq Vernacular Queries instead of Hallucinations
If you are not sure about the exact name of a definition/fixpoint/inductive in the standard library or the libraries availble to you can issue Coq queries to get more information about the available context. Some of the widely used queries are Search/About/Check/Locate. Here are some examples of search:

Search (nat -> nat). (* search the library for items of type nat -> nat *)

Search (nat -> list ?a -> list ?a). (* unification variables can be used to constrain occurrences: e.g. here the 2 occurrences of ?a must match the same term *)

About Nat.add (* show documentation for an item *)

Check (Nat.add 1 1). (* check type of a term *)

Locate nat. (* print the possible fully qualified name(s) of `nat`. unless the user defined their own `nat` type, this will print `Corelib.Init.Datatypes.nat` . this will print multiple items if there are several items whose fully qualified names have `nat` as the leaf, e.g. `A.nat`, `Corelib.Init.Datatypes.nat`. It would also print shorter names for each fully qualified name. The shorter name depends on the set and order of Imports in the current file. When writing Coq code, you should refer to the located item by a name not any shorter than the shorter name mentioned here: the longer the better as that is robust to moving code around where the order of imports are different. *)

Use the queries judiciously. Be very careful with `Search`: it can return too many items unless you chose a fairly discriminative query to rule out what you dont want.

## Mutual Inductives
If you want do define a function that recurses on inductive data, you typically use the `Fixpoint` keyword. If the inductive type is mutually indutive with other types, often the needed recursion is also mutually recursive. In such cases, you need to define your function using mutual Fixpoints. Below is an exampe:

```gallina
(* Define mutual inductive types Expr and ExprList. the type of at least one constructor of each mutual inductive type refers to the other mutual inductive type *)
Inductive Expr : Type :=
| Const : nat -> Expr
| Add : Expr -> Expr -> Expr
| Seq : ExprList -> Expr
with ExprList : Type :=
| ENil : ExprList
| ECons : Expr -> ExprList -> ExprList.

Fixpoint eval_expr (e : Expr) : nat :=
  match e with
  | Const n => n
  | Add e1 e2 => eval_expr e1 + eval_expr e2
  | Seq el => eval_list el
  end
with eval_list (l : ExprList) : nat :=
  match l with
  | ENil => 0
  | ECons e rest => eval_expr e + eval_list rest
  end.
  
```

# Current Task
I want you to write a Coq function to pretty print Stmt, an Inductive type I have defined for C++ statements. the type should be Stmt -> String.string.
# Response Format (IMPORTANT)
You can either give me the anwer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```. 
If you do not follow this format, my automated engine cannot parse your response.
An example of a valid response is:
```coqquery
Print Stmt.
```
An examplf of an answer (not to the the current task) is:
```gallina
Definition foo : nat := 1+2.
```

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasnt available in the queries you have issued so far.

Assistant: We need to know the exact constructors of your `Stmt` inductive in order to write a tailored pretty-printer. Let’s inspect its definition first:

```coqquery
Print Stmt.
```
User: Notation Stmt := Stmt

Inductive name' : Set :=
    Ninst : name → list temp_arg → name
  | Nglobal : atomic_name → name
  | Ndependent : type → name
  | Nscoped : name → atomic_name → name
  | Nunsupported : string → name
  with temp_arg' : Set :=
    Atype : type → temp_arg
  | Avalue : Expr → temp_arg
  | Apack : list temp_arg → temp_arg
  | Atemplate : name → temp_arg
  | Aunsupported : string → temp_arg
  with type' : Set :=
    Tparam : ident → type
  | Tresult_param : ident → type
  | Tresult_global : name → type
  | Tresult_unop : RUnOp → type → type
  | Tresult_binop : RBinOp → type → type → type
  | Tresult_call : name → list type → type
  | Tresult_member_call : name → type → list type → type
  | Tresult_parenlist : type → list type → type
  | Tresult_member : type → name → type
  | Tptr : type → type
  | Tref : type → type
  | Trv_ref : type → type
  | Tnum : int_rank → signed → type
  | Tchar_ : char_type → type
  | Tvoid : type
  | Tarray : type → N → type
  | Tincomplete_array : type → type
  | Tvariable_array : type → Expr → type
  | Tnamed : name → type
  | Tenum : name → type
  | Tfunction : function_type_ type → type
  | Tbool : type
  | Tmember_pointer : type → type → type
  | Tfloat_ : float_type.t → type
  | Tqualified : type_qualifiers → type → type
  | Tnullptr : type
  | Tarch : option bitsize → string → type
  | Tdecltype : Expr → type
  | Texprtype : Expr → type
  | Tunsupported : string → type
  with Expr' : Set :=
    Eparam : ident → Expr
  | Eunresolved_global : name → Expr
  | Eunresolved_unop : RUnOp → Expr → Expr
  | Eunresolved_binop : RBinOp → Expr → Expr → Expr
  | Eunresolved_call : name → list Expr → Expr
  | Eunresolved_member_call : name → Expr → list Expr → Expr
  | Eunresolved_parenlist : option type → list Expr → Expr
  | Eunresolved_member : Expr → name → Expr
  | Evar : localname → type → Expr
  | Eenum_const : name → ident → Expr
  | Eglobal : name → type → Expr
  | Eglobal_member : name → type → Expr
  | Echar : N → type → Expr
  | Estring : literal_string.t → type → Expr
  | Eint : Z → type → Expr
  | Ebool : bool → Expr
  | Eunop : UnOp → Expr → type → Expr
  | Ebinop : BinOp → Expr → Expr → type → Expr
  | Ederef : Expr → type → Expr
  | Eaddrof : Expr → Expr
  | Eassign : Expr → Expr → type → Expr
  | Eassign_op : BinOp → Expr → Expr → type → Expr
  | Epreinc : Expr → type → Expr
  | Epostinc : Expr → type → Expr
  | Epredec : Expr → type → Expr
  | Epostdec : Expr → type → Expr
  | Eseqand : Expr → Expr → Expr
  | Eseqor : Expr → Expr → Expr
  | Ecomma : Expr → Expr → Expr
  | Ecall : Expr → list Expr → Expr
  | Eexplicit_cast : cast_style.t → type → Expr → Expr
  | Ecast : Cast → Expr → Expr
  | Emember : bool → Expr → atomic_name → bool → type → Expr
  | Emember_ignore : bool → Expr → Expr → Expr
  | Emember_call : bool → MethodRef_ name type Expr → Expr → list Expr → Expr
  | Eoperator_call : OverloadableOperator → operator_impl.t name type → list Expr → Expr
  | Esubscript : Expr → Expr → type → Expr
  | Esizeof : type + Expr → type → Expr
  | Ealignof : type + Expr → type → Expr
  | Eoffsetof : type → ident → type → Expr
  | Econstructor : name → list Expr → type → Expr
  | Elambda : name → list Expr → Expr
  | Eimplicit : Expr → Expr
  | Eimplicit_init : type → Expr
  | Eif : Expr → Expr → Expr → type → Expr
  | Eif2 : N → Expr → Expr → Expr → Expr → type → Expr
  | Ethis : type → Expr
  | Enull : Expr
  | Einitlist : list Expr → option Expr → type → Expr
  | Einitlist_union : atomic_name → option Expr → type → Expr
  | Enew : name * type → list Expr → new_form → type → option Expr → option Expr → Expr
  | Edelete : bool → name → Expr → type → Expr
  | Eandclean : Expr → Expr
  | Ematerialize_temp : Expr → ValCat → Expr
  | Eatomic : AtomicOp → list Expr → type → Expr
  | Estmt : Stmt → type → Expr
  | Eva_arg : Expr → type → Expr
  | Epseudo_destructor : bool → type → Expr → Expr
  | Earrayloop_init : N → Expr → N → N → Expr → type → Expr
  | Earrayloop_index : N → type → Expr
  | Eopaque_ref : N → type → Expr
  | Eunsupported : string → type → Expr
  with Stmt' : Set :=
    Sseq : list Stmt → Stmt
  | Sdecl : list VarDecl → Stmt
  | Sif : option VarDecl → Expr → Stmt → Stmt → Stmt
  | Sif_consteval : Stmt → Stmt → Stmt
  | Swhile : option VarDecl → Expr → Stmt → Stmt
  | Sfor : option Stmt → option Expr → option Expr → Stmt → Stmt
  | Sdo : Stmt → Expr → Stmt
  | Sswitch : option VarDecl → Expr → Stmt → Stmt
  | Scase : SwitchBranch → Stmt
  | Sdefault : Stmt
  | Sbreak : Stmt
  | Scontinue : Stmt
  | Sreturn : option Expr → Stmt
  | Sexpr : Expr → Stmt
  | Sattr : list ident → Stmt → Stmt
  | Sasm : string → bool → list (ident * Expr) → list (ident * Expr) → list ident → Stmt
  | Slabeled : ident → Stmt → Stmt
  | Sgoto : ident → Stmt
  | Sunsupported : string → Stmt
  with VarDecl' : Set :=
    Dvar : localname → type → option Expr → VarDecl
  | Ddecompose : Expr → ident → list BindingDecl → VarDecl
  | Dinit : bool → name → type → option Expr → VarDecl
  with BindingDecl' : Set :=
    Bvar : localname → type → Expr → BindingDecl | Bbind : localname → type → Expr → BindingDecl
  with Cast' : Set :=
    Cdependent : type → Cast
  | Cbitcast : type → Cast
  | Clvaluebitcast : type → Cast
  | Cl2r : Cast
  | Cl2r_bitcast : type → Cast
  | Cnoop : type → Cast
  | Carray2ptr : Cast
  | Cfun2ptr : Cast
  | Cint2ptr : type → Cast
  | Cptr2int : type → Cast
  | Cptr2bool : Cast
  | Cintegral : type → Cast
  | Cint2bool : Cast
  | Cfloat2int : type → Cast
  | Cint2float : type → Cast
  | Cfloat : type → Cast
  | Cnull2ptr : type → Cast
  | Cnull2memberptr : type → Cast
  | Cbuiltin2fun : type → Cast
  | C2void : Cast
  | Cctor : type → Cast
  | Cuser : Cast
  | Cdynamic : type → Cast
  | Cderived2base : list type → type → Cast
  | Cbase2derived : list type → type → Cast
  | Cunsupported : bs → type → Cast.

Arguments Ninst c%_cpp_name_scope _%_list_scope
Arguments Nglobal c
Arguments Ndependent t%_cpp_type_scope
Arguments Nscoped n%_cpp_name_scope c
Arguments Nunsupported _%_pstring_scope
Arguments Atype _%_cpp_type_scope
Arguments Avalue _%_CPP_expr_scope
Arguments Apack _%_list_scope
Arguments Atemplate _%_cpp_name_scope
Arguments Aunsupported _%_pstring_scope
Arguments Tparam _%_pstring_scope
Arguments Tresult_param _%_pstring_scope
Arguments Tresult_global on%_cpp_name_scope
Arguments Tresult_unop _ _%_cpp_type_scope
Arguments Tresult_binop _ (_ _)%_cpp_type_scope
Arguments Tresult_call on%_cpp_name_scope _%_list_scope
Arguments Tresult_member_call on%_cpp_name_scope _%_cpp_type_scope _%_list_scope
Arguments Tresult_parenlist _%_cpp_type_scope _%_list_scope
Arguments Tresult_member _%_cpp_type_scope _%_cpp_name_scope
Arguments Tptr t%_cpp_type_scope
Arguments Tref t%_cpp_type_scope
Arguments Trv_ref t%_cpp_type_scope
Arguments Tnum sz sgn
Arguments Tarray t%_cpp_type_scope n%_N_scope
Arguments Tincomplete_array t%_cpp_type_scope
Arguments Tvariable_array t%_cpp_type_scope e%_CPP_expr_scope
Arguments Tnamed gn%_cpp_name_scope
Arguments Tenum gn%_cpp_name_scope
Arguments Tfunction t
Arguments Tmember_pointer (gn t)%_cpp_type_scope
Arguments Tqualified (q t)%_cpp_type_scope
Arguments Tarch osz name%_pstring_scope
Arguments Tdecltype _%_CPP_expr_scope
Arguments Texprtype _%_CPP_expr_scope
Arguments Tunsupported _%_pstring_scope
Arguments Eparam _%_pstring_scope
Arguments Eunresolved_global _%_cpp_name_scope
Arguments Eunresolved_unop _ e%_CPP_expr_scope
Arguments Eunresolved_binop _ (l r)%_CPP_expr_scope
Arguments Eunresolved_call on%_cpp_name_scope _%_list_scope
Arguments Eunresolved_member_call on%_cpp_name_scope _%_CPP_expr_scope _%_list_scope
Arguments Eunresolved_parenlist _ _%_list_scope
Arguments Eunresolved_member _%_CPP_expr_scope _%_cpp_name_scope
Arguments Evar _%_pstring_scope _%_cpp_type_scope
Arguments Eenum_const gn%_cpp_name_scope _%_pstring_scope
Arguments Eglobal on%_cpp_name_scope _%_cpp_type_scope
Arguments Eglobal_member gn%_cpp_name_scope ty%_cpp_type_scope
Arguments Echar c%_N_scope t%_cpp_type_scope
Arguments Estring s t%_cpp_type_scope
Arguments Eint n%_Z_scope t%_cpp_type_scope
Arguments Ebool b%_bool_scope
Arguments Eunop (op e)%_CPP_expr_scope t%_cpp_type_scope
Arguments Ebinop (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Ederef e%_CPP_expr_scope t%_cpp_type_scope
Arguments Eaddrof e%_CPP_expr_scope
Arguments Eassign (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eassign_op (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Epreinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epostinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epredec e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epostdec e%_CPP_expr_scope t%_cpp_type_scope
Arguments Eseqand (e1 e2)%_CPP_expr_scope
Arguments Eseqor (e1 e2)%_CPP_expr_scope
Arguments Ecomma (e1 e2)%_CPP_expr_scope
Arguments Ecall f%_CPP_expr_scope es%_list_scope
Arguments Eexplicit_cast c _%_cpp_type_scope e%_CPP_expr_scope
Arguments Ecast c e%_CPP_expr_scope
Arguments Emember arrow%_bool_scope obj%_CPP_expr_scope f mut%_bool_scope t%_cpp_type_scope
Arguments Emember_ignore arrow%_bool_scope (obj res)%_CPP_expr_scope
Arguments Emember_call arrow%_bool_scope method obj%_CPP_expr_scope args%_list_scope
Arguments Eoperator_call _ _ _%_list_scope
Arguments Esubscript (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Esizeof _ t%_cpp_type_scope
Arguments Ealignof _ t%_cpp_type_scope
Arguments Eoffsetof gn%_cpp_type_scope _%_pstring_scope t%_cpp_type_scope
Arguments Econstructor on%_cpp_name_scope args%_list_scope t%_cpp_type_scope
Arguments Elambda _%_cpp_name_scope captures%_list_scope
Arguments Eimplicit e%_CPP_expr_scope
Arguments Eimplicit_init t%_cpp_type_scope
Arguments Eif (e1 e2 e3)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eif2 n%_N_scope (common cond thn els)%_CPP_expr_scope _%_cpp_type_scope
Arguments Ethis t%_cpp_type_scope
Arguments Einitlist args%_list_scope default t%_cpp_type_scope
Arguments Einitlist_union _ _ t%_cpp_type_scope
Arguments Enew new_fn new_args%_list_scope pass_align alloc_ty%_cpp_type_scope array_size init
Arguments Edelete is_array%_bool_scope del_fn%_cpp_name_scope arg%_CPP_expr_scope deleted_type%_cpp_type_scope
Arguments Eandclean e%_CPP_expr_scope
Arguments Ematerialize_temp e%_CPP_expr_scope vc
Arguments Eatomic op%_pstring_scope args%_list_scope t%_cpp_type_scope
Arguments Estmt _%_CPP_stmt_scope _%_cpp_type_scope
Arguments Eva_arg e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epseudo_destructor is_arrow%_bool_scope t%_cpp_type_scope e%_CPP_expr_scope
Arguments Earrayloop_init oname%_N_scope src%_CPP_expr_scope (level length)%_N_scope init%_CPP_expr_scope t%_cpp_type_scope
Arguments Earrayloop_index level%_N_scope t%_cpp_type_scope
Arguments Eopaque_ref name%_N_scope t%_cpp_type_scope
Arguments Eunsupported s%_pstring_scope t%_cpp_type_scope
Arguments Sseq _%_list_scope
Arguments Sdecl _%_list_scope
Arguments Sif _ _%_CPP_expr_scope (_ _)%_CPP_stmt_scope
Arguments Sif_consteval (_ _)%_CPP_stmt_scope
Arguments Swhile _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments Sfor _ _ _ _%_CPP_stmt_scope
Arguments Sdo _%_CPP_stmt_scope _%_CPP_expr_scope
Arguments Sswitch _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments Sexpr _%_CPP_expr_scope
Arguments Sattr _%_list_scope _%_CPP_stmt_scope
Arguments Sasm _%_pstring_scope volatile%_bool_scope (inputs outputs clobbers)%_list_scope
Arguments Slabeled _%_pstring_scope _%_CPP_stmt_scope
Arguments Sgoto _%_pstring_scope
Arguments Sunsupported _%_pstring_scope
Arguments Dvar name%_pstring_scope _%_cpp_type_scope init
Arguments Ddecompose _%_CPP_expr_scope anon_var%_pstring_scope _%_list_scope
Arguments Dinit thread_safe%_bool_scope name%_cpp_name_scope _%_cpp_type_scope init
Arguments Bvar name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments Bbind name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments Cdependent _%_cpp_type_scope
Arguments Cbitcast _%_cpp_type_scope
Arguments Clvaluebitcast _%_cpp_type_scope
Arguments Cl2r_bitcast _%_cpp_type_scope
Arguments Cnoop _%_cpp_type_scope
Arguments Cint2ptr _%_cpp_type_scope
Arguments Cptr2int _%_cpp_type_scope
Arguments Cintegral _%_cpp_type_scope
Arguments Cfloat2int _%_cpp_type_scope
Arguments Cint2float _%_cpp_type_scope
Arguments Cfloat _%_cpp_type_scope
Arguments Cnull2ptr _%_cpp_type_scope
Arguments Cnull2memberptr _%_cpp_type_scope
Arguments Cbuiltin2fun _%_cpp_type_scope
Arguments Cctor _%_cpp_type_scope
Arguments Cdynamic to%_cpp_type_scope
Arguments Cderived2base path%_list_scope END%_cpp_type_scope
Arguments Cbase2derived path%_list_scope END%_cpp_type_scope
Arguments Cunsupported _%_bs_scope _%_cpp_type_scope

Assistant: We can give a standalone printer just for `Stmt`, leaving all the nested printers for names/types/expressions/etc admitted.  In particular we:

- Admit a small utility `intercalate` to join a list of strings.
- Admit printers for `Expr`, `VarDecl`, and `SwitchBranch`.
- Then write a `Fixpoint pprint_stmt : Stmt → string` covering every `Stmt` constructor.

This skeleton can be filled in later by implementing the admitted helpers.

```gallina
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* helper to join a list of strings with a separator *)
Definition intercalate (sep : string) (l : list string) : string. Admitted.

(* admitted printers for nested syntactic categories *)
Definition pprint_expr (e : Expr) : string. Admitted.
Definition pprint_vardecl (d : VarDecl) : string. Admitted.
Definition pprint_switchbranch (br : SwitchBranch) : string. Admitted.

Fixpoint pprint_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      "(" ++ intercalate ";" (map pprint_stmt ss) ++ ")"
  | Sdecl ds =>
      "decl " ++ intercalate "," (map pprint_vardecl ds)
  | Sif dv e thn els =>
      "if " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " then " ++ pprint_stmt thn ++
      " else " ++ pprint_stmt els
  | Sif_consteval thn els =>
      "if_consteval " ++ pprint_stmt thn ++ " else_consteval " ++ pprint_stmt els
  | Swhile dv e body =>
      "while " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " do " ++ pprint_stmt body
  | Sfor init cond step body =>
      "for (" ++
      match init with Some st => pprint_stmt st | None => "" end ++ "; " ++
      match cond with Some e => pprint_expr e | None => "" end ++ "; " ++
      match step with Some e => pprint_expr e | None => "" end ++
      ") " ++ pprint_stmt body
  | Sdo body e =>
      "do " ++ pprint_stmt body ++ " while " ++ pprint_expr e
  | Sswitch dv e body =>
      "switch " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++ " { " ++ pprint_stmt body ++ " }"
  | Scase br =>
      "case " ++ pprint_switchbranch br
  | Sdefault => "default"
  | Sbreak => "break"
  | Scontinue => "continue"
  | Sreturn eo =>
      "return" ++
      match eo with Some e => " " ++ pprint_expr e | None => "" end
  | Sexpr e =>
      pprint_expr e
  | Sattr attrs st =>
      "attr[" ++ intercalate "," attrs ++ "] " ++ pprint_stmt st
  | Sasm s vol inputs outputs clobs =>
      "asm(" ++ s ++
      if vol then ",volatile" else "" ++
      ", in{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) inputs) ++
      "}, out{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) outputs) ++
      "}, clob{" ++ intercalate "," clobs ++ "})"
  | Slabeled lbl st =>
      lbl ++ ": " ++ pprint_stmt st
  | Sgoto lbl =>
      "goto " ++ lbl
  | Sunsupported s =>
      "unsupported(" ++ s ++ ")"
  end.
```
User: Toplevel input, characters 1574-1579:
>       "attr[" ++ intercalate "," attrs ++ "] " ++ pprint_stmt st
>                                  ^^^^^
Error:
In environment
pprint_stmt : Stmt → string
s : Stmt
attrs : list ident
st : Stmt
The term "attrs" has type "list ident" while it is expected to have type "list string".

Assistant: We need to convert `ident` (and similarly any other non-`string` names) to `string` before intercalating.  We admit a helper

```coq
Definition ident_to_string (i: ident) : string. Admitted.
```

and then map it over `attrs` (and over labels in `Slabeled`, `Sgoto`, etc.).  Here is the corrected pretty-printer skeleton:

```gallina
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* helper to join a list of strings with a separator *)
Definition intercalate (sep : string) (l : list string) : string. Admitted.

(* admit conversion of identifiers to strings *)
Definition ident_to_string (i : ident) : string. Admitted.

(* admitted printers for nested syntactic categories *)
Definition pprint_expr (e : Expr) : string. Admitted.
Definition pprint_vardecl (d : VarDecl) : string. Admitted.
Definition pprint_switchbranch (br : SwitchBranch) : string. Admitted.

Fixpoint pprint_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      "(" ++ intercalate ";" (map pprint_stmt ss) ++ ")"
  | Sdecl ds =>
      "decl " ++ intercalate "," (map pprint_vardecl ds)
  | Sif dv e thn els =>
      "if " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " then " ++ pprint_stmt thn ++
      " else " ++ pprint_stmt els
  | Sif_consteval thn els =>
      "if_consteval " ++ pprint_stmt thn ++ " else_consteval " ++ pprint_stmt els
  | Swhile dv e body =>
      "while " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++
      " do " ++ pprint_stmt body
  | Sfor init cond step body =>
      "for (" ++
      match init with Some st => pprint_stmt st | None => "" end ++ "; " ++
      match cond with Some e => pprint_expr e | None => "" end ++ "; " ++
      match step with Some e => pprint_expr e | None => "" end ++
      ") " ++ pprint_stmt body
  | Sdo body e =>
      "do " ++ pprint_stmt body ++ " while " ++ pprint_expr e
  | Sswitch dv e body =>
      "switch " ++
      match dv with Some d => pprint_vardecl d ++ "; " | None => "" end ++
      pprint_expr e ++ " { " ++ pprint_stmt body ++ " }"
  | Scase br =>
      "case " ++ pprint_switchbranch br
  | Sdefault => "default"
  | Sbreak => "break"
  | Scontinue => "continue"
  | Sreturn eo =>
      "return" ++
      match eo with Some e => " " ++ pprint_expr e | None => "" end
  | Sexpr e =>
      pprint_expr e
  | Sattr attrs st =>
      "attr[" ++ intercalate "," (map ident_to_string attrs) ++ "] " ++ pprint_stmt st
  | Sasm s vol inputs outputs clobs =>
      "asm(" ++ s ++
      if vol then ",volatile" else "" ++
      ", in{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) inputs) ++
      "}, out{" ++
        intercalate "," (map (fun '(i,e) => i ++ ":" ++ pprint_expr e) outputs) ++
      "}, clob{" ++ intercalate "," (map ident_to_string clobs) ++ "})"
  | Slabeled lbl st =>
      ident_to_string lbl ++ ": " ++ pprint_stmt st
  | Sgoto lbl =>
      "goto " ++ ident_to_string lbl
  | Sunsupported s =>
      "unsupported(" ++ s ++ ")"
  end.
```
*)
