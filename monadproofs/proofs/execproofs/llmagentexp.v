Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* a single double‐quote as a Coq string *)
Definition doubleQuote : string := """".

(* high‐level helpers: refine these later *)

(** convert a “PrimString.string” (literal text) to a Coq [string] *)
Definition pp_pliteral (s: PrimString.string) : string :=
  "<lit>".          (* TODO: FILL IN LATER *)

(** convert an identifier (local or global) to [string] *)
Definition pp_ident (id: bluerock.lang.cpp.syntax.preliminary.ident) : string :=
  "<id>".           (* TODO: FILL IN LATER *)

(** convert a whole expression to [string] *)
Definition pp_expr (e: bluerock.lang.cpp.syntax.core.Expr) : string :=
  "<expr>".         (* TODO: FILL IN LATER *)

(** convert a single variable declaration to [string] *)
Definition pp_vardecl (d: bluerock.lang.cpp.syntax.core.VarDecl) : string :=
  "<vardecl>".      (* TODO: FILL IN LATER *)

(** convert one switch‐case branch to [string] *)
Definition pp_switch_branch (b: bluerock.lang.cpp.syntax.preliminary.SwitchBranch) : string :=
  "<branch>".       (* TODO: FILL IN LATER *)

(** The main statement pretty‐printer *)
Fixpoint pp_stmt (s: bluerock.lang.cpp.syntax.core.Stmt) : string :=
  match s with
  | bluerock.lang.cpp.syntax.core.Sseq ss =>
      "(" ++ String.concat "; " (map pp_stmt ss) ++ ")"
  | bluerock.lang.cpp.syntax.core.Sdecl ds =>
      "decl " ++ String.concat ", " (map pp_vardecl ds)
  | bluerock.lang.cpp.syntax.core.Sif None cond thn els =>
      "if(" ++ pp_expr cond ++ ") " ++ pp_stmt thn ++ " else " ++ pp_stmt els
  | bluerock.lang.cpp.syntax.core.Sif (Some vd) cond thn els =>
      "if(" ++ pp_vardecl vd ++ "; " ++ pp_expr cond ++ ") "
      ++ pp_stmt thn ++ " else " ++ pp_stmt els
  | bluerock.lang.cpp.syntax.core.Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els
  | bluerock.lang.cpp.syntax.core.Swhile None cond body =>
      "while(" ++ pp_expr cond ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Swhile (Some vd) cond body =>
      "while(" ++ pp_vardecl vd ++ "; " ++ pp_expr cond ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e => pp_expr e  | None => "" end in
      let incr_s := match incr with Some e => pp_expr e  | None => "" end in
      "for(" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sdo body cond =>
      "do " ++ pp_stmt body ++ " while(" ++ pp_expr cond ++ ")"
  | bluerock.lang.cpp.syntax.core.Sswitch None e body =>
      "switch(" ++ pp_expr e ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sswitch (Some vd) e body =>
      "switch(" ++ pp_vardecl vd ++ "; " ++ pp_expr e ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Scase br =>
      "case " ++ pp_switch_branch br
  | bluerock.lang.cpp.syntax.core.Sdefault =>
      "default"
  | bluerock.lang.cpp.syntax.core.Sbreak =>
      "break"
  | bluerock.lang.cpp.syntax.core.Scontinue =>
      "continue"
  | bluerock.lang.cpp.syntax.core.Sreturn None =>
      "return"
  | bluerock.lang.cpp.syntax.core.Sreturn (Some e) =>
      "return " ++ pp_expr e
  | bluerock.lang.cpp.syntax.core.Sexpr e =>
      pp_expr e
  | bluerock.lang.cpp.syntax.core.Sattr attrs s' =>
      "attr[" ++ String.concat ", " (map pp_ident attrs) ++ "] " ++ pp_stmt s'
  | bluerock.lang.cpp.syntax.core.Sasm str vol inps outs clobs =>
      "asm(" ++
        doubleQuote ++ pp_pliteral str ++ doubleQuote ++
        (if vol then " volatile" else "") ++
      " : " ++ String.concat ", "
           (map (fun io => pp_ident (fst io) ++ " : " ++ pp_expr (snd io)) inps) ++
      " : " ++ String.concat ", "
           (map (fun io => pp_ident (fst io) ++ " : " ++ pp_expr (snd io)) outs) ++
      " : " ++ String.concat ", " (map pp_ident clobs) ++ ")"
  | bluerock.lang.cpp.syntax.core.Slabeled lbl s' =>
      pp_ident lbl ++ ": " ++ pp_stmt s'
  | bluerock.lang.cpp.syntax.core.Sgoto lbl =>
      "goto " ++ pp_ident lbl
  | bluerock.lang.cpp.syntax.core.Sunsupported msg =>
      "unsupported_stmt(" ++ doubleQuote ++ pp_pliteral msg ++ doubleQuote ++ ")"
  end.


