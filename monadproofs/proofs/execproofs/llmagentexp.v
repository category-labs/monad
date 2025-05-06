Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Open Scope pstring_scope.

Locate string.

(*
Write a Coq function to pretty print bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
bluerock.lang.cpp.syntax.stmt.Stmt is defined mutually Inductively with many other types like Expr.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be bluerock.lang.cpp.syntax.stRequire Import List.
*)

Require Import Coq.Lists.List.
Require Import Corelib.Strings.PrimString.
Import ListNotations.
Open Scope pstring_scope.

(* ------------------------------------------------------------------ *)
(* STUBS FOR ALL OF THE OTHER PRINTERS.  TOFIXLATER                   *)
(* ------------------------------------------------------------------ *)
Axiom pp_name         : name       -> string.  (* TOFIXLATER *)
Axiom pp_temp_arg     : temp_arg   -> string.  (* TOFIXLATER *)
Axiom pp_type         : type       -> string.  (* TOFIXLATER *)
Axiom pp_expr         : Expr       -> string.  (* TOFIXLATER *)
Axiom pp_vardecl      : VarDecl    -> string.  (* TOFIXLATER *)
Axiom pp_bindingdecl  : BindingDecl-> string.  (* TOFIXLATER *)
Axiom pp_cast         : Cast       -> string.  (* TOFIXLATER *)

(* ------------------------------------------------------------------ *)
(* A little list‐printer                                              *)
(* ------------------------------------------------------------------ *)
Definition pp_list {A} (pp : A -> string) (sep : string) (l : list A) : string :=
  match l with
  | []    => ""
  | x::xs => fold_left
               (fun acc y => cat (cat acc sep) (pp y))
               xs
               (pp x)
  end.

(* ------------------------------------------------------------------ *)
(* THE STATEMENT PRINTER                                              *)
(* ------------------------------------------------------------------ *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq ss =>
      let inner := pp_list pp_stmt "; " ss in
      printer.prefix "{ " (printer.postfix " }" inner)

  | Sdecl ds =>
      cat "decl " (pp_list pp_vardecl ", " ds)

  | Sif _vd e thn els =>
      let c := pp_expr e in
      let t := pp_stmt thn in
      let e := pp_stmt els in
      cat (cat "if(" c) (cat ") " (cat t (cat " else " e)))

  | Swhile _vd e body =>
      cat (cat "while(" (pp_expr e)) (cat ") " (pp_stmt body))

  | Sfor init cond post body =>
      (* build the "for(init; cond; post)" header in steps *)
      let i := match init with Some st => pp_stmt st | None => "" end in
      let c := match cond with Some e => pp_expr e | None => "" end in
      let p := match post with Some e => pp_expr e | None => "" end in
      let header1 := cat "for(" (cat i "; ") in
      let header2 := cat header1 (cat c "; ") in
      let header3 := cat header2 p in
      cat header3 (cat ") " (pp_stmt body))

  | Sreturn oe =>
      cat "return" (match oe with None => "" | Some e => cat " " (pp_expr e) end)

  | Sexpr e =>
      pp_expr e

  | Sunsupported s' =>
      cat "/* unsupported Stmt: " (cat s' " */")

  | _ =>
      (* catch‐all for cases not yet implemented *)
      printer.prefix "/* unimpl stmt: " (printer.postfix " */" "")

  end.

