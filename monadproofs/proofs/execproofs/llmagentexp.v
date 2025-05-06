Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Open Scope pstring_scope.



(*
Write a Coq function to pretty print bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be `bluerock.lang.cpp.syntax.stmt.Stmt -> string`.
In the current context, `string` refers to `PrimString.string`, which is unusual in non-recent Coq developments. 
PrimString.string is a new type in Coq's core standard library. It axiomatizes primitive strings.
The scope delimiting key for  PrimString.string is pstring.
So, `(a ++ b)%pstring` appends `a:PrimString.string` and `b:PrimString.string`.
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.
*)

Require Import Corelib.Strings.PrimString.
Open Scope string.

(* stubs for sub-printers *)
Definition pp_expr (e : Expr) : string. Admitted.  (* TOFIXLATER *)
Definition pp_vardecl (d : VarDecl) : string. Admitted.  (* TOFIXLATER *)

(* a small list‐printer combinator *)
Fixpoint pp_list {A} (ppA : A → string) (sep : string) (l : list A) : string :=
  match l with
  | [] => ""
  | [x] => ppA x
  | x :: xs => cat (ppA x) (cat sep (pp_list ppA sep xs))
  end.

(* mutually recursive printing of Stmt and list of Stmt *)
Fixpoint pp_stmt_list (l : list Stmt) : string :=
  match l with
  | [] => ""
  | [s] => pp_stmt s
  | s :: ss => cat (pp_stmt s) (cat "; " (pp_stmt_list ss))
  end

with pp_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      cat "{ " (cat (pp_stmt_list ss) " }")
  | Sdecl ds =>
      cat (pp_list pp_vardecl "; " ds) ";"
  | Sif vd_opt cond thn els =>
      let vd_s := match vd_opt with
                  | None => ""
                  | Some vd => cat (pp_vardecl vd) " "
                  end in
      cat "if (" (cat (pp_expr cond) (cat ") " (cat vd_s (cat (pp_stmt thn) (cat " else " (pp_stmt els))))))
  | Sif_consteval thn els =>
      cat "if consteval " (cat (pp_stmt thn) (cat " else " (pp_stmt els)))
  | Swhile vd_opt cond body =>
      let vd_s := match vd_opt with
                  | None => ""
                  | Some vd => cat (pp_vardecl vd) " "
                  end in
      cat "while (" (cat (pp_expr cond) (cat ") " (cat vd_s (pp_stmt body))))
  | Sfor init cond incr body =>
      let i1 := match init with None => "" | Some st => pp_stmt st end in
      let c2 := match cond with None => "" | Some e => pp_expr e end in
      let i3 := match incr with None => "" | Some e => pp_expr e end in
      cat "for (" (cat i1 (cat "; " (cat c2 (cat "; " (cat i3 (cat ") " (pp_stmt body))))))
  | Sdo body cond =>
      cat "do " (cat (pp_stmt body) (cat " while (" (cat (pp_expr cond) ");")))
  | Sswitch vd_opt e br =>
      let vd_s := match vd_opt with None => "" | Some vd => cat (pp_vardecl vd) " " end in
      cat "switch (" (cat (pp_expr e) (cat ") " (cat vd_s (pp_stmt br))))
  | Scase sb =>
      cat "case " (cat (pp_expr sb.1) (cat ": " (pp_stmt sb.2)))
  | Sdefault => "default:;"
  | Sbreak => "break;"
  | Scontinue => "continue;"
  | Sreturn eo =>
      cat "return" (match eo with None => ";" | Some e => cat " " (cat (pp_expr e) ";") end)
  | Sexpr e => cat (pp_expr e) ";"
  | Sattr attrs st =>
      cat "[[" (cat (pp_list (fun i => i) ", ") (cat "]] " (pp_stmt st)))
  | Sasm txt vol inouts outouts clobs =>
      let in_s  := pp_list (fun io => cat io.1 (cat "(" (cat (pp_expr io.2) ")"))) ", " inouts in
      let out_s := pp_list (fun io => cat io.1 (cat "(" (cat (pp_expr io.2) ")"))) ", " outouts in
      let clob_s := pp_list (fun i => i) ", " clobs in
      cat "asm " (cat txt (cat " " (cat (if vol then "volatile " else "")
        (cat "(" (cat in_s (cat ") (" (cat out_s (cat ") {" (cat clob_s "};")))))))))
  | Slabeled lbl st => cat lbl (cat ": " (pp_stmt st))
  | Sgoto lbl => cat "goto " (cat lbl ";")
  | Sunsupported txt => txt
  end.





