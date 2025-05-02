(*
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition string := String.string.

(* Admitted helpers: you should implement these. *)
Definition pp_expr (e: Expr) : string. Admitted.
Definition pp_type (t: type) : string. Admitted.
Definition pp_list {A} (pp: A → string) (sep: string) (l: list A) : string. Admitted.

(* Pretty‐print a single VarDecl. *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar name ty init =>
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => String.append " = " (pp_expr e)
                    | None   => ""
                    end in
      String.append (String.append Require Import Coq.Strings.StringRequire Import Coq.Strings.StringRequire Import Coq.Strings.StringRequire Import Coq.Strings.StringRequire Import Coq.Strings.StringRequire Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition string := String.string.

(* Admitted helpers *)
Definition pp_expr      (e: Expr)           : string. Admitted.
Definition pp_type      (t: type)           : string. Admitted.
Definition pp_list {A} (pp: A -> string) (sep: string) (l: list A) : string. Admitted.
Definition pp_localname (n: localname)      : string. Admitted.
Definition pp_name      (n: name)           : string. Admitted.

(* Pretty-print a VarDecl *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar lname ty init =>
      let nm_s   := pp_localname lname in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s

  | Ddecompose e _ _ =>
      "decompose " ++ pp_expr e

  | Dinit _ nm ty init =>
      let nm_s   := pp_name nm in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s
  end.

(* Pretty-print a Stmt *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq stmts =>
      "{ " ++ pp_list pp_stmt "; " stmts ++ " }"

  | Sdecl ds =>
      "{ " ++ pp_list pp_var_decl "; " ds ++ " }"

  | Sif opt_d cond thn els =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "if (" ++ pp_expr cond ++ ") "
             ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Swhile opt_d cond body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "while (" ++ pp_expr cond ++ ") " ++ pp_stmt body

  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e  | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e  | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
             ++ pp_stmt body

  | Sdo body cond =>
      "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ");"

  | Sswitch opt_d e body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      "switch (" ++ pp_expr e ++ ") " ++ decl_s ++ pp_stmt body

  | Scase _          => "<case>"
  | Sdefault        => "default;"
  | Sbreak          => "break;"
  | Scontinue       => "continue;"

  | Sreturn opt_e   =>
      let e_s := match opt_e with
                 | Some e => " " ++ pp_expr e
                 | None   => ""
                 end in
      "return" ++ e_s ++ ";"

  | Sexpr e         => pp_expr e ++ ";"
  | Sattr _ _       => "<attr>"
  | Sasm str _ _ _ _=> "asm \"" ++ str ++ "\";"
  | Slabeled lab st => lab ++ ": " ++ pp_stmt st
  | Sgoto lab       => "goto " ++ lab ++ ";"
  | Sunsupported s  => "/* unsupported: " ++ s ++ " */"
  end.

.
Require Import Coq.Lists.List.
Open Scope string_scope.

Definition string := String.string.

(* === Admitted helpers (implement later) === *)
Definition pp_expr      (e: Expr)           : string. Admitted.
Definition pp_type      (t: type)           : string. Admitted.
Definition pp_list {A} (pp: A -> string) (sep: string) (l: list A) : string. Admitted.
Definition pp_localname (n: localname)      : string. Admitted.
Definition pp_name      (n: name)           : string. Admitted.

(* === Pretty‐print a VarDecl === *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar lname ty init =>
      let nm_s   := pp_localname lname in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s

  | Ddecompose e _id _bs =>
      "decompose " ++ pp_expr e

  | Dinit _ nm ty init =>
      let nm_s   := pp_name nm in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s
  end.

(* === Pretty‐print a Stmt === *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq stmts =>
      "{ " ++ pp_list pp_stmt "; " stmts ++ " }"

  | Sdecl ds =>
      "{ " ++ pp_list pp_var_decl "; " ds ++ " }"

  | Sif opt_d cond thn els =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "if (" ++ pp_expr cond ++ ") "
             ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Swhile opt_d cond body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "while (" ++ pp_expr cond ++ ") " ++ pp_stmt body

  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e  | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e  | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
             ++ pp_stmt body

  | Sdo body cond =>
      "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ");"

  | Sswitch opt_d e body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      "switch (" ++ pp_expr e ++ ") " ++ decl_s ++ pp_stmt body

  | Scase _       => "<case>"
  | Sdefault      => "default;"
  | Sbreak        => "break;"
  | Scontinue     => "continue;"

  | Sreturn opt_e =>
      let e_s := match opt_e with
                 | Some e => " " ++ pp_expr e
                 | None   => ""
                 end in
      "return" ++ e_s ++ ";"

  | Sexpr e       => pp_expr e ++ ";"
  | Sattr _ _     => "<attr>"
  | Sasm str _ _ _ _ => "asm \"" ++ str ++ "\";"
  | Slabeled lab st  => lab ++ ": " ++ pp_stmt st
  | Sgoto lab        => "goto " ++ lab ++ ";"
  | Sunsupported s   => "/* unsupported: " ++ s ++ " */"
  end.

.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition string := String.string.

(* Admitted helpers to fill in later *)
Definition pp_expr      (e: Expr)           : string. Admitted.
Definition pp_type      (t: type)           : string. Admitted.
Definition pp_list {A} (pp: A -> string) (sep: string) (l: list A) : string. Admitted.
Definition pp_localname (n: localname)      : string. Admitted.
Definition pp_name      (n: name)           : string. Admitted.

(* Pretty‐print a VarDecl *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar lname ty init =>
      let nm_s   := pp_localname lname in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s

  | Ddecompose e _id _bs =>
      "decompose " ++ pp_expr e

  | Dinit _ nm ty init =>
      let nm_s   := pp_name nm in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s
  end.

(* Pretty‐print a Stmt *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq stmts =>
      "{ " ++ pp_list pp_stmt "; " stmts ++ " }"
  | Sdecl ds =>
      "{ " ++ pp_list pp_var_decl "; " ds ++ " }"
  | Sif opt_d cond thn els =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "if (" ++ pp_expr cond ++ ") "
             ++ pp_stmt thn ++ " else " ++ pp_stmt els
  | Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els
  | Swhile opt_d cond body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "while (" ++ pp_expr cond ++ ") " ++ pp_stmt body
  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e  | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e  | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
             ++ pp_stmt body
  | Sdo body cond =>
      "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ");"
  | Sswitch opt_d e body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      "switch (" ++ pp_expr e ++ ") " ++ decl_s ++ pp_stmt body
  | Scase _          => "<case>"
  | Sdefault        => "default;"
  | Sbreak          => "break;"
  | Scontinue       => "continue;"
  | Sreturn opt_e   =>
      let e_s := match opt_e with
                 | Some e => " " ++ pp_expr e
                 | None   => ""
                 end in
      "return" ++ e_s ++ ";"
  | Sexpr e         => pp_expr e ++ ";"
  | Sattr _ _       => "<attr>"
  | Sasm str _ _ _ _=> "asm \"" ++ str ++ "\";"
  | Slabeled lab st => lab ++ ": " ++ pp_stmt st
  | Sgoto lab       => "goto " ++ lab ++ ";"
  | Sunsupported s  => "/* unsupported: " ++ s ++ " */"
  end.

.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition string := String.string.

(* === Admitted helpers to implement later === *)
Definition pp_expr      (e: Expr)           : string. Admitted.
Definition pp_type      (t: type)           : string. Admitted.
Definition pp_list {A} (pp: A -> string) (sep: string) (l: list A) : string. Admitted.
Definition pp_localname (n: localname)      : string. Admitted.
Definition pp_name      (n: name)           : string. Admitted.

(* === Pretty‐print a VarDecl === *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar lname ty init =>
      let nm_s   := pp_localname lname in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s

  | Ddecompose e _id _bs =>
      "decompose " ++ pp_expr e

  | Dinit _ nm ty init =>
      let nm_s   := pp_name nm in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s
  end.

(* === Pretty‐print a Stmt === *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq stmts =>
      "{ " ++ pp_list pp_stmt "; " stmts ++ " }"

  | Sdecl ds =>
      "{ " ++ pp_list pp_var_decl "; " ds ++ " }"

  | Sif opt_d cond thn els =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "if (" ++ pp_expr cond ++ ") "
             ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Swhile opt_d cond body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "while (" ++ pp_expr cond ++ ") " ++ pp_stmt body

  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e  | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e  | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
             ++ pp_stmt body

  | Sdo body cond =>
      "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ");"

  | Sswitch opt_d e body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      "switch (" ++ pp_expr e ++ ") " ++ decl_s ++ pp_stmt body

  | Scase _          => "<case>"
  | Sdefault        => "default;"
  | Sbreak          => "break;"
  | Scontinue       => "continue;"

  | Sreturn opt_e   =>
      let e_s := match opt_e with
                 | Some e => " " ++ pp_expr e
                 | None   => ""
                 end in
      "return" ++ e_s ++ ";"

  | Sexpr e         => pp_expr e ++ ";"
  | Sattr _ _       => "<attr>"
  | Sasm str _ _ _ _=> "asm \"" ++ str ++ "\";"
  | Slabeled lab st => lab ++ ": " ++ pp_stmt st
  | Sgoto lab       => "goto " ++ lab ++ ";"
  | Sunsupported s  => "/* unsupported: " ++ s ++ " */"
  end.

.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition string := String.string.

(* Admitted helpers: *)
Definition pp_expr      (e: Expr)           : string. Admitted.
Definition pp_type      (t: type)           : string. Admitted.
Definition pp_list {A} (pp: A -> string) (sep: string) (l: list A) : string. Admitted.
Definition pp_localname (n: localname)      : string. Admitted.
Definition pp_name      (n: name)           : string. Admitted.

(* Pretty‐print a VarDecl. *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar lname ty init =>
      let nm_s   := pp_localname lname in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s

  | Ddecompose e _id _bs =>
      "decompose " ++ pp_expr e

  | Dinit _ nm ty init =>
      let nm_s   := pp_name nm in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s
  end.

(* Main pretty‐printer for Stmt. *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq stmts =>
      "{ " ++ pp_list pp_stmt "; " stmts ++ " }"

  | Sdecl ds =>
      "{ " ++ pp_list pp_var_decl "; " ds ++ " }"

  | Sif opt_d cond thn els =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "if (" ++ pp_expr cond ++ ") "
             ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Swhile opt_d cond body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      decl_s ++ "while (" ++ pp_expr cond ++ ") " ++ pp_stmt body

  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e  | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e  | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
             ++ pp_stmt body

  | Sdo body cond =>
      "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ");"

  | Sswitch opt_d e body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      "switch (" ++ pp_expr e ++ ") " ++ decl_s ++ pp_stmt body

  | Scase _          => "<case>"
  | Sdefault        => "default;"
  | Sbreak          => "break;"
  | Scontinue       => "continue;"

  | Sreturn opt_e   =>
      let e_s := match opt_e with
                 | Some e => " " ++ pp_expr e
                 | None   => ""
                 end in
      "return" ++ e_s ++ ";"

  | Sexpr e         => pp_expr e ++ ";"
  | Sattr _ _       => "<attr>"
  | Sasm str _ _ _ _=> "asm \"" ++ str ++ "\";"
  | Slabeled lab st => lab ++ ": " ++ pp_stmt st
  | Sgoto lab       => "goto " ++ lab ++ ";"
  | Sunsupported s  => "/* unsupported: " ++ s ++ " */"
  end.

.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

Definition string := String.string.

(* Admitted helpers: *)
Definition pp_expr (e: Expr) : string. Admitted.
Definition pp_type (t: type) : string. Admitted.
Definition pp_list {A} (pp: A → string) (sep: string) (l: list A) : string. Admitted.

(* Convert a local variable name and a global/qualified name to string *)
Definition pp_localname (n: localname) : string. Admitted.
Definition pp_name      (n: name)      : string. Admitted.

(* Pretty‐print a single VarDecl. *)
Fixpoint pp_var_decl (d: VarDecl) : string :=
  match d with
  | Dvar lname ty init =>
      let nm_s   := pp_localname lname in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s

  | Ddecompose e id bs =>
      (* stub: ignore id, bs *)
      "decompose " ++ pp_expr e

  | Dinit _ nm ty init =>
      let nm_s   := pp_name nm in
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => " = " ++ pp_expr e
                    | None   => ""
                    end in
      nm_s ++ ": " ++ ty_s ++ init_s
  end.

(* The main pretty‐printer for Stmt. *)
Fixpoint pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq stmts =>
      "{ " ++ pp_list pp_stmt "; " stmts ++ " }"

  | Sdecl ds =>
      "{ " ++ pp_list pp_var_decl "; " ds ++ " }"

  | Sif opt_d cond thn els =>
      let decl_s :=
        match opt_d with
        | Some d => pp_var_decl d ++ "; "
        | None   => fun _ => ""
        end in
      let head := "if (" ++ pp_expr cond ++ ")" in
      decl_s "" ++ head ++ " " ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Sif_consteval thn els =>
      "if consteval " ++ pp_stmt thn ++ " else " ++ pp_stmt els

  | Swhile opt_d cond body =>
      let decl_s :=
        match opt_d with
        | Some d => pp_var_decl d ++ "; "
        | None   => fun _ => ""
        end in
      decl_s "" ++ "while (" ++ pp_expr cond ++ ") " ++ pp_stmt body

  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e   | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e   | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") " ++ pp_stmt body

  | Sdo body cond =>
      "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ");"

  | Sswitch opt_d e body =>
      let decl_s := match opt_d with
                    | Some d => pp_var_decl d ++ "; "
                    | None   => ""
                    end in
      "switch (" ++ pp_expr e ++ ") " ++ decl_s ++ pp_stmt body

  | Scase _          => "<case>"
  | Sdefault        => "default;"
  | Sbreak          => "break;"
  | Scontinue       => "continue;"

  | Sreturn opt_e   =>
      let e_s := match opt_e with
                 | Some e => " " ++ pp_expr e
                 | None   => ""
                 end in
      "return" ++ e_s ++ ";"

  | Sexpr e         => pp_expr e ++ ";"

  | Sattr _ _       => "<attr>"
  | Sasm str _ _ _ _ => "asm \"" ++ str ++ "\";"
  | Slabeled lab st => lab ++ ": " ++ pp_stmt st
  | Sgoto lab       => "goto " ++ lab ++ ";"
  | Sunsupported s  => "/* unsupported: " ++ s ++ " */"
  end.

name ": " ty_s) init_s
  | Ddecompose e id bs =>
      (* stub: ignore id, bs *)
      String.append "decompose " (pp_expr e)
  | Dinit _ nm ty init =>
      let ty_s   := pp_type ty in
      let init_s := match init with
                    | Some e => String.append " = " (pp_expr e)
                    | None   => ""
                    end in
      String.append (String.append nm ": " ty_s) init_s
  end.

(* The main pretty‐printer for Stmt. *)
Fixpoint pp_stmt (s: Stmt) {struct s} : string :=
  match s with
  | Sseq stmts =>
      let inner := pp_list pp_stmt "; " stmts in
      String.append "{ " (String.append inner " }")

  | Sdecl ds =>
      let body := pp_list pp_var_decl "; " ds in
      String.append "{ " (String.append body " }")

  | Sif opt_d cond thn els =>
      let decl_s :=
        match opt_d with
        | Some d => fun s0 => String.append (pp_var_decl d) "; " s0
        | None   => fun s0 => s0
        end in
      let head := String.append "if (" (String.append (pp_expr cond) ")") in
      decl_s (String.append head
                       (String.append " " 
                                      (String.append (pp_stmt thn)
                                                     (String.append " else "
                                                                    (pp_stmt els)))))

  | Sif_consteval thn els =>
      String.append "if consteval "
                    (String.append (pp_stmt thn)
                                   (String.append " else " (pp_stmt els)))

  | Swhile opt_d cond body =>
      let decl_s :=
        match opt_d with
        | Some d => fun s0 => String.append (pp_var_decl d) "; " s0
        | None   => fun s0 => s0
        end in
      let head := String.append "while (" (String.append (pp_expr cond) ")") in
      decl_s (String.append head (String.append " " (pp_stmt body)))

  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pp_stmt s' | None => "" end in
      let cond_s := match cond with Some e  => pp_expr e   | None => "" end in
      let incr_s := match incr with Some e  => pp_expr e   | None => "" end in
      String.append "for ("
                    (String.append init_s
                                   (String.append "; "
                                                  (String.append cond_s
                                                                 (String.append "; "
                                                                                (String.append incr_s
                                                                                               (String.append ") "
                                                                                                              (pp_stmt body)))))))

  | Sdo body cond =>
      String.append "do " (String.append (pp_stmt body)
                                         (String.append " while ("
                                                        (String.append (pp_expr cond) ");")))

  | Sswitch opt_d e body =>
      let decl_s :=
        match opt_d with
        | Some d => fun s0 => String.append (pp_var_decl d) "; " s0
        | None   => fun s0 => s0
        end in
      String.append "switch (" (String.append (pp_expr e)
                                             (String.append ") "
                                                            (decl_s (pp_stmt body))))

  | Scase _          => "<case>"

  | Sdefault        => "default;"

  | Sbreak          => "break;"

  | Scontinue       => "continue;"

  | Sreturn opt_e   =>
      let e_s := match opt_e with Some e => String.append " " (pp_expr e) | None => "" end in
      String.append "return" (String.append e_s ";")

  | Sexpr e         => String.append (pp_expr e) ";"

  | Sattr _ _       => "<attr>"

  | Sasm str _ _ _ _ => String.append "asm \"" (String.append str "\";")

  | Slabeled lab st => String.append lab (String.append ": " (pp_stmt st))

  | Sgoto lab       => String.append "goto " (String.append lab ";")

  | Sunsupported s  => String.append "/* unsupported: "
                                     (String.append s " */")
  end.



Locate nat.
Print Stmt.


Definition foo :=nat+nat.
   Definition bar :=nat.

```coqquery
  Print Ns.
```

```gallina
   Definition foo :=nat+nat.
   Definition bar :=nat.
```   
Definition foo :=nat+nat.
   Definition bar :=nat.




  Definition foo :=nat+nat.
   Definition bar :=nat.

Definition foo :=nat.



Require Import Coq.Strings.String.
Open Scope string_scope.

(* convert the AST’s PrimString.string into the printing String.string *)
Definition prim_to_String (s: PrimString.string) : String.string. Admitted.

(* helper admits for all subcomponents *)
Definition id_to_string (i: ident) : String.string. Admitted.
Definition pretty_name (n: name) : String.string. Admitted.
Definition pretty_temp_arg (a: temp_arg) : String.string. Admitted.
Definition pretty_type (t: type) : String.string. Admitted.
Definition pretty_expr (e: Expr) : String.string. Admitted.
Definition pretty_vardecl (d: VarDecl) : String.string. Admitted.
Definition pretty_bindingdecl (b: BindingDecl) : String.string. Admitted.
Definition pretty_cast (c: Cast) : String.string. Admitted.
Definition pretty_switch_branch (br: SwitchBranch) : String.string. Admitted.
Definition pretty_asm_ins (l: list (ident * Expr)) : String.string. Admitted.
Definition pretty_asm_outs (l: list (ident * Expr)) : String.string. Admitted.
Definition pretty_asm_clobbers (l: list ident) : String.string. Admitted.

Fixpoint pretty_stmt (s: Stmt) : String.string :=
  match s with
  | Sseq ss =>
      "{" ++ String.concat "" (List.map pretty_stmt ss) ++ "}"
  | Sdecl ds =>
      String.concat "; " (List.map pretty_vardecl ds) ++ ";"
  | Sif ovd cond tbranch fbranch =>
      let init_s := match ovd with
                    | Some d => pretty_vardecl d ++ "; "
                    | None => ""
                    end in
      "if (" ++ init_s ++ pretty_expr cond ++ ") "
        ++ pretty_stmt tbranch ++ " else " ++ pretty_stmt fbranch
  | Sif_consteval s1 s2 =>
      "if consteval " ++ pretty_stmt s1 ++ " else " ++ pretty_stmt s2
  | Swhile ovd cond body =>
      let init_s := match ovd with
                    | Some d => pretty_vardecl d ++ "; "
                    | None => ""
                    end in
      "while (" ++ init_s ++ pretty_expr cond ++ ") " ++ pretty_stmt body
  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pretty_stmt s' | None => "" end in
      let cond_s := match cond with Some e => pretty_expr e | None => "" end in
      let incr_s := match incr with Some e => pretty_expr e | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
        ++ pretty_stmt body
  | Sdo body cond =>
      "do " ++ pretty_stmt body ++ " while (" ++ pretty_expr cond ++ ");"
  | Sswitch ovd e body =>
      let init_s := match ovd with
                    | Some d => pretty_vardecl d ++ "; "
                    | None => ""
                    end in
      "switch (" ++ init_s ++ pretty_expr e ++ ") " ++ pretty_stmt body
  | Scase br =>
      "case " ++ pretty_switch_branch br ++ ":"
  | Sdefault => "default:"
  | Sbreak => "break;"
  | Scontinue => "continue;"
  | Sreturn oe =>
      "return" ++ match oe with
                  | Some e => " " ++ pretty_expr e
                  | None => ""
                  end ++ ";"
  | Sexpr e => pretty_expr e ++ ";"
  | Sattr attrs st =>
      "[" ++ String.concat " " (List.map id_to_string attrs) ++ "] "
        ++ pretty_stmt st
  | Sasm code volatile ins outs clobbers =>
      "asm('" ++ prim_to_String code ++ ": "
        ++ pretty_asm_ins ins ++ " : " ++ pretty_asm_outs outs
        ++ " : " ++ pretty_asm_clobbers clobbers ++ ")"
        ++ if volatile then " volatile;" else ";"
  | Slabeled lbl st =>
      id_to_string lbl ++ ": " ++ pretty_stmt st
  | Sgoto lbl => "goto " ++ id_to_string lbl ++ ";"
  | Sunsupported msg =>
      "/* unsupported: " ++ prim_to_String msg ++ " */"
  end.

Require Import Coq.Strings.String Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(* Helper: join a list of strings with a separator *)
Fixpoint join (sep : string) (l : list string) : string :=
  match l with
  | []      => ""
  | [x]     => x
  | x :: xs => x ++ sep ++ join sep xs
  end.


(* helper admits for all subcomponents *)

Definition id_to_string (i: ident) : PrimString.string. Admitted.
Definition pretty_name (n: name) : PrimString.string. Admitted.
Definition pretty_temp_arg (a: temp_arg) : PrimString.string. Admitted.
Definition pretty_type (t: type) : PrimString.string. Admitted.
Definition pretty_expr (e: Expr) : PrimString.string. Admitted.
Definition pretty_vardecl (d: VarDecl) : PrimString.string. Admitted.
Definition pretty_bindingdecl (b: BindingDecl) : PrimString.string. Admitted.
Definition pretty_cast (c: Cast) : PrimString.string. Admitted.
Definition pretty_switch_branch (br: SwitchBranch) : PrimString.string. Admitted.
Definition pretty_asm_ins (l: list (ident * Expr)) : PrimString.string. Admitted.
Definition pretty_asm_outs (l: list (ident * Expr)) : PrimString.string. Admitted.
Definition pretty_asm_clobbers (l: list ident) : PrimString.string. Admitted.

Search PrimString.string.
Fixpoint pretty_stmt (s: Stmt) : PrimString.string :=
  match s with
  | Sseq ss =>
      let parts := List.map pretty_stmt ss in
      "{" ++ PrimString.concat "" parts ++ "}"
  | Sdecl ds =>
      String.concat "; " (List.map pretty_vardecl ds) ++ ";"
  | Sif ovd cond tbranch fbranch =>
      let init_s := match ovd with
                    | Some d => pretty_vardecl d ++ "; "
                    | None => ""
                    end in
      "if (" ++ init_s ++ pretty_expr cond ++ ") "
        ++ pretty_stmt tbranch ++ " else " ++ pretty_stmt fbranch
  | Sif_consteval s1 s2 =>
      "if consteval " ++ pretty_stmt s1 ++ " else " ++ pretty_stmt s2
  | Swhile ovd cond body =>
      let init_s := match ovd with
                    | Some d => pretty_vardecl d ++ "; "
                    | None => ""
                    end in
      "while (" ++ init_s ++ pretty_expr cond ++ ") " ++ pretty_stmt body
  | Sfor init cond incr body =>
      let init_s := match init with Some s' => pretty_stmt s' | None => "" end in
      let cond_s := match cond with Some e => pretty_expr e | None => "" end in
      let incr_s := match incr with Some e => pretty_expr e | None => "" end in
      "for (" ++ init_s ++ "; " ++ cond_s ++ "; " ++ incr_s ++ ") "
        ++ pretty_stmt body
  | Sdo body cond =>
      "do " ++ pretty_stmt body ++ " while (" ++ pretty_expr cond ++ ");"
  | Sswitch ovd e body =>
      let init_s := match ovd with
                    | Some d => pretty_vardecl d ++ "; "
                    | None => ""
                    end in
      "switch (" ++ init_s ++ pretty_expr e ++ ") " ++ pretty_stmt body
  | Scase br =>
      "case " ++ pretty_switch_branch br ++ ":"
  | Sdefault => "default:"
  | Sbreak => "break;"
  | Scontinue => "continue;"
  | Sreturn oe =>
      "return" ++ match oe with
                  | Some e => " " ++ pretty_expr e
                  | None => ""
                  end ++ ";"
  | Sexpr e => pretty_expr e ++ ";"
  | Sattr attrs st =>
      "[" ++ String.concat " " (List.map id_to_string attrs) ++ "] "
        ++ pretty_stmt st
  | Sasm code volatile ins outs clobbers =>
      "asm(\"" ++ code ++ "\": "
        ++ pretty_asm_ins ins ++ " : " ++ pretty_asm_outs outs
        ++ " : " ++ pretty_asm_clobbers clobbers ++ ")"
        ++ if volatile then " volatile;" else ";"
  | Slabeled lbl st =>
      id_to_string lbl ++ ": " ++ pretty_stmt st
  | Sgoto lbl => "goto " ++ id_to_string lbl ++ ";"
  | Sunsupported msg =>
      "/* unsupported: " ++ msg ++ " */"
  end.

Axiom Zto_string: Z-> String.string.
Definition pretty_switch_branch (sb : SwitchBranch) : string :=
  match sb with
  | Exact n     => "case " ++ Zto_string n
  | Range lo hi => "case " ++ Zto_string lo ++ " ... " ++ Zto_string hi
  end.
*)
