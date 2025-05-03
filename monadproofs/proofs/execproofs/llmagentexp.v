Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.


```gallina
Require Import String List.
Import ListNotations.
Open Scope string_scope.

(* Admit all the helper printers; you can implement them later. *)
Definition print_name (n: name) : string. Admitted.
Definition print_type (t : type) : string. Admitted.
Definition print_expr (e : Expr) : string. Admitted.
Definition print_var_decl (vd : VarDecl) : string. Admitted.
Definition print_binding_decl (bd : BindingDecl) : string. Admitted.
Definition print_cast (c : Cast) : string. Admitted.
Definition print_switch_branch (b : SwitchBranch) : string. Admitted.

(* A small utility to join a list with a separator. *)
Fixpoint concat_with_sep {A} (f : A -> string) (sep : string) (l : list A) : string :=
  match l with
  | [] => ""
  | x :: xs =>
    fold_left (fun acc y => acc ++ sep ++ f y) xs (f x)
  end.

Fixpoint print_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      concat_with_sep print_stmt ";\n" ss
  | Sdecl vds =>
      "decl " ++ concat_with_sep print_var_decl "; " vds
  | Sif vd_opt cond then_s else_s =>
      let init :=
        match vd_opt with
        | Some vd => print_var_decl vd ++ "; "
        | None => ""
        end in
      "if(" ++ init ++ print_expr cond ++ ") {\n"
        ++ print_stmt then_s ++ "\n} else {\n"
        ++ print_stmt else_s ++ "\n}"
  | Sif_consteval thn els =>
      "if consteval {\n"
        ++ print_stmt thn ++ "\n} else {\n"
        ++ print_stmt els ++ "\n}"
  | Swhile vd_opt cond body =>
      let init :=
        match vd_opt with
        | Some vd => print_var_decl vd ++ "; "
        | None => ""
        end in
      "while(" ++ init ++ print_expr cond ++ ") {\n"
        ++ print_stmt body ++ "\n}"
  | Sfor init cond iter body =>
      let s_init := match init with Some s' => print_stmt s' | None => "" end in
      let s_cond := match cond with Some e => print_expr e | None => "" end in
      let s_iter := match iter with Some e => print_expr e | None => "" end in
      "for(" ++ s_init ++ "; " ++ s_cond ++ "; " ++ s_iter ++ ") {\n"
        ++ print_stmt body ++ "\n}"
  | Sdo body cond =>
      "do {\n" ++ print_stmt body ++ "\n} while(" ++ print_expr cond ++ ")"
  | Sswitch vd_opt e body =>
      let init :=
        match vd_opt with
        | Some vd => print_var_decl vd ++ "; "
        | None => ""
        end in
      "switch(" ++ init ++ print_expr e ++ ") {\n"
        ++ print_stmt body ++ "\n}"
  | Scase br =>
      "case " ++ print_switch_branch br
  | Sdefault => "default"
  | Sbreak => "break"
  | Scontinue => "continue"
  | Sreturn eo =>
      match eo with
      | Some e => "return " ++ print_expr e
      | None => "return"
      end
  | Sexpr e =>
      print_expr e
  | Sattr attrs s' =>
      concat_with_sep (fun x=>x) " " attrs ++ " " ++ print_stmt s'
  | Sasm str _volatile inputs outputs clobbers =>
      "asm \"" ++ str ++ "\""
  | Slabeled id s' =>
      id ++ ": " ++ print_stmt s'
  | Sgoto id =>
      "goto " ++ id
  | Sunsupported s' =>
      "unsupported_stmt(\"" ++ s' ++ "\")"
  end.

```
