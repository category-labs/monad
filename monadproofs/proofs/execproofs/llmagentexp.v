Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.


Require Import Coq.Strings.String Coq.Lists.List Coq.Arith.PeanoNat.
Import ListNotations.
Local Open Scope string_scope.

(* -------------------------------------------------------------------- *)
(* 1) stubs for the leaf printers – fill these in later                *)
Definition pp_list {A} (f : A -> string) (sep : string) (xs : list A) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition id_to_string (i : ident) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_name (n : name) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_type (t : type) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_expr (e : Expr) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_vardecl (d : VarDecl) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_bindingdecl (b : BindingDecl) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_cast (c : Cast) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_switchbranch (sb : SwitchBranch) : string.
Admitted. (* TODO: FILL IN LATER *)

Definition pp_prim (s : PrimString.string) : string.
Admitted. (* TODO: FILL IN LATER *)

(* -------------------------------------------------------------------- *)
(* 2) A simple size bound on a statement                                *)
Fixpoint total_size (s : Stmt) : nat :=
  match s with
  | Sseq ss           => 1 + fold_left (fun acc x => acc + total_size x) ss 0
  | Sdecl _           => 1
  | Sif _ _ thn els   => 1 + total_size thn + total_size els
  | Sif_consteval t f => 1 + total_size t + total_size f
  | Swhile _ _ body   => 1 + total_size body
  | Sfor init _ _ body =>
      1 + (match init with None => 0 | Some st => total_size st end)
        + total_size body
  | Sdo body _        => 1 + total_size body
  | Sswitch _ _ body  => 1 + total_size body
  | Scase _           => 1
  | Sdefault          => 1
  | Sbreak            => 1
  | Scontinue         => 1
  | Sreturn _         => 1
  | Sexpr _           => 1
  | Sattr _ st        => 1 + total_size st
  | Sasm _ _ _ _ _    => 1
  | Slabeled _ st     => 1 + total_size st
  | Sgoto _           => 1
  | Sunsupported _    => 1
  end.

(* -------------------------------------------------------------------- *)
(* 3) fuel‐driven pretty‐printer                                        *)
Fixpoint pp_stmt_fuel (fuel : nat) (s : Stmt) : string :=
  match fuel with
  | 0 => ""  (* out of fuel – should not happen if we start with total_size *)
  | S fuel' =>
    match s with
    | Sseq ss =>
        match ss with
        | []       => ""
        | hd :: tl => pp_stmt_fuel fuel' hd
                        ++ "\n"
                        ++ pp_stmt_fuel fuel' (Sseq tl)
        end

    | Sdecl ds =>
        "decl " ++ pp_list pp_vardecl "; " ds

    | Sif od e thn els =>
        let bind := match od with
                    | Some d => pp_vardecl d ++ "; "
                    | None   => "" end in
        "if(" ++ bind ++ pp_expr e ++ ") {\n"
             ++ pp_stmt_fuel fuel' thn ++ "\n}"
             ++ match els with
                | Sseq [] => ""
                | _       => " else {\n" ++ pp_stmt_fuel fuel' els ++ "\n}"
                end

    | Sif_consteval t f =>
        "if_consteval {\n"
          ++ pp_stmt_fuel fuel' t ++ "\n} else {\n"
          ++ pp_stmt_fuel fuel' f ++ "\n}"

    | Swhile od e body =>
        let bind := match od with
                    | Some d => pp_vardecl d ++ "; "
                    | None   => "" end in
        "while(" ++ bind ++ pp_expr e ++ ") {\n"
             ++ pp_stmt_fuel fuel' body ++ "\n}"

    | Sfor init cond iter body =>
        let s_i := match init with | None => "" | Some st => pp_stmt_fuel fuel' st end in
        let s_c := match cond with | None => "" | Some e  => pp_expr e end in
        let s_m := match iter with | None => "" | Some e  => pp_expr e end in
        "for(" ++ s_i ++ "; " ++ s_c ++ "; " ++ s_m ++ ") {\n"
               ++ pp_stmt_fuel fuel' body ++ "\n}"

    | Sdo body e =>
        "do " ++ pp_stmt_fuel fuel' body ++ " while(" ++ pp_expr e ++ ");"

    | Sswitch od e body =>
        let bind := match od with
                    | Some d => pp_vardecl d ++ "; "
                    | None   => "" end in
        "switch(" ++ bind ++ pp_expr e ++ ") {\n"
             ++ pp_stmt_fuel fuel' body ++ "\n}"

    | Scase sb =>
        "case " ++ pp_switchbranch sb ++ ":"

    | Sdefault =>
        "default:"

    | Sbreak   => "break;"
    | Scontinue => "continue;"

    | Sreturn None =>
        "return;"

    | Sreturn (Some e) =>
        "return " ++ pp_expr e ++ ";"

    | Sexpr e =>
        pp_expr e ++ ";"

    | Sattr attrs st =>
        "[[" ++ pp_list id_to_string " " attrs ++ "]] "
          ++ pp_stmt_fuel fuel' st

    | Sasm str vol inputs outputs clobbers =>
        "asm(" ++ pp_prim str ++ ") /* volatile="
           ++ (if vol then "yes" else "no")
           ++ "; in="  ++ pp_list (fun io => id_to_string (fst io) ++ ": " ++ pp_expr (snd io)) ", " inputs
           ++ "; out=" ++ pp_list (fun io => id_to_string (fst io) ++ ": " ++ pp_expr (snd io)) ", " outputs
           ++ "; clobbers=" ++ pp_list id_to_string ", " clobbers
           ++ " */"

    | Slabeled l st =>
        id_to_string l ++ ": " ++ pp_stmt_fuel fuel' st

    | Sgoto l =>
        "goto " ++ id_to_string l ++ ";"

    | Sunsupported s =>
        "/* unsupported: " ++ pp_prim s ++ " */"
    end
  end.

Definition pretty_print_stmt (s : Stmt) : string :=
  pp_stmt_fuel (total_size s) s.

Module MyCPPPrinter.
  Require Import Coq.Strings.String Coq.Lists.List Coq.Arith.PeanoNat.
  Import ListNotations.
  Local Open Scope string_scope.

  (* ------------------------------------------------------------------ *)
  (* 1) Our own list‐printer and ident‐printer (no name conflicts)      *)
  Definition pp_list_impl {A} (f : A → string) (sep : string)
             (xs : list A) : string :=
    let fix go l := match l with
      | []       => ""
      | [x]      => f x
      | x :: xs' => f x ++ sep ++ go xs'
      end in
    go xs.

  Definition pp_ident (i : ident) : string :=
    (* convert AST‐ident (PrimString.string) via pp_prim stub below *)
    pp_prim i.

  (* ------------------------------------------------------------------ *)
  (* 2) High‐level printers for VarDecl and BindingDecl                *)
  Definition pp_vardecl (d : VarDecl) : string :=
    match d with
    | Dvar ln ty None =>
        pp_ident ln ++ " : " ++ pp_type ty
    | Dvar ln ty (Some e) =>
        pp_ident ln ++ " : " ++ pp_type ty ++ " = " ++ pp_expr e
    | Ddecompose e id bs =>
        "decompose " ++ pp_expr e ++ " as " ++ pp_ident id
          ++ " { " ++ pp_list_impl pp_bindingdecl ", " bs ++ " }"
    | Dinit b n ty None =>
        (if b then "thread_safe " else "") ++ pp_name n ++ " : " ++ pp_type ty
    | Dinit b n ty (Some e) =>
        (if b then "thread_safe " else "") ++ pp_name n ++ " : " ++ pp_type ty
          ++ " = " ++ pp_expr e
    end.

  Definition pp_bindingdecl (b : BindingDecl) : string :=
    match b with
    | Bvar ln ty e =>
        pp_ident ln ++ " : " ++ pp_type ty ++ " ⇒ " ++ pp_expr e
    | Bbind ln ty e =>
        pp_ident ln ++ " : " ++ pp_type ty ++ " ↦ " ++ pp_expr e
    end.

  (* ------------------------------------------------------------------ *)
  (* 3) Leaf‐printers to fill in later                                 *)
  Definition pp_name (n : name) : string. Admitted.               (* TODO *)
  Definition pp_type (t : type) : string. Admitted.               (* TODO *)
  Definition pp_expr (e : Expr) : string. Admitted.               (* TODO *)
  Definition pp_cast (c : Cast) : string. Admitted.               (* TODO *)
  Definition pp_switchbranch (sb : SwitchBranch) : string. Admitted. (* TODO *)
  Definition pp_prim (s : PrimString.string) : string. Admitted.  (* TODO *)

  (* ------------------------------------------------------------------ *)
  (* 4) A crude “size” bound for fuel‐driven recursion                 *)
  Fixpoint total_size (s : Stmt) : nat :=
    match s with
    | Sseq ss           => 1 + fold_left (fun acc x => acc + total_size x) ss 0
    | Sdecl _           => 1
    | Sif _ _ thn els   => 1 + total_size thn + total_size els
    | Sif_consteval t f => 1 + total_size t + total_size f
    | Swhile _ _ body   => 1 + total_size body
    | Sfor init _ _ body =>
        1 + (match init with None => 0 | Some st => total_size st end)
          + total_size body
    | Sdo body _        => 1 + total_size body
    | Sswitch _ _ body  => 1 + total_size body
    | Scase _           => 1
    | Sdefault          => 1
    | Sbreak            => 1
    | Scontinue         => 1
    | Sreturn _         => 1
    | Sexpr _           => 1
    | Sattr _ st        => 1 + total_size st
    | Sasm _ _ _ _ _    => 1
    | Slabeled _ st     => 1 + total_size st
    | Sgoto _           => 1
    | Sunsupported _    => 1
    end.

  (* ------------------------------------------------------------------ *)
  (* 5) Fuel‐driven pretty‐printer                                      *)
  Fixpoint pp_stmt_fuel (fuel : nat) (s : Stmt) : string :=
    match fuel with
    | 0 => ""  (* out of fuel – shouldn’t happen if we start at total_size *)
    | S fuel' =>
      match s with
      | Sseq ss =>
          match ss with
          | []       => ""
          | hd :: tl =>
              pp_stmt_fuel fuel' hd ++ "\n"
            ++ pp_stmt_fuel fuel' (Sseq tl)
          end

      | Sdecl ds =>
          "decl " ++ pp_list_impl pp_vardecl "; " ds

      | Sif od e thn els =>
          let bind := match od with
                      | Some d => pp_vardecl d ++ "; "
                      | None   => "" end in
          "if(" ++ bind ++ pp_expr e ++ ") {\n"
               ++ pp_stmt_fuel fuel' thn ++ "\n}"
               ++ match els with
                  | Sseq [] => ""
                  | _       => " else {\n" ++ pp_stmt_fuel fuel' els ++ "\n}"
                  end

      | Sif_consteval t f =>
          "if_consteval {\n"
            ++ pp_stmt_fuel fuel' t ++ "\n} else {\n"
            ++ pp_stmt_fuel fuel' f ++ "\n}"

      | Swhile od e body =>
          let bind := match od with
                      | Some d => pp_vardecl d ++ "; "
                      | None   => "" end in
          "while(" ++ bind ++ pp_expr e ++ ") {\n"
               ++ pp_stmt_fuel fuel' body ++ "\n}"

      | Sfor init cond iter body =>
          let s_i := match init with None => "" | Some st => pp_stmt_fuel fuel' st end in
          let s_c := match cond with None => ""  | Some e => pp_expr e end in
          let s_m := match iter with None => ""  | Some e => pp_expr e end in
          "for(" ++ s_i ++ "; " ++ s_c ++ "; " ++ s_m ++ ") {\n"
                 ++ pp_stmt_fuel fuel' body ++ "\n}"

      | Sdo body e =>
          "do " ++ pp_stmt_fuel fuel' body ++ " while(" ++ pp_expr e ++ ");"

      | Sswitch od e body =>
          let bind := match od with
                      | Some d => pp_vardecl d ++ "; "
                      | None   => "" end in
          "switch(" ++ bind ++ pp_expr e ++ ") {\n"
               ++ pp_stmt_fuel fuel' body ++ "\n}"

      | Scase sb =>
          "case " ++ pp_switchbranch sb ++ ":"

      | Sdefault => "default:"

      | Sbreak   => "break;"
      | Scontinue => "continue;"

      | Sreturn None => "return;"
      | Sreturn (Some e) => "return " ++ pp_expr e ++ ";"

      | Sexpr e => pp_expr e ++ ";"

      | Sattr attrs st =>
          "[[" ++ pp_list_impl pp_ident " " attrs ++ "]] "
            ++ pp_stmt_fuel fuel' st

      | Sasm str vol inputs outputs clobbers =>
          "asm(" ++ pp_prim str ++ ") /* volatile="
             ++ (if vol then "yes" else "no")
             ++ "; in="  ++ pp_list_impl (fun io => pp_ident (fst io) ++ ": " ++ pp_expr (snd io)) ", " inputs
             ++ "; out=" ++ pp_list_impl (fun io => pp_ident (fst io) ++ ": " ++ pp_expr (snd io)) ", " outputs
             ++ "; clobbers=" ++ pp_list_impl pp_ident ", " clobbers
             ++ " */"

      | Slabeled l st =>
          pp_ident l ++ ": " ++ pp_stmt_fuel fuel' st

      | Sgoto l => "goto " ++ pp_ident l ++ ";"

      | Sunsupported s =>
          "/* unsupported: " ++ pp_prim s ++ " */"
      end
    end.

  (* ------------------------------------------------------------------ *)
  (* 6) Public API                                                      *)
  Definition pretty_print_stmt (s : Stmt) : string :=
    pp_stmt_fuel (total_size s) s.

End MyCPPPrinter.




Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope string_scope.

(* helper to turn an identifier into a string *)
Definition identToString (id : ident) : string. Admitted. (* TODO: FILL IN LATER *)

(* placeholders for sub‐printers *)
Definition ppExpr (e : Expr) : string. Admitted.            (* TODO: FILL IN LATER *)
Definition ppVarDecl (d : VarDecl) : string. Admitted.      (* TODO: FILL IN LATER *)
Definition ppSwitchBranch (b : SwitchBranch) : string. Admitted. (* TODO: FILL IN LATER *)

Fixpoint ppStmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      "{" ++ String.concat ";" (List.map ppStmt ss) ++ "}"
  | Sdecl ds =>
      String.concat ";" (List.map ppVarDecl ds)
  | Sif dv cond thn els =>
      let init := match dv with None => "" | Some d => ppVarDecl d ++ ";" end in
      "if(" ++ ppExpr cond ++ ")" ++ " " ++ init ++ ppStmt thn ++ " else " ++ ppStmt els
  | Sif_consteval thn els =>
      "if consteval " ++ ppStmt thn ++ " else " ++ ppStmt els
  | Swhile dv cond body =>
      let init := match dv with None => "" | Some d => ppVarDecl d ++ ";" end in
      "while(" ++ ppExpr cond ++ ")" ++ " " ++ init ++ ppStmt body
  | Sfor minit mcond mstep body =>
      let s_init := match minit  with None => ""        | Some st => ppStmt st end in
      let s_cond := match mcond with None => ""        | Some e  => ppExpr e end in
      let s_step := match mstep with None => ""        | Some e  => ppExpr e end in
      "for(" ++ s_init ++ ";" ++ s_cond ++ ";" ++ s_step ++ ")" ++ " " ++ ppStmt body
  | Sdo body cond =>
      "do " ++ ppStmt body ++ " while(" ++ ppExpr cond ++ ");"
  | Sswitch dv cond body =>
      let init := match dv with None => "" | Some d => ppVarDecl d ++ ";" end in
      "switch(" ++ init ++ ppExpr cond ++ ")" ++ " " ++ ppStmt body
  | Scase br =>
      "case " ++ ppSwitchBranch br
  | Sdefault =>
      "default:"
  | Sbreak =>
      "break;"
  | Scontinue =>
      "continue;"
  | Sreturn mexpr =>
      let arg := match mexpr with None => "" | Some e => " " ++ ppExpr e end in
      "return" ++ arg ++ ";"
  | Sexpr e =>
      ppExpr e ++ ";"
  | Sattr attrs st =>
      "[[" ++ String.concat " " (List.map identToString attrs) ++ "]] " ++ ppStmt st
  | Sasm _ _ _ _ _ =>
      "asm(/*…*/)"
  | Slabeled lbl st =>
      identToString lbl ++ ": " ++ ppStmt st
  | Sgoto lbl =>
      "goto " ++ identToString lbl ++ ";"
  | Sunsupported _ =>
      "/* unsupported stmt */"
  end.

