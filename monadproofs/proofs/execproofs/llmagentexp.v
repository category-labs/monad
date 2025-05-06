Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.


Require Import Corelib.Strings.PrimString.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

(* ------------------------------------------------------------------ *)
(* primitive‐string alias and low‐level admits                         *)
Local Notation psstring := Corelib.Strings.PrimString.string.

Definition ps_of_string (s: string) : psstring.
Admitted.   (* TOFIXLATER: inject Coq [string] literals into PrimString *)

Definition Zstring (z: Z) : psstring.
Admitted.   (* TOFIXLATER: decimal‐print Z into Coq [string] then to psstring *)

Definition print_expr (e: Expr) : psstring.
Admitted.   (* TOFIXLATER: full Expr‐printer *)

Definition print_type (t: type) : psstring.
Admitted.   (* TOFIXLATER: full type‐printer *)

(* empty and concatenation *)
Definition ps_empty : psstring := ps_of_string "".
Local Infix "++" := Corelib.Strings.PrimString.cat
                        (at level 60, right associativity).

(* ------------------------------------------------------------------ *)
(* trivial helpers                                                    *)
Definition print_ident (id: ident) : psstring := id.

Definition print_binding_decl (bd: BindingDecl) : psstring :=
  match bd with
  | Bvar ln _ _  => ln
  | Bbind ln _ _ => ln
  end.

(* ------------------------------------------------------------------ *)
(* high‐level printers for [temp_arg] and [name] via mutual Fixpoint   *)
Fixpoint print_temp_arg (a: temp_arg) : psstring :=
  match a with
  | Atype t         => print_type t
  | Avalue e        => print_expr e
  | Apack args      =>
      ps_of_string "{" ++
      let fix go l :=
          match l with
          | nil   => ps_empty
          | x::xs => print_temp_arg x ++
                     match xs with
                     | nil => ps_empty
                     | _   => ps_of_string ", " ++ go xs
                     end
          end in
      go args ++ ps_of_string "}"
  | Atemplate nm    => print_name nm
  | Aunsupported s  =>
      ps_of_string "/*unsupported temp_arg:" ++
      s ++ ps_of_string "*/"
  end

with print_name (nm: name) : psstring :=
  let fix go_args l :=
      match l with
      | nil   => ps_empty
      | x::xs => print_temp_arg x ++
                 match xs with
                 | nil => ps_empty
                 | _   => ps_of_string ", " ++ go_args xs
                 end
      end in
  match nm with
  | Ninst base args =>
      print_name base ++ ps_of_string "<" ++ go_args args ++ ps_of_string ">"
  | Nglobal c        => c
  | Ndependent t     =>
      ps_of_string "<dependent " ++ print_type t ++ ps_of_string ">"
  | Nscoped n0 c     =>
      print_name n0 ++ ps_of_string "::" ++ c
  | Nunsupported s   =>
      ps_of_string "/*unsupported name:" ++
      s ++ ps_of_string "*/"
  end.

(* ------------------------------------------------------------------ *)
(* variable‐decl and switch‐branch printers                           *)
Definition print_var_decl (d: VarDecl) : psstring :=
  match d with
  | Dvar ln ty oe =>
      print_type ty ++ ps_of_string " " ++ ln ++
      match oe with
      | Some e => ps_of_string " = " ++ print_expr e
      | None   => ps_empty
      end

  | Ddecompose e _ binds =>
      ps_of_string "auto [" ++
      let fix go l :=
          match l with
          | nil    => ps_empty
          | x::nil => print_binding_decl x
          | x::xs  => print_binding_decl x ++ ps_of_string ", " ++ go xs
          end in
      go binds ++ ps_of_string "] = " ++ print_expr e

  | Dinit thread_safe nm ty oe =>
      (if thread_safe then ps_of_string "thread_local " else ps_empty) ++
      print_type ty ++ ps_of_string " " ++ print_name nm ++
      match oe with
      | Some e => ps_of_string " = " ++ print_expr e
      | None   => ps_empty
      end
  end.

Definition print_switch_branch (br: SwitchBranch) : psstring :=
  match br with
  | Exact z    => ps_of_string "case " ++ Zstring z ++ ps_of_string ":;"
  | Range lo hi =>
      ps_of_string "case " ++ Zstring lo ++
      ps_of_string " ... " ++ Zstring hi ++
      ps_of_string ":;"
  end.

(* ------------------------------------------------------------------ *)
(* main printer for statements                                        *)
Fixpoint print_stmt (s: Stmt) : psstring :=
  let fix print_list (l: list Stmt) : psstring :=
      match l with
      | nil     => ps_empty
      | x :: xs => print_stmt x ++ print_list xs
      end in

  match s with
  | Sseq ss      => ps_of_string "{" ++ print_list ss ++ ps_of_string "}"
  | Sdecl ds     =>
      let fix go l :=
          match l with
          | nil     => ps_empty
          | x :: xs => print_var_decl x ++ ps_of_string ";" ++ go xs
          end in
      go ds

  | Sif od c t e =>
      ps_of_string "if (" ++
        match od with Some d => print_var_decl d ++ ps_of_string ";"
                   | None   => ps_empty end ++
      print_expr c ++ ps_of_string ") " ++
      print_stmt t ++ ps_of_string " else " ++ print_stmt e

  | Sif_consteval t e =>
      ps_of_string "if consteval " ++ print_stmt t ++
      ps_of_string " else " ++ print_stmt e

  | Swhile od c b =>
      ps_of_string "while (" ++
        match od with Some d => print_var_decl d ++ ps_of_string ";"
                   | None   => ps_empty end ++
      print_expr c ++ ps_of_string ") " ++ print_stmt b

  | Sfor i c s0 b =>
      ps_of_string "for (" ++
        (match i  with Some s1 => print_stmt s1 | None => ps_empty end) ++
      ps_of_string ";" ++
        (match c  with Some e  => print_expr e | None => ps_empty end) ++
      ps_of_string ";" ++
        (match s0 with Some e  => print_expr e | None => ps_empty end) ++
      ps_of_string ") " ++ print_stmt b

  | Sdo b c =>
      ps_of_string "do " ++ print_stmt b ++
      ps_of_string " while (" ++ print_expr c ++ ps_of_string ");"

  | Sswitch od e b =>
      ps_of_string "switch (" ++
        match od with Some d => print_var_decl d ++ ps_of_string ";"
                   | None   => ps_empty end ++
      print_expr e ++ ps_of_string ") " ++ print_stmt b

  | Scase br      => print_switch_branch br
  | Sdefault      => ps_of_string "default:;"
  | Sbreak        => ps_of_string "break;"
  | Scontinue     => ps_of_string "continue;"

  | Sreturn oe    =>
      ps_of_string "return" ++
        (match oe with Some e => ps_of_string " " ++ print_expr e
                     | None   => ps_empty end) ++
      ps_of_string ";"

  | Sexpr e       => print_expr e ++ ps_of_string ";"

  | Sattr ids st  =>
      ps_of_string "[[" ++
        let fix go_id l :=
            match l with
            | nil     => ps_empty
            | x :: xs => print_ident x ++
                         match xs with
                         | nil => ps_empty
                         | _   => ps_of_string ", " ++ go_id xs
                         end
            end in
      go_id ids ++ ps_of_string "]] " ++ print_stmt st

  | Sasm str vol _ _ _ =>
      ps_of_string "asm(" ++ str ++
      ps_of_string ", /*volatile=" ++
        (if vol then ps_of_string "true" else ps_of_string "false") ++
      ps_of_string "*/, /*…*/);"

  | Slabeled lbl st => lbl ++ ps_of_string ": " ++ print_stmt st
  | Sgoto lbl       => ps_of_string "goto " ++ lbl ++ ps_of_string ";"
  | Sunsupported s  => ps_of_string "// unsupported stmt: " ++ s
  end.

