Require Import bluerock.auto.invariants.
Set Printing FullyQualifiedNames.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Disable Notation atomic_name.
Open Scope pstring_scope.

(*
bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
Write a set of mutually recursive pretty-printer functions for all such types.
These Gallina functions should return `string`.
In the current context, `string` refers to `PrimString.string`, which is unusual in non-recent Coq developments. 
PrimString.string is a new type in Coq's core standard library. It axiomatizes primitive strings.
The scope delimiting key for  PrimString.string is pstring.
So, `(a ++ b)%pstring` appends `a:PrimString.string` and `b:PrimString.string`.
I have already opened pstring_scope so you may be able to elide the %pstring part.
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.
*)

Require Import Corelib.Init.Datatypes.       (* list, option, bool, N, Z *)
Require Import Corelib.Strings.PrimString.   (* PrimString.string *)
Require Import bluerock.lang.cpp.syntax.core.        (* name', temp_arg', Expr', Stmt', VarDecl', BindingDecl', Cast', atomic_name *)
Require Import bluerock.lang.cpp.syntax.preliminary. (* ident, UnOp, BinOp, float_type, … *)
Require Import bluerock.lang.cpp.syntax.overloadable. (* RUnOp, RBinOp *)

Open Scope pstring.

(* -------------------------------------------------------------------- *)
(* Low‐level routines, to be implemented later *)
Definition Ztostring (z: Z)                                           : string. Admitted. (* TOFIXLATER *)
Definition Ntostring (n: N)                                           : string. Admitted. (* TOFIXLATER *)

(* implemented *)
Definition booltostring (b: bool) : string :=
  if b then "true" else "false".

(* implemented *)
Definition pp_ident (i: bluerock.lang.cpp.syntax.preliminary.ident) : string :=
  i.

(* implemented *)
Definition pp_atomic_name (a: bluerock.lang.cpp.syntax.core.atomic_name) : string :=
  a.

Definition pp_RUnOp  (op: bluerock.lang.cpp.syntax.overloadable.RUnOp)  : string. Admitted. (* TOFIXLATER *)
Definition pp_RBinOp (op: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted. (* TOFIXLATER *)
Definition pp_UnOp   (op: bluerock.lang.cpp.syntax.preliminary.UnOp)    : string. Admitted. (* TOFIXLATER *)
Definition pp_BinOp  (op: bluerock.lang.cpp.syntax.preliminary.BinOp)   : string. Admitted. (* TOFIXLATER *)
Definition pp_type   (t: bluerock.lang.cpp.syntax.core.type')         : string. Admitted. (* TOFIXLATER *)

(* -------------------------------------------------------------------- *)
(* Main mutually‐recursive pretty‐printers *)

Fixpoint pp_name (n: bluerock.lang.cpp.syntax.core.name') : string :=
  match n with
  | bluerock.lang.cpp.syntax.core.Ninst n' args =>
      let fix go (l: list bluerock.lang.cpp.syntax.core.temp_arg') : string :=
          match l with
          | [] => ""
          | x :: [] => pp_temp_arg x
          | x :: xs => pp_temp_arg x ++ "," ++ go xs
          end in
      pp_name n' ++ "<" ++ go args ++ ">"

  | bluerock.lang.cpp.syntax.core.Nglobal an =>
      pp_atomic_name an

  | bluerock.lang.cpp.syntax.core.Ndependent ty =>
      "dependent<" ++ pp_type ty ++ ">"

  | bluerock.lang.cpp.syntax.core.Nscoped n' c =>
      pp_name n' ++ "::" ++ pp_atomic_name c

  | bluerock.lang.cpp.syntax.core.Nunsupported s =>
      s
  end

with pp_temp_arg (a: bluerock.lang.cpp.syntax.core.temp_arg') : string :=
  match a with
  | bluerock.lang.cpp.syntax.core.Atype ty =>
      pp_type ty
  | bluerock.lang.cpp.syntax.core.Avalue e =>
      pp_expr e
  | bluerock.lang.cpp.syntax.core.Apack args =>
      let fix go (l: list bluerock.lang.cpp.syntax.core.temp_arg') : string :=
          match l with
          | [] => ""
          | x :: [] => pp_temp_arg x
          | x :: xs => pp_temp_arg x ++ "," ++ go xs
          end in
      "pack(" ++ go args ++ ")"
  | bluerock.lang.cpp.syntax.core.Atemplate n =>
      pp_name n
  | bluerock.lang.cpp.syntax.core.Aunsupported s =>
      s
  end

with pp_expr (e: bluerock.lang.cpp.syntax.core.Expr') : string :=
  match e with
  | bluerock.lang.cpp.syntax.core.Eparam id =>
      pp_ident id
  | bluerock.lang.cpp.syntax.core.Eunresolved_global n =>
      pp_name n
  | bluerock.lang.cpp.syntax.core.Eunresolved_unop op e1 =>
      "(" ++ pp_RUnOp op ++ pp_expr e1 ++ ")"
  | bluerock.lang.cpp.syntax.core.Eunresolved_binop op e1 e2 =>
      "(" ++ pp_expr e1 ++ pp_RBinOp op ++ pp_expr e2 ++ ")"
  | bluerock.lang.cpp.syntax.core.Eunresolved_call f args =>
      let fix go (l: list bluerock.lang.cpp.syntax.core.Expr') : string :=
          match l with
          | [] => ""
          | x :: [] => pp_expr x
          | x :: xs => pp_expr x ++ "," ++ go xs
          end in
      pp_name f ++ "(" ++ go args ++ ")"
  | bluerock.lang.cpp.syntax.core.Ecall f args =>
      let fix go (l: list bluerock.lang.cpp.syntax.core.Expr') : string :=
          match l with
          | [] => ""
          | x :: [] => pp_expr x
          | x :: xs => pp_expr x ++ "," ++ go xs
          end in
      pp_expr f ++ "(" ++ go args ++ ")"
  | bluerock.lang.cpp.syntax.core.Eint z ty =>
      Ztostring z ++ ":" ++ pp_type ty
  | bluerock.lang.cpp.syntax.core.Ebool b =>
      booltostring b
  | bluerock.lang.cpp.syntax.core.Eunsupported s _ =>
      s
  | _ =>
      "<?>"  (* catch‐all *)
  end

with pp_stmt (s: bluerock.lang.cpp.syntax.core.Stmt') : string :=
  match s with
  | bluerock.lang.cpp.syntax.core.Sseq ss =>
      let fix go (l: list bluerock.lang.cpp.syntax.core.Stmt') : string :=
          match l with
          | [] => ""
          | x :: [] => pp_stmt x
          | x :: xs => pp_stmt x ++ " " ++ go xs
          end in
      "{" ++ go ss ++ "}"
  | bluerock.lang.cpp.syntax.core.Sdecl ds =>
      let fix go (l: list bluerock.lang.cpp.syntax.core.VarDecl') : string :=
          match l with
          | [] => ""
          | x :: [] => pp_vardecl x
          | x :: xs => pp_vardecl x ++ "," ++ go xs
          end in
      go ds ++ ";"
  | bluerock.lang.cpp.syntax.core.Sif _vd cond thn els =>
      "if(" ++ pp_expr cond ++ ")" ++ pp_stmt thn ++ " else " ++ pp_stmt els
  | bluerock.lang.cpp.syntax.core.Swhile _vd cond body =>
      "while(" ++ pp_expr cond ++ ")" ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sexpr e =>
      pp_expr e ++ ";"
  | _ =>
      "<?>"  (* catch‐all *)
  end

with pp_vardecl (d: bluerock.lang.cpp.syntax.core.VarDecl') : string :=
  match d with
  | bluerock.lang.cpp.syntax.core.Dvar nm ty init_opt =>
      pp_ident nm ++ ":" ++ pp_type ty ++
      match init_opt with
      | Some e => " = " ++ pp_expr e
      | None   => ""
      end
  | _ =>
      "<?>"  (* catch‐all *)
  end

with pp_bindingdecl (bd: bluerock.lang.cpp.syntax.core.BindingDecl') : string :=
  match bd with
  | bluerock.lang.cpp.syntax.core.Bvar nm ty init =>
      pp_ident nm ++ ":" ++ pp_type ty ++ " = " ++ pp_expr init
  | bluerock.lang.cpp.syntax.core.Bbind nm ty init =>
      pp_ident nm ++ ":" ++ pp_type ty ++ " = " ++ pp_expr init
  end

with pp_cast (c: bluerock.lang.cpp.syntax.core.Cast') : string :=
  match c with
  | bluerock.lang.cpp.syntax.core.Cdependent ty =>
      "cast_dep<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Cbitcast ty =>
      "bitcast<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Cnoop ty =>
      "noop<" ++ pp_type ty ++ ">"
  | _ =>
      "<?>"  (* catch‐all *)
  end.

