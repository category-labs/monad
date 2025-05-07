Require Import bluerock.auto.invariants.
Set Printing FullyQualifiedNames.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
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
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.Require Import PrimString.
 *)

Require Import PrimString Coq.Lists.List.
Open Scope pstring_scope.

(* --------------------------------------------------------------------- *)
(* Primitive‐to‐string stubs: fill these in later *)
Definition ident_to_string      (id: bluerock.lang.cpp.syntax.preliminary.ident)     : string
  := id.
(* no TOFIXLATER *)

Definition atomic_name_to_string(an: bluerock.lang.cpp.syntax.core.atomic_name)      : string.
Admitted. (* TOFIXLATER *)

Definition Z_to_string          (z: Corelib.Numbers.BinNums.Z)                       : string.
Admitted. (* TOFIXLATER *)

Definition N_to_string          (n: Corelib.Numbers.BinNums.N)                       : string.
Admitted. (* TOFIXLATER *)

Definition bool_to_string       (b: Corelib.Init.Datatypes.bool)                     : string :=
  if b then "true"%pstring else "false"%pstring.
(* no TOFIXLATER *)

Definition ru_op_to_string      (op: bluerock.lang.cpp.syntax.overloadable.RUnOp)     : string. Admitted. (* TOFIXLATER *)
Definition rb_op_to_string      (op: bluerock.lang.cpp.syntax.overloadable.RBinOp)    : string. Admitted. (* TOFIXLATER *)
Definition unop_to_string       (op: bluerock.lang.cpp.syntax.preliminary.UnOp)       : string. Admitted. (* TOFIXLATER *)
Definition binop_to_string      (op: bluerock.lang.cpp.syntax.preliminary.BinOp)      : string. Admitted. (* TOFIXLATER *)

(* --------------------------------------------------------------------- *)
(* join a list of A’s with separator [sep], right‐associative folding *)
Definition pp_sep_list {A:Type} (sep:string) (f:A->string) (l:list A) : string :=
  List.fold_right (fun x acc => f x ++ sep ++ acc) "" l.

(* --------------------------------------------------------------------- *)
Fixpoint pp_name
         (n: bluerock.lang.cpp.syntax.core.name) : string :=
  match n with
  | bluerock.lang.cpp.syntax.core.Ninst base args =>
      pp_name base ++ "<"%pstring ++ pp_sep_list "," pp_temp_arg args ++ ">"%pstring
  | bluerock.lang.cpp.syntax.core.Nglobal an =>
      atomic_name_to_string an
  | bluerock.lang.cpp.syntax.core.Ndependent t =>
      "dependent<"%pstring ++ pp_type t ++ ">"%pstring
  | bluerock.lang.cpp.syntax.core.Nscoped ns an =>
      pp_name ns ++ "::"%pstring ++ atomic_name_to_string an
  | bluerock.lang.cpp.syntax.core.Nunsupported s =>
      s
  end

with pp_temp_arg
         (a: bluerock.lang.cpp.syntax.core.temp_arg) : string :=
  match a with
  | bluerock.lang.cpp.syntax.core.Atype t =>
      pp_type t
  | bluerock.lang.cpp.syntax.core.Avalue e =>
      pp_expr e
  | bluerock.lang.cpp.syntax.core.Apack ts =>
      "pack<"%pstring ++ pp_sep_list "," pp_temp_arg ts ++ ">"%pstring
  | bluerock.lang.cpp.syntax.core.Atemplate n =>
      pp_name n
  | bluerock.lang.cpp.syntax.core.Aunsupported s =>
      s
  end

with pp_type
         (t: bluerock.lang.cpp.syntax.core.type) : string :=
  match t with
  | bluerock.lang.cpp.syntax.core.Tparam id =>
      ident_to_string id
  | bluerock.lang.cpp.syntax.core.Tresult_param id =>
      ident_to_string id
  | bluerock.lang.cpp.syntax.core.Tresult_global n =>
      pp_name n
  | bluerock.lang.cpp.syntax.core.Tptr t' =>
      pp_type t' ++ "*"%pstring
  | bluerock.lang.cpp.syntax.core.Tref t' =>
      pp_type t' ++ "&"%pstring
  | bluerock.lang.cpp.syntax.core.Trv_ref t' =>
      pp_type t' ++ "&&"%pstring
  | bluerock.lang.cpp.syntax.core.Tbool =>
      "bool"%pstring
  | bluerock.lang.cpp.syntax.core.Tvoid =>
      "void"%pstring
  | bluerock.lang.cpp.syntax.core.Tnamed n' =>
      pp_name n'
  | bluerock.lang.cpp.syntax.core.Tenum n' =>
      "enum "%pstring ++ pp_name n'
  | bluerock.lang.cpp.syntax.core.Tunsupported s =>
      s
  | _ =>
      "/*unsupported‐type*/"%pstring
  end

with pp_expr
         (e: bluerock.lang.cpp.syntax.core.Expr) : string :=
  match e with
  | bluerock.lang.cpp.syntax.core.Eparam id =>
      ident_to_string id
  | bluerock.lang.cpp.syntax.core.Eunresolved_unop op e =>
      ru_op_to_string op ++ pp_expr e
  | bluerock.lang.cpp.syntax.core.Eunresolved_binop op e1 e2 =>
      "(" ++ pp_expr e1 ++ rb_op_to_string op ++ pp_expr e2 ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Eunresolved_call f args =>
      pp_name f ++ "(" ++ pp_sep_list "," pp_expr args ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Eunop op e' _ =>
      "(" ++ unop_to_string op ++ pp_expr e' ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Ebinop op e1 e2 _ =>
      "(" ++ pp_expr e1 ++ binop_to_string op ++ pp_expr e2 ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Ecall f args =>
      pp_expr f ++ "(" ++ pp_sep_list "," pp_expr args ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Ecast c e' =>
      "(" ++ pp_cast c ++ ")"%pstring ++ pp_expr e'
  | bluerock.lang.cpp.syntax.core.Eif cond thn els _ =>
      "(" ++ pp_expr cond ++ " ? " ++ pp_expr thn ++ " : " ++ pp_expr els ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Estmt s _ =>
      "(" ++ pp_stmt s ++ ")"%pstring
  | bluerock.lang.cpp.syntax.core.Eunsupported s _ =>
      s
  | _ =>
      "/*unsupported‐expr*/"%pstring
  end

with pp_stmt
         (s: bluerock.lang.cpp.syntax.core.Stmt) : string :=
  match s with
  | bluerock.lang.cpp.syntax.core.Sseq ss =>
      "{ " ++ pp_sep_list "; " pp_stmt ss ++ "}"%pstring
  | bluerock.lang.cpp.syntax.core.Sdecl ds =>
      pp_sep_list "; " pp_vardecl ds ++ ";"%pstring
  | bluerock.lang.cpp.syntax.core.Sif None cond s1 s2 =>
      "if(" ++ pp_expr cond ++ ") " ++ pp_stmt s1 ++ " else " ++ pp_stmt s2
  | bluerock.lang.cpp.syntax.core.Swhile _ cond body =>
      "while(" ++ pp_expr cond ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sfor init cond incr body =>
      "for(" 
      ++ (match init  with None => ""%pstring | Some st => pp_stmt st end)
      ++ ";" 
      ++ (match cond  with None => ""%pstring | Some e => pp_expr e end)
      ++ ";" 
      ++ (match incr with None => ""%pstring | Some e => pp_expr e end)
      ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sdo body cond =>
      "do " ++ pp_stmt body ++ " while(" ++ pp_expr cond ++ ");"%pstring
  | bluerock.lang.cpp.syntax.core.Sreturn None =>
      "return;"%pstring
  | bluerock.lang.cpp.syntax.core.Sreturn (Some e') =>
      "return " ++ pp_expr e' ++ ";"%pstring
  | bluerock.lang.cpp.syntax.core.Sexpr e' =>
      pp_expr e' ++ ";"%pstring
  | bluerock.lang.cpp.syntax.core.Sunsupported s =>
      s ++ ";"%pstring
  | _ =>
      "/*unsupported‐stmt*/"%pstring
  end

with pp_vardecl
         (d: bluerock.lang.cpp.syntax.core.VarDecl) : string :=
  match d with
  | bluerock.lang.cpp.syntax.core.Dvar ln ty init =>
      pp_type ty ++ " " ++ ident_to_string ln
      ++ (match init with None => ""%pstring | Some e => " = " ++ pp_expr e end)
  | bluerock.lang.cpp.syntax.core.Dinit _ n ty init =>
      pp_type ty ++ " " ++ pp_name n
      ++ (match init with None => ""%pstring | Some e => " = " ++ pp_expr e end)
  | _ =>
      "/*unsupported‐vardecl*/"%pstring
  end

with pp_bindingdecl
         (b: bluerock.lang.cpp.syntax.core.BindingDecl) : string :=
  match b with
  | bluerock.lang.cpp.syntax.core.Bvar  ln ty e' =>
      pp_type ty ++ " " ++ ident_to_string ln ++ " = " ++ pp_expr e'
  | bluerock.lang.cpp.syntax.core.Bbind ln ty e' =>
      pp_type ty ++ " " ++ ident_to_string ln ++ " = " ++ pp_expr e'
  end

with pp_cast
         (c: bluerock.lang.cpp.syntax.core.Cast) : string :=
  match c with
  | bluerock.lang.cpp.syntax.core.Cdependent t =>
      pp_type t
  | bluerock.lang.cpp.syntax.core.Cbitcast t
  | bluerock.lang.cpp.syntax.core.Cnoop t
  | bluerock.lang.cpp.syntax.core.Cunsupported _ t =>
      "(" ++ pp_type t ++ ")"%pstring
  | _ =>
      "/*unsupported‐cast*/"%pstring
  end.

