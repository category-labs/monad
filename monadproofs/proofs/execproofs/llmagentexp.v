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

Local Open Scope pstring.

(* ------------------------------------------------------------------ *)
(* single‐char double‐quote for pstring *)
Definition dq : string := """".

(* ------------------------------------------------------------------ *)
(* transparent list‐printer for structural recursion *)
Fixpoint print_list {A : Type} (sep : string) (f : A → string) (l : list A) : string :=
  match l with
  | [] => ""
  | x :: xs =>
      let rest := match xs with
                  | [] => ""
                  | _  => sep ++ print_list sep f xs
                  end in
      f x ++ rest
  end.

(* ------------------------------------------------------------------ *)
(* still to implement *)
Definition print_name (n : name) : string. Admitted.        (* TOFIXLATER *)
Definition print_type (t : type) : string. Admitted.        (* TOFIXLATER *)
Definition print_expr (e : Expr) : string. Admitted.        (* TOFIXLATER *)

(* ------------------------------------------------------------------ *)
(* function-qualifiers printer *)
Definition print_fq (fq : function_qualifiers.t) : string :=
  match fq with
  | function_qualifiers.N    => ""
  | function_qualifiers.Nl   => "&"
  | function_qualifiers.Nr   => "&&"
  | function_qualifiers.Nc   => " const"
  | function_qualifiers.Ncl  => " const&"
  | function_qualifiers.Ncr  => " const&&"
  | function_qualifiers.Nv   => " volatile"
  | function_qualifiers.Nvl  => " volatile&"
  | function_qualifiers.Nvr  => " volatile&&"
  | function_qualifiers.Ncv  => " const volatile"
  | function_qualifiers.Ncvl => " const volatile&"
  | function_qualifiers.Ncvr => " const volatile&&"
  end.

(* ------------------------------------------------------------------ *)
(* OverloadableOperator printer *)
Definition print_oo (o : OverloadableOperator) : string :=
  match o with
  | OOTilde               => "~"
  | OOExclaim             => "!"
  | OOPlusPlus            => "++"
  | OOMinusMinus          => "--"
  | OOStar                => "*"
  | OOPlus                => "+"
  | OOMinus               => "-"
  | OOSlash               => "/"
  | OOPercent             => "%"
  | OOCaret               => "^"
  | OOAmp                 => "&"
  | OOPipe                => "|"
  | OOEqual               => "="
  | OOLessLess            => "<<"
  | OOGreaterGreater      => ">>"
  | OOPlusEqual           => "+="
  | OOMinusEqual          => "-="
  | OOStarEqual           => "*="
  | OOSlashEqual          => "/="
  | OOPercentEqual        => "%="
  | OOCaretEqual          => "^="
  | OOAmpEqual            => "&="
  | OOPipeEqual           => "|="
  | OOLessLessEqual       => "<<="
  | OOGreaterGreaterEqual => ">>="
  | OOEqualEqual          => "=="
  | OOExclaimEqual        => "!="
  | OOLess                => "<"
  | OOGreater             => ">"
  | OOLessEqual           => "<="
  | OOGreaterEqual        => ">="
  | OOSpaceship           => "<=>"
  | OOComma               => ","
  | OOArrowStar           => "->*"
  | OOArrow               => "->"
  | OOSubscript           => "[]"
  | OOAmpAmp              => "&&"
  | OOPipePipe            => "||"
  | OONew array           => if array then "new[]" else "new"
  | OODelete array        => if array then "delete[]" else "delete"
  | OOCall                => "()"
  | OOCoawait             => "co_await"
  end.

(* ------------------------------------------------------------------ *)
(* SwitchBranch printer *)
Definition print_switch_branch (sb : SwitchBranch) : string :=
  match sb with
  | Exact z     => printer.showN.showZ z
  | Range z1 z2 => printer.showN.showZ z1 ++ "..." ++ printer.showN.showZ z2
  end.

(* ------------------------------------------------------------------ *)
(* BindingDecl printer *)
Definition print_binding_decl (b : BindingDecl) : string :=
  match b with
  | Bvar id ty e =>
      print_type ty ++ " " ++ id ++ " = " ++ print_expr e
  | Bbind id ty e =>
      "(" ++ id ++ " : " ++ print_type ty ++ ") = " ++ print_expr e
  end.

(* ------------------------------------------------------------------ *)
(* temp_arg printer *)
Fixpoint print_temp_arg (a : temp_arg) : string :=
  match a with
  | Atype t        => print_type t
  | Avalue e       => print_expr e
  | Apack args     => "pack<" ++ print_list "," print_temp_arg args ++ ">"
  | Atemplate nm   => print_name nm
  | Aunsupported s => s
  end.

(* ------------------------------------------------------------------ *)
(* VarDecl printer *)
Definition print_var_decl (d : VarDecl) : string :=
  match d with
  | Dvar id ty None =>
      print_type ty ++ " " ++ id
  | Dvar id ty (Some e) =>
      print_type ty ++ " " ++ id ++ " = " ++ print_expr e
  | Ddecompose e id binds =>
      print_expr e ++ " = " ++ id ++ " unpack {"
      ++ print_list "," print_binding_decl binds ++ "}"
  | Dinit thread_safe nm ty None =>
      (if thread_safe then "/*ts*/ " else "")
      ++ print_name nm ++ " " ++ print_type ty
  | Dinit thread_safe nm ty (Some e) =>
      (if thread_safe then "/*ts*/ " else "")
      ++ print_name nm ++ " " ++ print_type ty ++ " = " ++ print_expr e
  end.

(* ------------------------------------------------------------------ *)
(* inline asm printer *)
Definition print_asm
           (body : string)
           (vol : bool)
           (ins outs : list (ident * Expr))
           (clob : list ident)
         : string :=
  "asm " ++ (if vol then "volatile " else "") ++ "("
    ++ dq ++ body ++ dq ++ ":"
    ++ print_list ","
         (fun '(id,e) => dq ++ id ++ dq ++ "(" ++ print_expr e ++ ")")
         outs
    ++ ":"
    ++ print_list ","
         (fun '(id,e) => dq ++ id ++ dq ++ "(" ++ print_expr e ++ ")")
         ins
    ++ ":"
    ++ print_list ","
         (fun id => dq ++ id ++ dq)
         clob
    ++ ");".

(* ------------------------------------------------------------------ *)
(* now fully implemented: Cast printer *)
Definition print_cast (c : Cast) : string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ print_type t ++ ">"
  | Cbitcast t         => "bitcast<" ++ print_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bitcast<" ++ print_type t ++ ">"
  | Cl2r               => "l2r"
  | Cl2r_bitcast t     => "l2r_bitcast<" ++ print_type t ++ ">"
  | Cnoop t            => "noop<" ++ print_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ print_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ print_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "integral<" ++ print_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ print_type t ++ ">"
  | Cint2float t       => "int2float<" ++ print_type t ++ ">"
  | Cfloat t           => "float<" ++ print_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ print_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ print_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ print_type t ++ ">"
  | C2void             => "to_void"
  | Cctor t            => "ctor_conv<" ++ print_type t ++ ">"
  | Cuser              => "user_conv"
  | Cdynamic t         => "dynamic_cast<" ++ print_type t ++ ">"
  | Cderived2base ps t => "derived2base<"
                            ++ print_list "," print_type ps ++ "," ++ print_type t ++ ">"
  | Cbase2derived ps t => "base2derived<"
                            ++ print_list "," print_type ps ++ "," ++ print_type t ++ ">"
  | Cunsupported _ _   => "unsupported_cast"
  end.

(* ------------------------------------------------------------------ *)
(* the main Stmt printer *)
Fixpoint print_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss     => "(" ++ print_list ";" print_stmt ss ++ ")"
  | Sdecl ds    => print_list ";" print_var_decl ds ++ ";"
  | Sif od e t f =>
      let cs := match od with
                | None   => print_expr e
                | Some d => print_var_decl d ++ "; " ++ print_expr e
                end in
      "if(" ++ cs ++ ")" ++ print_stmt t ++ "else" ++ print_stmt f
  | Sif_consteval t f =>
      "__builtin_consteval ? " ++ print_stmt t ++ " : " ++ print_stmt f
  | Swhile od e body =>
      let cs := match od with
                | None   => print_expr e
                | Some d => print_var_decl d ++ "; " ++ print_expr e
                end in
      "while(" ++ cs ++ ")" ++ print_stmt body
  | Sfor o1 o2 o3 body =>
      let i := match o1 with Some st => print_stmt st | None => "" end in
      let c := match o2 with Some e  => print_expr e  | None => "" end in
      let p := match o3 with Some e  => print_expr e  | None => "" end in
      "for(" ++ i ++ "; " ++ c ++ "; " ++ p ++ ")" ++ print_stmt body
  | Sdo body e   => "do" ++ print_stmt body ++ "while(" ++ print_expr e ++ ");"
  | Sswitch od e b =>
      let cs := match od with
                | None   => print_expr e
                | Some d => print_var_decl d ++ "; " ++ print_expr e
                end in
      "switch(" ++ cs ++ ")" ++ print_stmt b
  | Scase sb     => "case " ++ print_switch_branch sb ++ ":"
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn oe   =>
      "return" ++ match oe with Some e => " " ++ print_expr e | None => "" end ++ ";"
  | Sexpr e      => print_expr e ++ ";"
  | Sattr as_ st => print_list " " (fun id => id) as_ ++ " " ++ print_stmt st
  | Sasm b v i o cl => print_asm b v i o cl
  | Slabeled id st   => id ++ ":" ++ print_stmt st
  | Sgoto id         => "goto " ++ id ++ ";"
  | Sunsupported s   => s
  end.

