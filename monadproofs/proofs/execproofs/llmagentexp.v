Require Import bluerock.auto.invariants.
Set Printing FullyQualifiedNames.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Disable Notation atomic_name.
Open Scope pstring_scope.

(*
bluerock.lang.cpp.syntax.stmt.Stmt is an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
Write a set of mutually recursive pretty-printer functions for all such types.
These Gallina functions should return `PrimString.string`.
*)
Open Scope pstring_scope.

(* Existing library conversions *)
Definition Ztostring (z: Z) : string :=
  bluerock.lang.cpp.syntax.name_notation.printer.showN.showZ z.

Definition Ntostring (n: Corelib.Numbers.BinNums.N) : string :=
  bluerock.prelude.pstring.N.to_string n.

(* Pretty‐print function qualifiers *)
Definition pp_fqual
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string :=
  match q with
  | bluerock.lang.cpp.syntax.core.function_qualifiers.N    => ""
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Nl   => "&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Nr   => "&&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Nc   => "const"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Ncl  => "const&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Ncr  => "const&&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Nv   => "volatile"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Nvl  => "volatile&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Nvr  => "volatile&&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Ncv  => "const volatile"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Ncvl => "const volatile&"
  | bluerock.lang.cpp.syntax.core.function_qualifiers.Ncvr => "const volatile&&"
  end.

(* Pretty‐print overloadable operators *)
Definition pp_overop
  (o: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : string :=
  match o with
  | bluerock.lang.cpp.syntax.preliminary.OOTilde               => "~"
  | bluerock.lang.cpp.syntax.preliminary.OOExclaim             => "!"
  | bluerock.lang.cpp.syntax.preliminary.OOPlusPlus            => "++"
  | bluerock.lang.cpp.syntax.preliminary.OOMinusMinus          => "--"
  | bluerock.lang.cpp.syntax.preliminary.OOStar                => "*"
  | bluerock.lang.cpp.syntax.preliminary.OOPlus                => "+"
  | bluerock.lang.cpp.syntax.preliminary.OOMinus               => "-"
  | bluerock.lang.cpp.syntax.preliminary.OOSlash               => "/"
  | bluerock.lang.cpp.syntax.preliminary.OOPercent             => "%"
  | bluerock.lang.cpp.syntax.preliminary.OOCaret               => "^"
  | bluerock.lang.cpp.syntax.preliminary.OOAmp                 => "&"
  | bluerock.lang.cpp.syntax.preliminary.OOPipe                => "|"
  | bluerock.lang.cpp.syntax.preliminary.OOEqual               => "="
  | bluerock.lang.cpp.syntax.preliminary.OOLessLess            => "<<"
  | bluerock.lang.cpp.syntax.preliminary.OOGreaterGreater      => ">>"
  | bluerock.lang.cpp.syntax.preliminary.OOPlusEqual           => "+="
  | bluerock.lang.cpp.syntax.preliminary.OOMinusEqual          => "-="
  | bluerock.lang.cpp.syntax.preliminary.OOStarEqual           => "*="
  | bluerock.lang.cpp.syntax.preliminary.OOSlashEqual          => "/="
  | bluerock.lang.cpp.syntax.preliminary.OOPercentEqual        => "%="
  | bluerock.lang.cpp.syntax.preliminary.OOCaretEqual          => "^="
  | bluerock.lang.cpp.syntax.preliminary.OOAmpEqual            => "&="
  | bluerock.lang.cpp.syntax.preliminary.OOPipeEqual           => "|="
  | bluerock.lang.cpp.syntax.preliminary.OOLessLessEqual       => "<<="
  | bluerock.lang.cpp.syntax.preliminary.OOGreaterGreaterEqual => ">>="
  | bluerock.lang.cpp.syntax.preliminary.OOEqualEqual          => "=="
  | bluerock.lang.cpp.syntax.preliminary.OOExclaimEqual        => "!="
  | bluerock.lang.cpp.syntax.preliminary.OOLess                => "<"
  | bluerock.lang.cpp.syntax.preliminary.OOGreater             => ">"
  | bluerock.lang.cpp.syntax.preliminary.OOLessEqual           => "<="
  | bluerock.lang.cpp.syntax.preliminary.OOGreaterEqual        => ">="
  | bluerock.lang.cpp.syntax.preliminary.OOSpaceship           => "<=>"
  | bluerock.lang.cpp.syntax.preliminary.OOComma               => ","
  | bluerock.lang.cpp.syntax.preliminary.OOArrowStar           => "->*"
  | bluerock.lang.cpp.syntax.preliminary.OOArrow               => "->"
  | bluerock.lang.cpp.syntax.preliminary.OOSubscript           => "[]"
  | bluerock.lang.cpp.syntax.preliminary.OOAmpAmp             => "&&"
  | bluerock.lang.cpp.syntax.preliminary.OOPipePipe           => "||"
  | bluerock.lang.cpp.syntax.preliminary.OONew arr             =>
      "operator new" ++ if arr then "[]" else ""
  | bluerock.lang.cpp.syntax.preliminary.OODelete arr          =>
      "operator delete" ++ if arr then "[]" else ""
  | bluerock.lang.cpp.syntax.preliminary.OOCall                => "operator()"
  | bluerock.lang.cpp.syntax.preliminary.OOCoawait             => "co_await"
  end.

(* Pretty‐print plain BinOp *)
Definition pp_binop
  (b: bluerock.lang.cpp.syntax.preliminary.BinOp) : string :=
  match b with
  | bluerock.lang.cpp.syntax.preliminary.Badd       => "+"
  | bluerock.lang.cpp.syntax.preliminary.Bsub       => "-"
  | bluerock.lang.cpp.syntax.preliminary.Bmul       => "*"
  | bluerock.lang.cpp.syntax.preliminary.Bdiv       => "/"
  | bluerock.lang.cpp.syntax.preliminary.Bmod       => "%"
  | bluerock.lang.cpp.syntax.preliminary.Bshl       => "<<"
  | bluerock.lang.cpp.syntax.preliminary.Bshr       => ">>"
  | bluerock.lang.cpp.syntax.preliminary.Band       => "&"
  | bluerock.lang.cpp.syntax.preliminary.Bor        => "|"
  | bluerock.lang.cpp.syntax.preliminary.Bxor       => "^"
  | bluerock.lang.cpp.syntax.preliminary.Beq        => "=="
  | bluerock.lang.cpp.syntax.preliminary.Bneq       => "!="
  | bluerock.lang.cpp.syntax.preliminary.Blt        => "<"
  | bluerock.lang.cpp.syntax.preliminary.Bgt        => ">"
  | bluerock.lang.cpp.syntax.preliminary.Ble        => "<="
  | bluerock.lang.cpp.syntax.preliminary.Bge        => ">="
  | bluerock.lang.cpp.syntax.preliminary.Bcmp       => "<=>"
  | bluerock.lang.cpp.syntax.preliminary.Bdotp      => ".*"
  | bluerock.lang.cpp.syntax.preliminary.Bdotip     => "->*"
  | bluerock.lang.cpp.syntax.preliminary.Bunsupported s => s
  end.

(* Pretty‐print RBinOp *)
Definition pp_rbinop
  (r: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string :=
  match r with
  | bluerock.lang.cpp.syntax.overloadable.Rbinop op     => pp_binop op
  | bluerock.lang.cpp.syntax.overloadable.Rassign       => "="
  | bluerock.lang.cpp.syntax.overloadable.Rassign_op op => pp_binop op ++ "="
  | bluerock.lang.cpp.syntax.overloadable.Rsubscript    => "[]"
  end.

(* join a list of strings with a separator *)
Fixpoint join (sep: string) (ss: list string) : string :=
  match ss with
  | []     => ""%pstring
  | [x]    => x
  | x :: xs => x ++ sep ++ join sep xs
  end.

(* The top‐two printers now complete: *)
Fixpoint pp_name
         (n: bluerock.lang.cpp.syntax.core.name')
       : string :=
  match n with
  | bluerock.lang.cpp.syntax.core.Ninst base args =>
      pp_name base ++ "<" ++ join ", " (List.map pp_temp_arg args) ++ ">"
  | bluerock.lang.cpp.syntax.core.Nglobal nm =>
      match nm with
      | bluerock.lang.cpp.syntax.core.Nid id => id
      | bluerock.lang.cpp.syntax.core.Nfunction q id tys =>
          pp_fqual q ++ id ++ "(" ++ join ", " (List.map pp_type tys) ++ ")"
      | bluerock.lang.cpp.syntax.core.Nctor tys =>
          "ctor(" ++ join ", " (List.map pp_type tys) ++ ")"
      | bluerock.lang.cpp.syntax.core.Ndtor => "dtor"
      | bluerock.lang.cpp.syntax.core.Nop q op tys =>
          pp_fqual q ++ pp_overop op ++ "(" ++ join ", " (List.map pp_type tys) ++ ")"
      | bluerock.lang.cpp.syntax.core.Nop_conv q t =>
          pp_fqual q ++ "conv<" ++ pp_type t ++ ">"
      | bluerock.lang.cpp.syntax.core.Nop_lit id tys =>
          id ++ "(" ++ join ", " (List.map pp_type tys) ++ ")"
      | bluerock.lang.cpp.syntax.core.Nanon m => "anon" ++ Ntostring m
      | bluerock.lang.cpp.syntax.core.Nanonymous => "anonymous"
      | bluerock.lang.cpp.syntax.core.Nfirst_decl id => id
      | bluerock.lang.cpp.syntax.core.Nfirst_child id => id
      | bluerock.lang.cpp.syntax.core.Nunsupported_atomic s => s
      end
  | bluerock.lang.cpp.syntax.core.Ndependent t =>
      "(" ++ pp_type t ++ ")"
  | bluerock.lang.cpp.syntax.core.Nscoped base sel =>
      pp_name base ++ "::" ++
      (match sel with
       | bluerock.lang.cpp.syntax.core.Nid id => id
       | bluerock.lang.cpp.syntax.core.Nfunction q id tys =>
           pp_fqual q ++ id ++ "(" ++ join ", " (List.map pp_type tys) ++ ")"
       | bluerock.lang.cpp.syntax.core.Nctor tys =>
           "ctor(" ++ join ", " (List.map pp_type tys) ++ ")"
       | bluerock.lang.cpp.syntax.core.Ndtor => "dtor"
       | bluerock.lang.cpp.syntax.core.Nop q op tys =>
           pp_fqual q ++ pp_overop op ++ "(" ++ join ", " (List.map pp_type tys) ++ ")"
       | bluerock.lang.cpp.syntax.core.Nop_conv q t =>
           pp_fqual q ++ "conv<" ++ pp_type t ++ ">"
       | bluerock.lang.cpp.syntax.core.Nop_lit id tys =>
           id ++ "(" ++ join ", " (List.map pp_type tys) ++ ")"
       | bluerock.lang.cpp.syntax.core.Nanon m => "anon" ++ Ntostring m
       | bluerock.lang.cpp.syntax.core.Nanonymous => "anonymous"
       | bluerock.lang.cpp.syntax.core.Nfirst_decl id => id
       | bluerock.lang.cpp.syntax.core.Nfirst_child id => id
       | bluerock.lang.cpp.syntax.core.Nunsupported_atomic s => s
       end)
  | bluerock.lang.cpp.syntax.core.Nunsupported s => s
  end

with pp_temp_arg
         (ta: bluerock.lang.cpp.syntax.core.temp_arg')
       : string :=
  match ta with
  | bluerock.lang.cpp.syntax.core.Atype t => pp_type t
  | bluerock.lang.cpp.syntax.core.Avalue e => pp_expr e
  | bluerock.lang.cpp.syntax.core.Apack tas =>
      "pack<" ++ join ", " (List.map pp_temp_arg tas) ++ ">"
  | bluerock.lang.cpp.syntax.core.Atemplate nm => pp_name nm
  | bluerock.lang.cpp.syntax.core.Aunsupported s => s
  end

with pp_type
         (t: bluerock.lang.cpp.syntax.core.type')
       : string := ""%pstring          (* TOFIXLATER *)

with pp_expr
         (e: bluerock.lang.cpp.syntax.core.Expr')
       : string := ""%pstring          (* TOFIXLATER *)

with pp_stmt
         (s: bluerock.lang.cpp.syntax.core.Stmt')
       : string := ""%pstring          (* TOFIXLATER *)

with pp_vardecl
         (d: bluerock.lang.cpp.syntax.core.VarDecl')
       : string := ""%pstring          (* TOFIXLATER *)

with pp_bindingdecl
         (bd: bluerock.lang.cpp.syntax.core.BindingDecl')
       : string := ""%pstring          (* TOFIXLATER *)

with pp_cast
         (c: bluerock.lang.cpp.syntax.core.Cast')
       : string := ""%pstring.         (* TOFIXLATER *)


