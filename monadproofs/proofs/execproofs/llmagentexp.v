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
Import bluerock.lang.cpp.syntax.core.
Open Scope pstring.

(* TOFIXLATER: admit a Z → string converter *)
Definition Ztostring (z: Corelib.Numbers.BinNums.Z) : string.
Admitted. (* TOFIXLATER *)

(* join a list of strings with a separator *)
Fixpoint join (sep : string) (l : Corelib.Init.Datatypes.list string) : string :=
  match l with
  | [] => ""%pstring
  | [x] => x
  | x :: xs => x ++ sep ++ join sep xs
  end.

(* ident is just a primitive string *)
Definition pp_ident (id: bluerock.lang.cpp.syntax.preliminary.ident) : string := id.

(* integer‐rank → string *)
Definition pp_int_rank (r: bluerock.lang.cpp.syntax.preliminary.int_rank.t) : string :=
  match r with
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ichar     => "char"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ishort    => "short"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Iint      => "int"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilong     => "long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilonglong => "long long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.I128      => "__int128"
  end.

(* signed → prefix string *)
Definition pp_signed (s: bluerock.prelude.arith.types.signed) : string :=
  match s with
  | bluerock.prelude.arith.types.Signed   => ""%pstring
  | bluerock.prelude.arith.types.Unsigned => "unsigned "%pstring
  end.

(* char_type → string *)
Definition pp_char_type (c: char_type) : string :=
  match c with
  | bluerock.lang.cpp.syntax.preliminary.char_type.Cchar  => "char"
  | bluerock.lang.cpp.syntax.preliminary.char_type.Cwchar => "wchar_t"
  | bluerock.lang.cpp.syntax.preliminary.char_type.C8     => "char8_t"
  | bluerock.lang.cpp.syntax.preliminary.char_type.C16    => "char16_t"
  | bluerock.lang.cpp.syntax.preliminary.char_type.C32    => "char32_t"
  end.

(* float_type → string *)
Definition pp_float_type (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string :=
  match f with
  | bluerock.lang.cpp.syntax.preliminary.float_type.Ffloat16    => "float16"
  | bluerock.lang.cpp.syntax.preliminary.float_type.Ffloat      => "float"
  | bluerock.lang.cpp.syntax.preliminary.float_type.Fdouble     => "double"
  | bluerock.lang.cpp.syntax.preliminary.float_type.Flongdouble => "long double"
  | bluerock.lang.cpp.syntax.preliminary.float_type.Ffloat128   => "__float128"
  end.

(* type_qualifiers → string *)
Definition pp_type_qualifiers
           (q: bluerock.lang.cpp.syntax.preliminary.type_qualifiers) : string :=
  match q with
  | bluerock.lang.cpp.syntax.preliminary.QCV => "const volatile"
  | bluerock.lang.cpp.syntax.preliminary.QC  => "const"
  | bluerock.lang.cpp.syntax.preliminary.QV  => "volatile"
  | bluerock.lang.cpp.syntax.preliminary.QM  => "mutable"
  end.

(* cast_style → string *)
Definition pp_cast_style (cs: core.cast_style.t) : string :=
  match cs with
  | bluerock.lang.cpp.syntax.core.cast_style.functional  => "functional_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.c           => "C_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.static      => "static_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.dynamic     => "dynamic_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.reinterpret => "reinterpret_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.const       => "const_cast"
  end.

(* helper for options *)
Definition option_default {A B}
           (d : B) (f: A → B) (o : Corelib.Init.Datatypes.option A) : B :=
  match o with None => d | Some x => f x end.

(* main mutual pretty‐printer, inlining atomic_name_ and Tfunction *)
Fixpoint pp_name      (n   : name)        : string :=
  match n with
  | Ninst n0 args =>
      pp_name n0 ++ "<" ++ join ", " (List.map pp_temp_arg args) ++ ">"
  | Nglobal an    =>
      match an with
      | Nid id                => id
      | Nfunction _ id ts     => id ++ "<" ++ join ", " (List.map pp_type ts) ++ ">"
      | Nunsupported_atomic s => "unsupported_atomic(" ++ s ++ ")"
      | _                     => "TODO_atomic"
      end
  | Ndependent t  => "dependent(" ++ pp_type t ++ ")"
  | Nscoped n0 an =>
      pp_name n0 ++ "::" ++
      match an with
      | Nid id                => id
      | Nfunction _ id ts     => id ++ "<" ++ join ", " (List.map pp_type ts) ++ ">"
      | Nunsupported_atomic s => "unsupported_atomic(" ++ s ++ ")"
      | _                     => "TODO_atomic"
      end
  | Nunsupported s => "unsupported_name(" ++ s ++ ")"
  end

with pp_temp_arg (a : temp_arg)    : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_Expr e
  | Apack args     => "pack<" ++ join ", " (List.map pp_temp_arg args) ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => "unsupported_targ(" ++ s ++ ")"
  end

with pp_type     (t : type)        : string :=
  match t with
  | Tparam id        => pp_ident id
  | Tresult_param id => pp_ident id
  | Tresult_global n => pp_name n
  | Tptr t'          => pp_type t' ++ "*"
  | Tref t'          => pp_type t' ++ "&"
  | Trv_ref t'       => pp_type t' ++ "&&"
  | Tnum r sgn       => pp_signed sgn ++ pp_int_rank r
  | Tchar_ c         => pp_char_type c
  | Tvoid            => "void"
  | Tqualified q t'  => pp_type_qualifiers q ++ " " ++ pp_type t'
  | Texprtype e      => "decltype(" ++ pp_Expr e ++ ")"
  | Tfunction ft     =>
      let cc_str :=
        match ft_cc ft with
        | bluerock.lang.cpp.syntax.preliminary.CC_C       => "cdecl"
        | bluerock.lang.cpp.syntax.preliminary.CC_MsAbi   => "ms_abi"
        | bluerock.lang.cpp.syntax.preliminary.CC_RegCall => "regcall"
        end in
      let ret := pp_type (ft_return ft) in
      let ps_list := List.map pp_type (ft_params ft) in
      let ps_str0 := join ", " ps_list in
      let ps_str :=
        match ft_arity ft with
        | bluerock.lang.cpp.syntax.preliminary.Ar_Definite => ps_str0
        | bluerock.lang.cpp.syntax.preliminary.Ar_Variadic =>
            match ps_list with
            | [] => "..."
            | _  => ps_str0 ++ ", ..."
            end
        end in
      cc_str ++ " " ++ ret ++ "(" ++ ps_str ++ ")"
  | Tunsupported s   => "unsupported_type(" ++ s ++ ")"
  | _                => "TODO_type"
  end

with pp_Expr     (e : Expr)        : string :=
  match e with
  | Eparam id          => pp_ident id
  | Eunresolved_global n => pp_name n
  | Evar l ty          => pp_ident l ++ ":" ++ pp_type ty
  | Eint z ty          => "(" ++ Ztostring z ++ ":" ++ pp_type ty ++ ")"%pstring
  | Eunop op e1 ty     => "(" ++ "unop" ++ pp_Expr e1 ++ ")"
  | Ebinop op l r ty   => "(" ++ "binop" ++ pp_Expr l ++ "," ++ pp_Expr r ++ ")"
  | Ecall f args       => pp_Expr f ++ "(" ++ join ", " (List.map pp_Expr args) ++ ")"
  | Eexplicit_cast cs ty e1 =>
      pp_cast_style cs ++ "<" ++ pp_type ty ++ ">(" ++ pp_Expr e1 ++ ")"
  | Ecast c e1         => pp_cast c ++ "(" ++ pp_Expr e1 ++ ")"
  | Estmt s _          => "[stmt:" ++ pp_Stmt s ++ "]"
  | Eunsupported s _   => "unsupported_expr(" ++ s ++ ")"
  | _                  => "TODO_expr"
  end

with pp_Stmt     (s : Stmt)        : string :=
  match s with
  | Sseq ss         => "{" ++ join "; " (List.map pp_Stmt ss) ++ "}"
  | Sdecl ds        => "decl{" ++ join ", " (List.map pp_VarDecl ds) ++ "}"
  | Sif od c t f    =>
      "if(" ++ option_default "" pp_VarDecl od ++ pp_Expr c
      ++ ")" ++ pp_Stmt t ++ " else " ++ pp_Stmt f
  | Swhile od c b   =>
      "while(" ++ option_default "" pp_VarDecl od ++ pp_Expr c ++ ")" ++ pp_Stmt b
  | Sreturn oe      => "return " ++ option_default "" pp_Expr oe
  | Sexpr e         => pp_Expr e ++ ";"
  | Sunsupported s  => "unsupported_stmt(" ++ s ++ ")"
  | _               => "TODO_stmt"
  end

with pp_VarDecl  (d : VarDecl)     : string :=
  match d with
  | Dvar l ty oi     =>
      pp_ident l ++ ":" ++ pp_type ty
      ++ option_default "" (fun e => " = " ++ pp_Expr e) oi
  | Dinit _ n ty oi  =>
      pp_name n ++ ":" ++ pp_type ty
      ++ option_default "" (fun e => " = " ++ pp_Expr e) oi
  | _                => "TODO_vardecl"
  end

with pp_BindingDecl (b: BindingDecl) : string :=
  match b with
  | Bvar l ty e    => pp_ident l ++ ":" ++ pp_type ty ++ " = " ++ pp_Expr e
  | Bbind l ty e   => pp_ident l ++ ":" ++ pp_type ty ++ " <- " ++ pp_Expr e
  end

with pp_cast (c : Cast) : string :=
  match c with
  | Cdependent t      => "cast_dep(" ++ pp_type t ++ ")"
  | Cbitcast t        => "bitcast(" ++ pp_type t ++ ")"
  | Clvaluebitcast t  => "lvalue_bitcast(" ++ pp_type t ++ ")"
  | Cl2r              => "l2r"
  | Cl2r_bitcast t    => "l2r_bitcast(" ++ pp_type t ++ ")"
  | Cnoop t           => "noop(" ++ pp_type t ++ ")"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr(" ++ pp_type t ++ ")"
  | Cptr2int t        => "ptr2int(" ++ pp_type t ++ ")"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "integral(" ++ pp_type t ++ ")"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int(" ++ pp_type t ++ ")"
  | Cint2float t      => "int2float(" ++ pp_type t ++ ")"
  | Cfloat t          => "float(" ++ pp_type t ++ ")"
  | Cnull2ptr t       => "null2ptr(" ++ pp_type t ++ ")"
  | Cnull2memberptr t => "null2memberptr(" ++ pp_type t ++ ")"
  | Cbuiltin2fun t    => "builtin2fun(" ++ pp_type t ++ ")"
  | C2void            => "to_void"
  | Cctor t           => "ctor(" ++ pp_type t ++ ")"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic(" ++ pp_type t ++ ")"
  | Cderived2base ps t => "derived2base(" ++ join "," (List.map pp_type ps) ++ ";" ++ pp_type t ++ ")"
  | Cbase2derived ps t => "base2derived(" ++ join "," (List.map pp_type ps) ++ ";" ++ pp_type t ++ ")"
  | Cunsupported _ _  => "unsupported_cast"
  end.










