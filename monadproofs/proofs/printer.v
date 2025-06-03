Require Import bluerock.auto.cpp.proof.

(*
bluerock.lang.cpp.syntax.stmt.Stmt is an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
Write a set of mutually recursive pretty-printer functions for all such types.
These Gallina functions should return `PrimString.string`.
 *)

(* we use PrimString.string and its “++” *)
Local Open Scope pstring_scope.

(* helper to join a list of strings with a separator *)
Fixpoint sep_by (sep:PrimString.string) (l:list PrimString.string) : PrimString.string :=
  match l with
  | []    => ""
  | [x]   => x
  | x::xs => x ++ sep ++ sep_by sep xs
  end.

(* Z‐printer from the library *)
Definition pp_Z (z: Z) : PrimString.string :=
  bluerock.lang.cpp.syntax.name_notation.printer.showN.showZ z.

(* bitsize is an inductive enum *)
Definition pp_bitsize (b: bitsize) : PrimString.string :=
  match b with
  | bluerock.prelude.arith.types.bitsize.W8   => "8"
  | bluerock.prelude.arith.types.bitsize.W16  => "16"
  | bluerock.prelude.arith.types.bitsize.W32  => "32"
  | bluerock.prelude.arith.types.bitsize.W64  => "64"
  | bluerock.prelude.arith.types.bitsize.W128 => "128"
  end.

(* implemented stubs *)
Definition pp_ident (id:bluerock.lang.cpp.syntax.preliminary.ident) : PrimString.string := id.

Definition pp_RUnOp (op:bluerock.lang.cpp.syntax.overloadable.RUnOp) : PrimString.string :=
  bluerock.lang.cpp.syntax.pretty.printUO op.

Definition pp_RBinOp (op:bluerock.lang.cpp.syntax.overloadable.RBinOp) : PrimString.string :=
  bluerock.lang.cpp.syntax.pretty.printBO op.

Definition pp_literal_string
  (ls:bluerock.lang.cpp.syntax.literal_string.literal_string.t) : PrimString.string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.

Definition pp_char_type
  (ct:bluerock.lang.cpp.syntax.preliminary.char_type.t) : PrimString.string :=
  match ct with
  | bluerock.lang.cpp.syntax.preliminary.char_type.Cchar  => "char"
  | bluerock.lang.cpp.syntax.preliminary.char_type.Cwchar => "wchar_t"
  | bluerock.lang.cpp.syntax.preliminary.char_type.C8     => "char8_t"
  | bluerock.lang.cpp.syntax.preliminary.char_type.C16    => "char16_t"
  | bluerock.lang.cpp.syntax.preliminary.char_type.C32    => "char32_t"
  end.

Definition pp_int_rank
  (ir:bluerock.lang.cpp.syntax.preliminary.int_rank.t) : PrimString.string :=
  match ir with
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ichar     => "char"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ishort    => "short"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Iint      => "int"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilong     => "long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilonglong => "long long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.I128      => "__int128"
  end.

Definition pp_signed (sg:bluerock.prelude.arith.types.signed) : PrimString.string :=
  match sg with
  | bluerock.prelude.arith.types.Signed   => "signed"
  | bluerock.prelude.arith.types.Unsigned => "unsigned"
  end.

Definition pp_cast_style (cs:bluerock.lang.cpp.syntax.core.cast_style.t) : PrimString.string :=
  match cs with
  | bluerock.lang.cpp.syntax.core.cast_style.functional  => "functional"
  | bluerock.lang.cpp.syntax.core.cast_style.c           => "C-style"
  | bluerock.lang.cpp.syntax.core.cast_style.static      => "static_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.dynamic     => "dynamic_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.reinterpret => "reinterpret_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.const       => "const_cast"
  end.

Definition pp_new_form (nf:bluerock.lang.cpp.syntax.preliminary.new_form.t) : PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating pass_align =>
      if pass_align then "Allocating_align" else "Allocating"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating       =>
      "NonAllocating"
  end.

Definition pp_valcat (vc:bluerock.lang.cpp.syntax.preliminary.ValCat) : PrimString.string :=
  match vc with
  | bluerock.lang.cpp.syntax.preliminary.Lvalue  => "lvalue"
  | bluerock.lang.cpp.syntax.preliminary.Prvalue => "prvalue"
  | bluerock.lang.cpp.syntax.preliminary.Xvalue  => "xvalue"
  end.

Definition pp_AtomicOp (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t) : PrimString.string :=
  ao.

(* alias the library atomic_name_ printer, supplying its implicit [type] argument *)
Definition printAN {A : Set} := bluerock.lang.cpp.syntax.pretty.printAN (type:=A).

Fixpoint
  pp_name          (n:bluerock.lang.cpp.syntax.core.name)          : PrimString.string :=
  match n with
  | bluerock.lang.cpp.syntax.core.Ninst base args =>
      pp_name base ++ "<" ++ sep_by "," (List.map pp_temp_arg args) ++ ">"
  | bluerock.lang.cpp.syntax.core.Nglobal an =>
      printAN pp_type None an
  | bluerock.lang.cpp.syntax.core.Ndependent ty =>
      "dependent<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Nscoped n' an =>
      pp_name n' ++ "::" ++ printAN pp_type None an
  | bluerock.lang.cpp.syntax.core.Nunsupported s =>
      s
  end

with pp_temp_arg
  (ta:bluerock.lang.cpp.syntax.core.temp_arg) : PrimString.string :=
  match ta with
  | bluerock.lang.cpp.syntax.core.Atype ty     => pp_type ty
  | bluerock.lang.cpp.syntax.core.Avalue e      => pp_expr e
  | bluerock.lang.cpp.syntax.core.Apack args    =>
      "pack<" ++ sep_by "," (List.map pp_temp_arg args) ++ ">"
  | bluerock.lang.cpp.syntax.core.Atemplate n   => pp_name n
  | bluerock.lang.cpp.syntax.core.Aunsupported s => s
  end

with pp_type
  (t:bluerock.lang.cpp.syntax.core.type)       : PrimString.string :=
  match t with
  | bluerock.lang.cpp.syntax.core.Tparam id              => pp_ident id
  | bluerock.lang.cpp.syntax.core.Tresult_param id       => "result_param(" ++ pp_ident id ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_global n       => "result_global(" ++ pp_name n ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_unop op t1     => pp_RUnOp op ++ pp_type t1
  | bluerock.lang.cpp.syntax.core.Tresult_binop op l r   =>
      "(" ++ pp_RBinOp op ++ sep_by "," [pp_type l; pp_type r] ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_call n args    =>
      pp_name n ++ "(" ++ sep_by "," (List.map pp_type args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_member_call n r args =>
      pp_name n ++ "[" ++ pp_type r ++ "](" ++ sep_by "," (List.map pp_type args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_parenlist t args =>
      "(" ++ pp_type t ++ ")(" ++ sep_by "," (List.map pp_type args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_member t n      =>
      pp_type t ++ "::" ++ pp_name n
  | bluerock.lang.cpp.syntax.core.Tptr t                  => pp_type t ++ "*"
  | bluerock.lang.cpp.syntax.core.Tref t                  => pp_type t ++ "&"
  | bluerock.lang.cpp.syntax.core.Trv_ref t               => pp_type t ++ "&&"
  | bluerock.lang.cpp.syntax.core.Tnum ir sgn             =>
      pp_int_rank ir ++ " " ++ pp_signed sgn
  | bluerock.lang.cpp.syntax.core.Tchar_ ct               => pp_char_type ct
  | bluerock.lang.cpp.syntax.core.Tvoid                   => "void"
  | bluerock.lang.cpp.syntax.core.Tarray t n              =>
      pp_type t ++ "[" ++ pp_Z (Z.of_N n) ++ "]"
  | bluerock.lang.cpp.syntax.core.Tincomplete_array t     => pp_type t ++ "[]"
  | bluerock.lang.cpp.syntax.core.Tvariable_array t e     => pp_type t ++ "[" ++ pp_expr e ++ "]"
  | bluerock.lang.cpp.syntax.core.Tnamed n                => pp_name n
  | bluerock.lang.cpp.syntax.core.Tenum n                 => "enum " ++ pp_name n
  | bluerock.lang.cpp.syntax.core.Tfunction ft            => "(…)"  (* TOFIXLATER *)
  | bluerock.lang.cpp.syntax.core.Tbool                   => "bool"
  | bluerock.lang.cpp.syntax.core.Tmember_pointer cbase cmem =>
      pp_type cbase ++ "->*" ++ pp_type cmem
  | bluerock.lang.cpp.syntax.core.Tfloat_ f               => "(float-type…)" (* TOFIXLATER *)
  | bluerock.lang.cpp.syntax.core.Tqualified qs t'        => "(qual " ++ "(…)" ++ ")"
  | bluerock.lang.cpp.syntax.core.Tnullptr                => "nullptr_t"
  | bluerock.lang.cpp.syntax.core.Tarch osz nm            =>
      "arch(" ++
        (match osz with
         | None   => ""
         | Some b => pp_bitsize b
         end) ++
      "," ++ nm ++ ")"
  | bluerock.lang.cpp.syntax.core.Tdecltype e             => "decltype(" ++ pp_expr e ++ ")"
  | bluerock.lang.cpp.syntax.core.Texprtype e             => "exprtype(" ++ pp_expr e ++ ")"
  | bluerock.lang.cpp.syntax.core.Tunsupported s          => s
  end

with pp_expr
  (e:bluerock.lang.cpp.syntax.core.Expr) : PrimString.string :=
  match e with
  | bluerock.lang.cpp.syntax.core.Eparam id                => pp_ident id
  | bluerock.lang.cpp.syntax.core.Eunresolved_global n     => pp_name n
  | bluerock.lang.cpp.syntax.core.Eunresolved_unop op x    => pp_RUnOp op ++ pp_expr x
  | bluerock.lang.cpp.syntax.core.Eunresolved_binop op l r =>
      "(" ++ pp_expr l ++ pp_RBinOp op ++ pp_expr r ++ ")"
  | bluerock.lang.cpp.syntax.core.Eunresolved_call n args  =>
      pp_name n ++ "(" ++ sep_by "," (List.map pp_expr args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Eunresolved_member_call n obj args =>
      pp_expr obj ++ "." ++ pp_name n ++ "(" ++ sep_by "," (List.map pp_expr args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Evar ln ty                => "(var " ++ ln ++ ":" ++ pp_type ty ++ ")"
  | bluerock.lang.cpp.syntax.core.Eint z ty                 => pp_Z z ++ ":" ++ pp_type ty
  | bluerock.lang.cpp.syntax.core.Ebool b                   => if b then "true" else "false"
  | bluerock.lang.cpp.syntax.core.Estring ls ty             => pp_literal_string ls ++ ":" ++ pp_type ty
  | bluerock.lang.cpp.syntax.core.Ebinop op a b ty          => "(" ++ pp_expr a ++ " " ++ "(…)" ++ " " ++ pp_expr b ++ ")"
  | bluerock.lang.cpp.syntax.core.Ecall f args             => pp_expr f ++ "(" ++ sep_by "," (List.map pp_expr args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Eexplicit_cast cs ty x    => "(" ++ pp_cast_style cs ++ "<" ++ pp_type ty ++ ">)" ++ pp_expr x
  | bluerock.lang.cpp.syntax.core.Emember arrow obj fld mut ty =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ "(…)"
  | bluerock.lang.cpp.syntax.core.Eif c t e ty              => "if(" ++ pp_expr c ++ ") " ++ pp_expr t ++ " else " ++ pp_expr e
  | bluerock.lang.cpp.syntax.core.Eatomic ao args ty        => pp_AtomicOp ao ++ "(" ++ sep_by "," (List.map pp_expr args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Estmt stm ty              => "(stmt:" ++ pp_stmt stm ++ ")"
  | bluerock.lang.cpp.syntax.core.Eunsupported s _          => s
  | _                                                      => "(…expr case unimplemented…)"
  end

with pp_stmt
  (s:bluerock.lang.cpp.syntax.core.Stmt) : PrimString.string :=
  match s with
  | bluerock.lang.cpp.syntax.core.Sseq ss    => "{ " ++ sep_by "; " (List.map pp_stmt ss) ++ " }"
  | bluerock.lang.cpp.syntax.core.Sdecl dvs  => "decl " ++ sep_by ", " (List.map pp_vardecl dvs)
  | bluerock.lang.cpp.syntax.core.Sif None c t e   => "if(" ++ pp_expr c ++ ") " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | bluerock.lang.cpp.syntax.core.Sif (Some vd) c t e => "if(" ++ pp_vardecl vd ++ "; " ++ pp_expr c ++ ") " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | bluerock.lang.cpp.syntax.core.Swhile o c body     => "while(" ++ (match o with None => "" | Some vd => pp_vardecl vd ++ "; " end) ++ pp_expr c ++ ") " ++ pp_stmt body
  | bluerock.lang.cpp.syntax.core.Sreturn None        => "return;"
  | bluerock.lang.cpp.syntax.core.Sreturn (Some e)    => "return " ++ pp_expr e ++ ";"
  | bluerock.lang.cpp.syntax.core.Sexpr e            => pp_expr e ++ ";"
  | bluerock.lang.cpp.syntax.core.Sunsupported s     => "// unsupported: " ++ s
  | _                                                => "(…stmt case unimplemented…)"
  end

with pp_vardecl
  (vd:bluerock.lang.cpp.syntax.core.VarDecl) : PrimString.string :=
  match vd with
  | bluerock.lang.cpp.syntax.core.Dvar ln ty init    => pp_ident ln ++ ":" ++ pp_type ty ++ (match init with None => "" | Some e => " = " ++ pp_expr e end)
  | bluerock.lang.cpp.syntax.core.Ddecompose e ln bd => "(decomp " ++ pp_expr e ++ " to " ++ ln ++ " and …)"
  | bluerock.lang.cpp.syntax.core.Dinit b ln ty init => "(init " ++ (if b then "thread_safe " else "") ++ pp_name ln ++ ":" ++ pp_type ty ++ (match init with None => "" | Some e => " = " ++ pp_expr e end) ++ ")"
  end

with pp_bindingdecl
  (bd:bluerock.lang.cpp.syntax.core.BindingDecl) : PrimString.string :=
  match bd with
  | bluerock.lang.cpp.syntax.core.Bvar ln ty e  => "(bind-var " ++ ln ++ ":" ++ pp_type ty ++ " = " ++ pp_expr e ++ ")"
  | bluerock.lang.cpp.syntax.core.Bbind ln ty e => "(bind " ++ ln ++ ":" ++ pp_type ty ++ " = " ++ pp_expr e ++ ")"
  end

with pp_cast
  (c:bluerock.lang.cpp.syntax.core.Cast) : PrimString.string :=
  match c with
  | bluerock.lang.cpp.syntax.core.Cdependent ty       => "dep-cast<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Cbitcast ty         => "bitcast<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Clvaluebitcast ty   => "lvalue-bitcast<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Cl2r                 => "l2r"
  | bluerock.lang.cpp.syntax.core.Carray2ptr           => "array2ptr"
  | bluerock.lang.cpp.syntax.core.Cbuiltin2fun ty      => "builtin2fun<" ++ pp_type ty ++ ">"
  | bluerock.lang.cpp.syntax.core.Cunsupported _ ty    => "(unsupported-cast)"
  | _                                                   => "(…cast unimplemented…)"
  end.

