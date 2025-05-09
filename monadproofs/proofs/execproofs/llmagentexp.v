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
Module LLMSOLN.
Module CPP_PP.
  Import bluerock.lang.cpp.syntax.core.
  Import bluerock.lang.cpp.syntax.preliminary.
  (* Ensure ++ is PrimString.string‐append, not list‐append or stdpp append *)
  Local Close Scope list_scope.
  Local Close Scope stdpp_scope.
  Open Scope pstring_scope.

  (* ------------------------------------------------------------------ *)
  (* Helper for option printing *)
  Definition pp_option {A} (ppA: A → PrimString.string) (o: option A)
    : PrimString.string :=
    match o with Some x => ppA x | None => "" end.

  (* ------------------------------------------------------------------ *)
  (* List‐printers stubs (TOFIXLATER) *)
  Definition pp_list_name     (l: list name')        : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_list_temp_arg (l: list temp_arg')    : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_list_type     (l: list type')        : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_list_Expr     (l: list Expr')        : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_list_ident    (l: list ident)        : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_list_binding  (l: list BindingDecl') : PrimString.string. Admitted. (* TOFIXLATER *)

  (* ------------------------------------------------------------------ *)
  (* Leaf printers (all TOFIXLATER) *)
  Definition pp_int_rank      (r: int_rank)          : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_signed        (sg: bluerock.prelude.arith.types.signed)
                                          : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_atomic_name {T}(an: atomic_name_ T)  : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_RUnOp         (op: overloadable.RUnOp) : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_RBinOp        (op: overloadable.RBinOp): PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_UnOp          (op: UnOp)            : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_BinOp         (op: BinOp)           : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_function_type(ft: function_type_ type') : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_cast_style    (cs: cast_style.t)    : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_valcat        (vc: ValCat)          : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_operator_impl(oi: operator_impl.t name' type')
                                          : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_overloadable_operator
                            (o: OverloadableOperator): PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_method_ref    (mr: MethodRef_ name' type' Expr')
                                          : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_literal_string
                            (s: literal_string.t)   : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_float_type    (f: float_type.t)     : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_type_qualifiers
                            (q: type_qualifiers)    : PrimString.string. Admitted. (* TOFIXLATER *)
  Definition pp_bitsize       (b: bs)               : PrimString.string. Admitted. (* TOFIXLATER *)

  (* ------------------------------------------------------------------ *)
  Fixpoint pp_name  (n: name')    : PrimString.string :=
    match n with
    | Ninst on args      => pp_name on ++ "<" ++ pp_list_temp_arg args ++ ">"
    | Nglobal an         => pp_atomic_name an
    | Ndependent t       => pp_type t
    | Nscoped n' an      => pp_name n' ++ "::" ++ pp_atomic_name an
    | Nunsupported s     => s
    end

  with pp_temp_arg (ta: temp_arg') : PrimString.string :=
    match ta with
    | Atype t            => pp_type t
    | Avalue e           => pp_Expr e
    | Apack l            => pp_list_temp_arg l
    | Atemplate n        => pp_name n
    | Aunsupported s     => s
    end

  with pp_type     (t: type')      : PrimString.string :=
    match t with
    | Tparam id                => id
    | Tresult_param id         => id
    | Tresult_global on        => pp_name on
    | Tresult_unop op t1       => pp_RUnOp op ++ pp_type t1
    | Tresult_binop op t1 t2   => pp_RBinOp op ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
    | Tresult_call on tys      => pp_name on ++ "(" ++ pp_list_type tys ++ ")"
    | Tresult_member_call on t1 tys =>
        pp_name on ++ "[" ++ pp_type t1 ++ ";" ++ pp_list_type tys ++ "]"
    | Tresult_parenlist t1 ts  =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list_type ts ++ ")"
    | Tresult_member t1 on     => pp_type t1 ++ "::" ++ pp_name on
    | Tptr t1                  => pp_type t1 ++ "*"
    | Tref t1                  => pp_type t1 ++ "&"
    | Trv_ref t1               => pp_type t1 ++ "&&"
    | Tnum r sg                => pp_int_rank r ++ pp_signed sg
    | Tchar_ ct                => "char"
    | Tvoid                    => "void"
    | Tarray t1 n              => pp_type t1 ++ "[" ++ "" ++ "]"    (* TOFIXLATER *)
    | Tincomplete_array t1     => pp_type t1 ++ "[]"
    | Tvariable_array t1 e     => pp_type t1 ++ "[" ++ pp_Expr e ++ "]"
    | Tnamed on                => pp_name on
    | Tenum on                 => "enum " ++ pp_name on
    | Tfunction ft             => pp_function_type ft
    | Tbool                    => "bool"
    | Tmember_pointer t1 t2    => pp_type t1 ++ "::*" ++ pp_type t2
    | Tfloat_ f                => pp_float_type f
    | Tqualified q t1          => pp_type_qualifiers q ++ " " ++ pp_type t1
    | Tnullptr                 => "nullptr_t"
    | Tarch osz nm             => nm
    | Tdecltype e              => "decltype(" ++ pp_Expr e ++ ")"
    | Texprtype e              => "decltype(" ++ pp_Expr e ++ ")"
    | Tunsupported s           => s
    end

  with pp_Expr (e: Expr')        : PrimString.string :=
    match e with
    | Eparam id                        => id
    | Eunresolved_global on            => pp_name on
    | Eunresolved_unop op e1           => pp_RUnOp op ++ pp_Expr e1
    | Eunresolved_binop op l r         => pp_RBinOp op ++ "(" ++ pp_Expr l ++ "," ++ pp_Expr r ++ ")"
    | Eunresolved_call on args         => pp_name on ++ "(" ++ pp_list_Expr args ++ ")"
    | Eunresolved_member_call on obj args =>
        pp_name on ++ "(" ++ pp_Expr obj ++ "," ++ pp_list_Expr args ++ ")"
    | Eunresolved_parenlist optT args  => "(" ++ pp_list_Expr args ++ ")"  (* TOFIXLATER *)
    | Eunresolved_member obj on        => pp_Expr obj ++ "." ++ pp_name on
    | Evar ln ty                       => ln
    | Eenum_const on id                => pp_name on ++ "::" ++ id
    | Eglobal on ty                    => pp_name on
    | Eglobal_member on ty             => pp_name on
    | Echar n ty                       => ""                             (* TOFIXLATER *)
    | Estring s ty                     => pp_literal_string s
    | Eint z ty                        => ""                             (* TOFIXLATER *)
    | Ebool b                          => if b then "true" else "false"
    | Eunop op e1 ty                   => pp_UnOp op ++ pp_Expr e1
    | Ebinop op l r ty                 => pp_BinOp op ++ "(" ++ pp_Expr l ++ "," ++ pp_Expr r ++ ")"
    | Ederef e1 ty                     => "*" ++ pp_Expr e1
    | Eaddrof e1                       => "&" ++ pp_Expr e1
    | Eassign e1 e2 ty                 => pp_Expr e1 ++ " = " ++ pp_Expr e2
    | Eassign_op op e1 e2 ty           => pp_Expr e1 ++ pp_BinOp op ++ pp_Expr e2
    | Epreinc e1 ty                    => "++" ++ pp_Expr e1
    | Epostinc e1 ty                   => pp_Expr e1 ++ "++"
    | Epredec e1 ty                    => "--" ++ pp_Expr e1
    | Epostdec e1 ty                   => pp_Expr e1 ++ "--"
    | Eseqand l r                      => pp_Expr l ++ " && " ++ pp_Expr r
    | Eseqor  l r                      => pp_Expr l ++ " || " ++ pp_Expr r
    | Ecomma  l r                      => pp_Expr l ++ ", " ++ pp_Expr r
    | Ecall f args                     => pp_Expr f ++ "(" ++ pp_list_Expr args ++ ")"
    | Eexplicit_cast cs ty e1          => pp_cast_style cs ++ "<" ++ pp_type ty ++ ">(" ++ pp_Expr e1 ++ ")"
    | Ecast c e1                       => pp_Cast c ++ pp_Expr e1
    | Emember arrow obj an mut ty     => (if arrow then "->" else ".") ++ pp_Expr obj ++ pp_atomic_name an
    | Emember_ignore arrow p q        => ""                             (* TOFIXLATER *)
    | Emember_call arrow mr obj args  => (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list_Expr args ++ ")"
    | Eoperator_call oper impl args   => pp_overloadable_operator oper ++ "(" ++ pp_list_Expr args ++ ")"
    | Esubscript e1 e2 ty             => pp_Expr e1 ++ "[" ++ pp_Expr e2 ++ "]"
    | Esizeof s_e ty                  => "sizeof(" ++ "" ++ ")"         (* TOFIXLATER *)
    | Ealignof s_e ty                 => "alignof(" ++ "" ++ ")"        (* TOFIXLATER *)
    | Eoffsetof t id ty               => "offsetof(" ++ pp_type t ++ "," ++ id ++ ")"
    | Econstructor on args ty         => pp_name on ++ "(" ++ pp_list_Expr args ++ ")"
    | Elambda id captures             => "[capture](" ++ pp_list_Expr captures ++ ")"
    | Eimplicit e1                    => pp_Expr e1
    | Eimplicit_init ty               => pp_type ty ++ "{}"
    | Eif cond thn els ty             => "if(" ++ pp_Expr cond ++ ") " ++ pp_Expr thn ++ " else " ++ pp_Expr els
    | Eif2 n c t e1 e2 ty             => ""                             (* TOFIXLATER *)
    | Ethis ty                        => "this"
    | Enull                           => "nullptr"
    | Einitlist elems def ty         => "{" ++ pp_list_Expr elems ++ (match def with Some d => "," ++ pp_Expr d | None => "" end) ++ "}"
    | Einitlist_union an def ty       => ""                             (* TOFIXlATER *)
    | Enew pr args nf ty init pre     => ""                             (* TOFIXlATER *)
    | Edelete is_arr on e1 ty         => "delete " ++ pp_Expr e1
    | Eandclean e1                    => pp_Expr e1
    | Ematerialize_temp e1 vc        => "materialize(" ++ pp_Expr e1 ++ ")"
    | Eatomic op args ty              => "atomic(" ++ pp_list_Expr args ++ ")"
    | Estmt st ty                     => "(" ++ pp_Stmt st ++ ")"
    | Eva_arg e1 ty                   => pp_Expr e1
    | Epseudo_destructor arr ty e1    => ""                             (* TOFIXLATER *)
    | Earrayloop_init lv src l ln init ty => ""                       (* TOFIXLATER *)
    | Earrayloop_index lv ty          => ""                             (* TOFIXlATER *)
    | Eopaque_ref lv ty               => ""                             (* TOFIXlATER *)
    | Eunsupported s ty               => s
    end

  with pp_Stmt (s: Stmt') : PrimString.string :=
    match s with
    | Sseq ss =>
        "{" ++
        (* local printer for lists of statements *)
        (fix aux (l: list Stmt') : PrimString.string :=
           match l with
           | Datatypes.nil       => ""
           | Datatypes.cons x xs => pp_Stmt x ++ aux xs
           end) ss
        ++ "}"
    | Sdecl ds =>
        (* local printer for lists of VarDecl' *)
        (fix aux (l: list VarDecl') : PrimString.string :=
           match l with
           | Datatypes.nil       => ""
           | Datatypes.cons d ds => pp_VarDecl d ++ aux ds
           end) ds
    | Sif dv c t e => "if(" ++ pp_option pp_VarDecl dv ++ pp_Expr c ++
                      ") " ++ pp_Stmt t ++ " else " ++ pp_Stmt e
    | Sif_consteval t e => "if consteval " ++ pp_Stmt t ++ " else " ++ pp_Stmt e
    | Swhile dv c b     => "while(" ++ pp_option pp_VarDecl dv ++ pp_Expr c ++ ") " ++ pp_Stmt b
    | Sfor i c u b      => "for(" ++ pp_option pp_Stmt i ++ ";" ++ pp_option pp_Expr c ++ ";" ++ pp_option pp_Expr u ++ ") " ++ pp_Stmt b
    | Sdo b c           => "do " ++ pp_Stmt b ++ " while(" ++ pp_Expr c ++ ")"
    | Sswitch dv c b    => "switch(" ++ pp_option pp_VarDecl dv ++ pp_Expr c ++ ") " ++ pp_Stmt b
    | Scase br          => "case " ++ "" ++ ":"    (* TOFIXLATER *)
    | Sdefault          => "default:"
    | Sbreak            => "break;"
    | Scontinue         => "continue;"
    | Sreturn eo        => "return " ++ pp_option pp_Expr eo ++ ";"
    | Sexpr e1          => pp_Expr e1 ++ ";"
    | Sattr attrs b     => "[[" ++ pp_list_ident attrs ++ "]] " ++ pp_Stmt b
    | Sasm s vol inp out clob => "asm(" ++ s ++ ");"  (* TOFIXLATER *)
    | Slabeled id b     => id ++ ": " ++ pp_Stmt b
    | Sgoto lab         => "goto " ++ lab ++ ";"
    | Sunsupported s    => "// unsupported: " ++ s
    end

  with pp_VarDecl (d: VarDecl') : PrimString.string :=
    match d with
    | Dvar ln ty eo       => pp_type ty ++ " " ++ ln ++ pp_option pp_Expr eo ++ ";"
    | Ddecompose e id bs  => ""                        (* TOFIXLATER *)
    | Dinit tsafe on ty eo=> ""                        (* TOFIXLATER *)
    end

  with pp_BindingDecl (b: BindingDecl') : PrimString.string :=
    match b with
    | Bvar ln ty e1 => pp_type ty ++ " " ++ ln ++ " = " ++ pp_Expr e1
    | Bbind ln ty e1=> pp_type ty ++ " " ++ ln ++ " : " ++ pp_Expr e1
    end

  with pp_Cast (c: Cast') : PrimString.string :=
    match c with
    | Cdependent t     => "/*dep*/"
    | Cbitcast t       => "bitcast"
    | Clvaluebitcast t => "lvalue_bit_cast"
    | Cl2r             => "l2r"
    | Cl2r_bitcast t   => "l2r_bit_cast"
    | Cnoop t          => ""
    | Carray2ptr       => "array2ptr"
    | Cfun2ptr         => "fun2ptr"
    | Cint2ptr t       => "int2ptr"
    | Cptr2int t       => "ptr2int"
    | Cptr2bool        => "ptr2bool"
    | Cintegral t      => "integral"
    | Cint2bool        => "int2bool"
    | Cfloat2int t     => "float2int"
    | Cint2float t     => "int2float"
    | Cfloat t         => "float"
    | Cnull2ptr t      => "null2ptr"
    | Cnull2memberptr t=> "null2memberptr"
    | Cbuiltin2fun t   => "builtin2fun"
    | C2void           => "to_void"
    | Cctor t          => "ctor"
    | Cuser            => "user"
    | Cdynamic t       => "dynamic"
    | Cderived2base ps t=> "derived2base"
    | Cbase2derived ps t=> "base2derived"
    | Cunsupported b t => "/*cast?*/"
    end.
End CPP_PP.
End LLMSOLN.

