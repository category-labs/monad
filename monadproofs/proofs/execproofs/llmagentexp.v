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
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A → Corelib.Strings.PrimString.string)
           (l: list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go rest acc :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* low-level conversions *)
Definition pp_int (z: Z) : string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: N) : string. Admitted.        (* TOFIXLATER *)

(* pretty-printing integer ranks *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string :=
  match r with
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ichar     => "char"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ishort    => "short"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Iint      => "int"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilong     => "long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilonglong => "long long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.I128      => "__int128"
  end.

(* pretty-printing architecture bit-sizes *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string :=
  match b with
  | bitsize.W8   => "8"
  | bitsize.W16  => "16"
  | bitsize.W32  => "32"
  | bitsize.W64  => "64"
  | bitsize.W128 => "128"
  end.

(* other stubs *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp) : string. Admitted.
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string. Admitted.
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted.
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp) : string. Admitted.
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string. Admitted.
Definition pp_atomic_name {T} (a: bluerock.lang.cpp.syntax.core.atomic_name_ T) : string. Admitted.
Definition pp_function_qualifiers (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string. Admitted.
Definition pp_method_ref (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr) : string. Admitted.
Definition pp_operator_impl (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type) : string. Admitted.
Definition pp_overloadable_op (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string. Admitted.
Definition pp_float_type (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string. Admitted.

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t) : string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t) : string := ao.

Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst base args  => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      => pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                  => ln
  | Eenum_const n id           => pp_name n ++ "::" ++ id
  | Eglobal n _                => pp_name n
  | Eglobal_member n _         => pp_name n
  | Echar c _                  => pp_int (Z.of_N c)
  | Estring s _                => pp_literal_string s
  | Eint n _                   => pp_int n
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                 => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1                => pp_expr e1
  | Eimplicit_init _            => ""
  | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                     => "this"
  | Enull                       => "nullptr"
  | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _    => pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                 => pp_expr e
  | Ematerialize_temp e1 _      => pp_expr e1
  | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                   => pp_stmt s
  | Eva_arg e1 _                => pp_expr e1
  | Epseudo_destructor _ _ e1   => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ => pp_expr src
  | Earrayloop_index lvl _      => pp_N lvl
  | Eopaque_ref lvl _           => pp_N lvl
  | Eunsupported s _            => s
  end

with pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br            => "case ...: " ++ ""   (* TOFIXLATER *)
  | Sdefault            => "default:"
  | Sbreak              => "break;"
  | Scontinue           => "continue;"
  | Sreturn None        => "return;"
  | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0            => pp_expr e0 ++ ";"
  | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _     => "asm " ++ s0         (* TOFIXLATER *)
  | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
  | Sgoto id            => "goto " ++ id ++ ";"
  | Sunsupported s0     => s0
  end

with pp_vardecl (d: VarDecl) : string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : string :=
  match c with
  | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r              => "l2r"                    (* TOFIXLATER *)
  | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
  | C2void            => "c2void"                 (* TOFIXLATER *)
  | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _ => "derived2base"           (* TOFIXLATER *)
  | Cbase2derived _ _ => "base2derived"           (* TOFIXLATER *)
  | Cunsupported _ _  => "unsupported_cast"
  end.


