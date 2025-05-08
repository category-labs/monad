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

Require Import PrimString.
Require Import List.
Open Scope pstring_scope.

(* -------------------------------------------------------------------------- *)
(* 1) helper to join a list of PrimString.string with a separator *)
Definition pstring_join (sep: string) (ls: list string) : string :=
  match ls with
  | []    => ""
  | x::xs => fold_left (fun acc y => acc ++ sep ++ y) xs x
  end.

(* -------------------------------------------------------------------------- *)
(* 2) stubs for leaf printers, except Z and N which we now implement. *)

(* ident is just PrimString.string *)
Definition string_of_ident
           (id: bluerock.lang.cpp.syntax.preliminary.ident) : string :=
  id.

(* use existing showZ *)
Definition string_of_Z (z: Z) : string :=
  bluerock.lang.cpp.syntax.name_notation.printer.showN.showZ z.

(* use existing N.to_string *)
Definition string_of_N (n: N) : string :=
  bluerock.prelude.pstring.N.to_string n.

Definition string_of_bitsize (b: bitsize) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_int_rank
           (r: int_rank) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_char_type
           (c: bluerock.lang.cpp.syntax.preliminary.char_type.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_float_type
           (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_unop
           (op: bluerock.lang.cpp.syntax.preliminary.UnOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_binop
           (op: bluerock.lang.cpp.syntax.preliminary.BinOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_runop
           (op: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_rbinop
           (op: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_overloadable
           (op: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_cast_style
           (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_atomic_name
           {A} (a: bluerock.lang.cpp.syntax.core.atomic_name_ A) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_new_form (n: new_form) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_bs (b: bs) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_function_type
           (ft: bluerock.lang.cpp.syntax.core.function_type_ type) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_atomic_op (op: AtomicOp) : string.
Admitted. (* TOFIXLATER *)

Definition pp_switch_branch
           (br: bluerock.lang.cpp.syntax.preliminary.SwitchBranch) : string.
Admitted. (* TOFIXLATER *)

(* -------------------------------------------------------------------------- *)
(* 3) the big mutually‐recursive pretty-printers *)

Fixpoint pp_name   (n: name) : string :=
  match n with
  | Ninst base args =>
      pp_name base ++ "<"
      ++ pstring_join "," (List.map pp_temp_arg args)
      ++ ">"
  | Nglobal an       => string_of_atomic_name an
  | Ndependent t     => "(" ++ pp_type t ++ ")"
  | Nscoped n' an    => pp_name n' ++ "::" ++ string_of_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "(" ++ pstring_join "," (List.map pp_temp_arg args) ++ ")"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id              => string_of_ident id
  | Tresult_param id       => string_of_ident id
  | Tresult_global n       => pp_name n
  | Tresult_unop op t1     => "(" ++ string_of_runop op ++ pp_type t1 ++ ")"
  | Tresult_binop op l r   => "(" ++ pp_type l ++ string_of_rbinop op ++ pp_type r ++ ")"
  | Tresult_call fn args   =>
      pp_name fn ++ "(" ++ pstring_join "," (List.map pp_type args) ++ ")"
  | Tresult_member_call fn t1 args =>
      pp_name fn ++ "[" ++ pp_type t1 ++ "]("
      ++ pstring_join "," (List.map pp_type args) ++ ")"
  | Tresult_parenlist t1 args =>
      "(" ++ pp_type t1 ++ ")" ++ "("
      ++ pstring_join "," (List.map pp_type args) ++ ")"
  | Tresult_member t1 n     => pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                 => pp_type t1 ++ "*"
  | Tref t1                 => pp_type t1 ++ "&"
  | Trv_ref t1              => pp_type t1 ++ "&&"
  | Tnum r sgn              => string_of_int_rank r ++ if sgn then "" else "u"
  | Tchar_ c                => string_of_char_type c
  | Tvoid                   => "void"
  | Tarray t1 n             => pp_type t1 ++ "[" ++ string_of_N n ++ "]"
  | Tincomplete_array t1    => pp_type t1 ++ "[]"
  | Tvariable_array t1 e    => pp_type t1 ++ "[" ++ pp_expr e ++ "]"
  | Tnamed n                => pp_name n
  | Tenum n                 => "enum " ++ pp_name n
  | Tfunction ft            => string_of_function_type ft
  | Tbool                   => "bool"
  | Tmember_pointer t1 t2   => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ f               => string_of_float_type f
  | Tqualified _ t1         => pp_type t1 ++ "(qual)"  (* qualifiers TOFIXLATER *)
  | Tnullptr                => "nullptr_t"
  | Tarch None nm           => "arch:" ++ nm
  | Tarch (Some b) nm       => "arch<" ++ string_of_bitsize b ++ ">:" ++ nm
  | Tdecltype e             => "decltype(" ++ pp_expr e ++ ")"
  | Texprtype e             => "typeof(" ++ pp_expr e ++ ")"
  | Tunsupported s          => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id               => string_of_ident id
  | Eunresolved_global n    => pp_name n
  | Eunresolved_unop op e1  => string_of_runop op ++ pp_expr e1
  | Eunresolved_binop op l r=> pp_expr l ++ string_of_rbinop op ++ pp_expr r
  | Eunresolved_call fn es  =>
      pp_name fn ++ "(" ++ pstring_join "," (List.map pp_expr es) ++ ")"
  | Eunresolved_member_call fn obj es =>
      pp_expr obj ++ "." ++ pp_name fn ++ "("
      ++ pstring_join "," (List.map pp_expr es) ++ ")"
  | Eunresolved_parenlist _ es => "(" ++ pstring_join "," (List.map pp_expr es) ++ ")"
  | Eunresolved_member obj n   => pp_expr obj ++ "." ++ pp_name n
  | Evar ln ty                 => string_of_ident ln ++ ":" ++ pp_type ty
  | Eenum_const n id           => pp_name n ++ "::" ++ string_of_ident id
  | Eglobal n ty               => pp_name n ++ ":" ++ pp_type ty
  | Eglobal_member n ty        => pp_name n ++ ":" ++ pp_type ty
  | Echar c ty                 => string_of_N c
  | Estring _ _                => ""  (* TOFIXLATER *)
  | Eint z _                   => string_of_Z z
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => string_of_unop op ++ pp_expr e1
  | Ebinop op l r _            => pp_expr l ++ string_of_binop op ++ pp_expr r
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign l r _              => pp_expr l ++ " = " ++ pp_expr r
  | Eassign_op op l r _        => pp_expr l ++ string_of_binop op ++ "= " ++ pp_expr r
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand l r                => pp_expr l ++ " && " ++ pp_expr r
  | Eseqor  l r                => pp_expr l ++ " || " ++ pp_expr r
  | Ecomma  l r                => pp_expr l ++ ", " ++ pp_expr r
  | Ecall f args               =>
      pp_expr f ++ "(" ++ pstring_join "," (List.map pp_expr args) ++ ")"
  | Eexplicit_cast st t1 e1    =>
      string_of_cast_style st ++ "<" ++ pp_type t1 ++ ">(" ++ pp_expr e1 ++ ")"
  | Ecast c e1                 => pp_cast c ++ "(" ++ pp_expr e1 ++ ")"
  | Emember arr obj an _ _     =>
      pp_expr obj ++ (if arr then "->" else ".") ++ string_of_atomic_name an
  | Emember_ignore arr p res   =>
      pp_expr p ++ (if arr then "->" else ".") ++ pp_expr res
  | Emember_call arr _ obj args=>
      pp_expr obj ++ (if arr then "->" else ".")
      ++ "(" ++ pstring_join "," (List.map pp_expr args) ++ ")"
  | Eoperator_call op _ args   =>
      string_of_overloadable op ++ "(" ++ pstring_join "," (List.map pp_expr args) ++ ")"
  | Esubscript a i _           => pp_expr a ++ "[" ++ pp_expr i ++ "]"
  | Esizeof targ _             =>
      "sizeof(" ++ (match targ with inl t => pp_type t | inr e => pp_expr e end) ++ ")"
  | Ealignof targ _            =>
      "alignof(" ++ (match targ with inl t => pp_type t | inr e => pp_expr e end) ++ ")"
  | Eoffsetof n id _           =>
      "offsetof(" ++ pp_type n ++ "," ++ string_of_ident id ++ ")"
  | Econstructor n args _      =>
      pp_name n ++ "(" ++ pstring_join "," (List.map pp_expr args) ++ ")"
  | Elambda id caps            =>
      "[" ++ pstring_join "," (List.map pp_expr caps) ++ "]("
      ++ pp_name id ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => "{}"
  | Eif c t f _                => pp_expr c ++ " ? " ++ pp_expr t ++ " : " ++ pp_expr f
  | Eif2 _ _ c thn els _       =>
      "if(" ++ pp_expr c ++ "){" ++ pp_expr thn ++ "}else{" ++ pp_expr els ++ "}"
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist args def _       =>
      "{" ++ pstring_join "," (List.map pp_expr args)
      ++ match def with Some e => ", " ++ pp_expr e | None => "" end ++ "}"
  | Einitlist_union an def _   =>
      "union " ++ string_of_atomic_name an ++ "{"
      ++ match def with Some e => pp_expr e | None => "" end ++ "}"
  | Enew (n,ty0) args _ _ _ _  =>
      "new " ++ pp_name n ++ "<" ++ pp_type ty0 ++ ">("
      ++ pstring_join "," (List.map pp_expr args) ++ ")"
  | Edelete arr fn arg _       =>
      (if arr then "delete[]" else "delete") ++ " "
      ++ pp_name fn ++ "(" ++ pp_expr arg ++ ")"
  | Eandclean a                => pp_expr a
  | Ematerialize_temp e1 _     => "materialize(" ++ pp_expr e1 ++ ")"
  | Eatomic op args _          =>
      "atomic<" ++ string_of_atomic_op op ++ ">("
      ++ pstring_join "," (List.map pp_expr args) ++ ")"
  | Estmt s _                  => "(" ++ pp_stmt s ++ ")"
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor arr _ e1=>
      pp_expr e1 ++ (if arr then "->~" else ".~")
  | Earrayloop_init _ src _ _ init _ =>
      "array_loop_init(" ++ pp_expr src ++ "," ++ pp_expr init ++ ")"
  | Earrayloop_index _ _       => "array_loop_index()"
  | Eopaque_ref _ _            => "opaque_ref"
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : string :=
  let opt {A} (pp: A → string) (o: option A) : string :=
      match o with None => "" | Some x => pp x end in
  match s with
  | Sseq ss          => "{ " ++ pstring_join "; " (List.map pp_stmt ss) ++ " }"
  | Sdecl ds         => "decl " ++ pstring_join ", " (List.map pp_vardecl ds)
  | Sif mv c t e     =>
      "if(" ++ opt pp_vardecl mv ++ pp_expr c ++ ") "
      ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Sif_consteval t e => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile mv c bd   =>
      "while(" ++ opt pp_vardecl mv ++ pp_expr c ++ ") " ++ pp_stmt bd
  | Sfor i c1 c2 bd  =>
      "for(" ++ opt pp_stmt i ++ "; " ++ opt pp_expr c1 ++ "; "
      ++ opt pp_expr c2 ++ ") " ++ pp_stmt bd
  | Sdo bd c         => "do " ++ pp_stmt bd ++ " while(" ++ pp_expr c ++ ")"
  | Sswitch mv c bd  =>
      "switch(" ++ opt pp_vardecl mv ++ pp_expr c ++ ") " ++ pp_stmt bd
  | Scase br         => pp_switch_branch br
  | Sdefault         => "default: ;"
  | Sbreak           => "break;"
  | Scontinue        => "continue;"
  | Sreturn me       =>
      "return" ++ match me with None => ";" | Some e => " " ++ pp_expr e ++ ";" end
  | Sexpr e          => pp_expr e ++ ";"
  | Sattr ids s1     =>
      "[[" ++ pstring_join "," (List.map string_of_ident ids) ++ "]] " ++ pp_stmt s1
  | Sasm s _ _ _ _   => "asm(" ++ s ++ ")"
  | Slabeled id s1   => string_of_ident id ++ ": " ++ pp_stmt s1
  | Sgoto id         => "goto " ++ string_of_ident id ++ ";"
  | Sunsupported s   => s
  end

with pp_vardecl (d: VarDecl) : string :=
  match d with
  | Dvar ln ty init       =>
      string_of_ident ln ++ ":" ++ pp_type ty
      ++ match init with None => "" | Some e => " = " ++ pp_expr e end
  | Ddecompose e _ _      => "decomp(" ++ pp_expr e ++ ")"
  | Dinit _ n ty init     =>
      pp_name n ++ ":" ++ pp_type ty
      ++ match init with None => "" | Some e => " = " ++ pp_expr e end
  end

with pp_bindingdecl (b: BindingDecl) : string :=
  match b with
  | Bvar ln ty e  =>
      string_of_ident ln ++ ":" ++ pp_type ty ++ " = " ++ pp_expr e
  | Bbind ln _ e  =>
      string_of_ident ln ++ " = " ++ pp_expr e
  end

with pp_cast (c: Cast) : string :=
  match c with
  | Cdependent t         => "(depcast<" ++ pp_type t ++ ">)"
  | Cbitcast t           => "(bitcast<" ++ pp_type t ++ ">)"
  | Clvaluebitcast t     => "(lvaluebitcast<" ++ pp_type t ++ ">)"
  | Cl2r                 => "(l2r)"
  | Cl2r_bitcast t       => "(l2r_bitcast<" ++ pp_type t ++ ">)"
  | Cnoop t              => "(noop<" ++ pp_type t ++ ">)"
  | Carray2ptr           => "(array2ptr)"
  | Cfun2ptr             => "(fun2ptr)"
  | Cint2ptr t           => "(int2ptr<" ++ pp_type t ++ ">)"
  | Cptr2int t           => "(ptr2int<" ++ pp_type t ++ ">)"
  | Cptr2bool            => "(ptr2bool)"
  | Cintegral t          => "(integral<" ++ pp_type t ++ ">)"
  | Cint2bool            => "(int2bool)"
  | Cfloat2int _         => "(float2int)"
  | Cint2float _         => "(int2float)"
  | Cfloat t             => "(float<" ++ pp_type t ++ ">)"
  | Cnull2ptr _          => "(null2ptr)"
  | Cnull2memberptr t    => "(null2memberptr<" ++ pp_type t ++ ">)"
  | Cbuiltin2fun t       => "(builtin2fun<" ++ pp_type t ++ ">)"
  | C2void               => "(to_void)"
  | Cctor t              => "(ctor<" ++ pp_type t ++ ">)"
  | Cuser                => "(user_cast)"
  | Cdynamic t           => "(dynamic_cast<" ++ pp_type t ++ ">)"
  | Cderived2base path _ => "(derived2base<" ++ pstring_join "," (List.map pp_type path) ++ ">)"
  | Cbase2derived path _ => "(base2derived<" ++ pstring_join "," (List.map pp_type path) ++ ">)"
  | Cunsupported bs _    => string_of_bs bs
  end.

