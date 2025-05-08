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

From Coq Require Import
  ZArith
  Numbers.BinNums
  Strings.PrimString
  Lists.List.
Import ListNotations.
Open Scope pstring_scope.

(* low‐level stub: numeric printing; still TOFIXLATER *)
Definition Z_to_string (z:Z) : string. Admitted. (* TOFIXLATER *)

(* now implemented “root” stubs *)
Definition N_to_string (n:N) : string :=
  Z_to_string (Z.of_N n).

Definition bool_to_string (b:bool) : string :=
  if b then "true" else "false".

(* quote a PrimString.string *)
Definition pp_pstring (s:string) : string := """" ++ s ++ """".

(* identifier and literal‐string printers *)
Definition pp_ident (id: bluerock.lang.cpp.syntax.preliminary.ident) : string := id.
Definition pp_literal_string
           (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string :=
  """" ++ bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls ++ """".

(* generic list‐printer *)
Definition pp_list {A:Type} (sep:string) (ppA:A→string) (l:list A) : string :=
  match l with
  | [] => ""
  | x::xs => fold_left (fun acc y => acc ++ sep ++ ppA y) xs (ppA x)
  end.

(* print a switch‐case label or range *)
Definition pp_SwitchBranch
           (sb: bluerock.lang.cpp.syntax.preliminary.SwitchBranch) : string :=
  match sb with
  | bluerock.lang.cpp.syntax.preliminary.Exact z =>
      Z_to_string z
  | bluerock.lang.cpp.syntax.preliminary.Range z1 z2 =>
      Z_to_string z1 ++ ".." ++ Z_to_string z2
  end.

(* stubs for all the other atomic pieces *)
Definition pp_atomic_name {T}
           (a: bluerock.lang.cpp.syntax.core.atomic_name_ T) : string. Admitted. (* TOFIXLATER *)
Definition pp_RUnOp   (op: bluerock.lang.cpp.syntax.overloadable.RUnOp)    : string. Admitted. (* TOFIXLATER *)
Definition pp_RBinOp  (op: bluerock.lang.cpp.syntax.overloadable.RBinOp)   : string. Admitted. (* TOFIXLATER *)
Definition pp_UnOp    (op: bluerock.lang.cpp.syntax.preliminary.UnOp)      : string. Admitted. (* TOFIXLATER *)
Definition pp_BinOp   (op: bluerock.lang.cpp.syntax.preliminary.BinOp)     : string. Admitted. (* TOFIXLATER *)
Definition pp_op_impl {N T}
           (impl: bluerock.lang.cpp.syntax.preliminary.operator_impl.t N T) : string. Admitted. (* TOFIXLATER *)
Definition pp_OvlOp   (op: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string. Admitted. (* TOFIXLATER *)
Definition pp_cast_style
           (cs: bluerock.lang.cpp.syntax.core.cast_style.t)             : string. Admitted. (* TOFIXLATER *)
Definition pp_new_form (nf:new_form)                                   : string. Admitted. (* TOFIXLATER *)
Definition pp_AtomicOp (op:AtomicOp)                                   : string. Admitted. (* TOFIXLATER *)
Definition pp_valCat   (vc:bluerock.lang.cpp.syntax.preliminary.ValCat) : string. Admitted. (* TOFIXLATER *)

Fixpoint pp_name      (n: name)      : string :=
  match n with
  | Ninst base args =>
      pp_name base ++ "<" ++ pp_list ", " pp_temp_arg args ++ ">"
  | Nglobal atm        => pp_atomic_name atm
  | Ndependent t0      => "dependent<" ++ pp_type t0 ++ ">"
  | Nscoped base f     => pp_name base ++ "::" ++ pp_atomic_name f
  | Nunsupported s     => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t0           => pp_type t0
  | Avalue e0          => pp_expr e0
  | Apack args         => "pack<" ++ pp_list ", " pp_temp_arg args ++ ">"
  | Atemplate n0       => pp_name n0
  | Aunsupported s     => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id               => pp_ident id
  | Tresult_param id        => pp_ident id
  | Tresult_global n0       => pp_name n0
  | Tresult_unop op t0      => pp_RUnOp op ++ pp_type t0
  | Tresult_binop op t1 t2  => pp_type t1 ++ pp_RBinOp op ++ pp_type t2
  | Tresult_call n0 ts      => pp_name n0 ++ "(" ++ pp_list ", " pp_type ts ++ ")"
  | Tresult_member_call n0 t0 ts =>
      pp_type t0 ++ "::" ++ pp_name n0 ++ "(" ++ pp_list ", " pp_type ts ++ ")"
  | Tresult_parenlist t0 ts =>
      "(" ++ pp_type t0 ++ ")" ++ "(" ++ pp_list ", " pp_type ts ++ ")"
  | Tresult_member t0 n0    => pp_type t0 ++ "::" ++ pp_name n0
  | Tptr t0                 => pp_type t0 ++ "*"
  | Tref t0                 => pp_type t0 ++ "&"
  | Trv_ref t0              => pp_type t0 ++ "&&"
  | Tnum _ _                => Z_to_string 0         (* stub *)
  | Tchar_ _                => "char"               (* stub *)
  | Tvoid                   => "void"
  | Tarray t0 n             => pp_type t0 ++ "[" ++ N_to_string n ++ "]"
  | Tincomplete_array t0    => pp_type t0 ++ "[]"
  | Tvariable_array t0 e0   => pp_type t0 ++ "[" ++ pp_expr e0 ++ "]"
  | Tnamed n0               => pp_name n0
  | Tenum n0                => "enum " ++ pp_name n0
  | Tfunction _             => "function"           (* stub *)
  | Tbool                   => "bool"
  | Tmember_pointer t1 t2   => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ _               => "float"              (* stub *)
  | Tqualified _ t0         => "(qual " ++ pp_type t0 ++ ")"
  | Tnullptr                => "nullptr_t"
  | Tarch _ _               => "arch"               (* stub *)
  | Tdecltype e0            => "decltype(" ++ pp_expr e0 ++ ")"
  | Texprtype e0            => "typeof(" ++ pp_expr e0 ++ ")"
  | Tunsupported s          => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id                => pp_ident id
  | Eunresolved_global n0    => pp_name n0
  | Eunresolved_unop op e0   => pp_RUnOp op ++ pp_expr e0
  | Eunresolved_binop op l r => pp_expr l ++ pp_RBinOp op ++ pp_expr r
  | Eunresolved_call n0 es   => pp_name n0 ++ "(" ++ pp_list ", " pp_expr es ++ ")"
  | Eunresolved_member_call n0 e0 es =>
      pp_expr e0 ++ "." ++ pp_name n0 ++ "(" ++ pp_list ", " pp_expr es ++ ")"
  | Eunresolved_parenlist _ es =>
      "(" ++ pp_list ", " pp_expr es ++ ")"
  | Eunresolved_member e0 n0 => pp_expr e0 ++ "." ++ pp_name n0
  | Evar id _                => pp_ident id
  | Eenum_const n0 id        => pp_name n0 ++ "::" ++ pp_ident id
  | Eglobal n0 _             => pp_name n0
  | Eglobal_member n0 _      => pp_name n0
  | Echar _ _                => "'c'"               (* stub *)
  | Estring ls _             => pp_literal_string ls
  | Eint z _                 => Z_to_string z
  | Ebool b                  => bool_to_string b
  | Eunop op e0 _            => pp_UnOp op ++ pp_expr e0
  | Ebinop op l r _          => pp_expr l ++ pp_BinOp op ++ pp_expr r
  | Ederef e0 _              => "*" ++ pp_expr e0
  | Eaddrof e0               => "&" ++ pp_expr e0
  | Eassign l r _            => pp_expr l ++ " = " ++ pp_expr r
  | Eassign_op op l r _      =>
      pp_expr l ++ " " ++ pp_BinOp op ++ "= " ++ pp_expr r
  | Epreinc e0 _             => "++" ++ pp_expr e0
  | Epostinc e0 _            => pp_expr e0 ++ "++"
  | Epredec e0 _             => "--" ++ pp_expr e0
  | Epostdec e0 _            => pp_expr e0 ++ "--"
  | Eseqand l r              => pp_expr l ++ " && " ++ pp_expr r
  | Eseqor l r               => pp_expr l ++ " || " ++ pp_expr r
  | Ecomma l r               => pp_expr l ++ ", " ++ pp_expr r
  | Ecall f es               => pp_expr f ++ "(" ++ pp_list ", " pp_expr es ++ ")"
  | Eexplicit_cast cs _ e0   =>
      "(" ++ pp_cast_style cs ++ ")" ++ pp_expr e0
  | Ecast c e0               =>
      "(" ++ pp_cast c ++ ")" ++ pp_expr e0
  | Emember arrow obj f _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name f
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mth obj args =>
      let fname :=
        match mth with
        | inl (nm, _dt, _ty) => pp_name nm
        | inr e1             => pp_expr e1
        end in
      pp_expr obj ++ (if arrow then "->" else ".")
                   ++ fname ++ "(" ++ pp_list ", " pp_expr args ++ ")"
  | Eoperator_call op impl args =>
      pp_OvlOp op ++ "(" ++ pp_list ", " pp_expr args ++ ")"
  | Esubscript a i _        => pp_expr a ++ "[" ++ pp_expr i ++ "]"
  | Esizeof ar _            =>
      "sizeof(" ++ match ar with inl t0 => pp_type t0 | inr e1 => pp_expr e1 end ++ ")"
  | Ealignof ar _           =>
      "alignof(" ++ match ar with inl t0 => pp_type t0 | inr e1 => pp_expr e1 end ++ ")"
  | Eoffsetof t0 id _       =>
      "offsetof(" ++ pp_type t0 ++ ", " ++ pp_ident id ++ ")"
  | Econstructor n0 es _    =>
      pp_name n0 ++ "(" ++ pp_list ", " pp_expr es ++ ")"
  | Elambda id args         =>
      "[" ++ pp_name id ++ "](" ++ pp_list ", " pp_expr args ++ ")"
  | Eimplicit e0            => pp_expr e0
  | Eimplicit_init t0       => "implicit_init<" ++ pp_type t0 ++ ">"
  | Eif c t f _             =>
      "(" ++ pp_expr c ++ " ? " ++ pp_expr t ++ " : " ++ pp_expr f ++ ")"
  | Eif2 _ c t f _ _        =>
      "(" ++ pp_expr c ++ " ? " ++ pp_expr t ++ " : " ++ pp_expr f ++ ")"
  | Ethis _                 => "this"
  | Enull                   => "nullptr"
  | Einitlist es dv _       =>
      "{" ++ pp_list ", " pp_expr es
          ++ match dv with None => "" | Some d => " ... " ++ pp_expr d end
          ++ "}"
  | Einitlist_union n0 dv _ =>
      "{" ++ pp_atomic_name n0
          ++ match dv with None => "" | Some d => " ... " ++ pp_expr d end
          ++ "}"
  | Enew _ _ _ _ _ _        => "new_expr"     (* stub *)
  | Edelete is_arr _ e0 _   =>
      "delete" ++ (if is_arr then "[]" else "") ++ pp_expr e0
  | Eandclean e1            => pp_expr e1
  | Ematerialize_temp e0 _  => "materialize(" ++ pp_expr e0 ++ ")"
  | Eatomic op args _       => pp_AtomicOp op ++ "(" ++ pp_list ", " pp_expr args ++ ")"
  | Estmt s0 _              => "(" ++ pp_stmt s0 ++ ")"
  | Eva_arg e0 _            => pp_expr e0
  | Epseudo_destructor a _ e0 =>
      pp_expr e0 ++ (if a then "->" else ".") ++ "destroy"
  | Earrayloop_init _ src _ _ init _ =>
      "arrayloop(" ++ pp_expr src ++ ", " ++ pp_expr init ++ ")"
  | Earrayloop_index _ _    => "array_index"
  | Eopaque_ref _ _         => "opaque_ref"
  | Eunsupported s _        => s
  end

with pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq ss                => "{ " ++ pp_list "; " pp_stmt ss ++ " }"
  | Sdecl ds               => "decl " ++ pp_list ", " pp_vardecl ds
  | Sif vd c t f           =>
      let pre := match vd with None => "" | Some d => pp_vardecl d ++ "; " end in
      pre ++ "if(" ++ pp_expr c ++ ") " ++ pp_stmt t ++ " else " ++ pp_stmt f
  | Sif_consteval t f      =>
      "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt f
  | Swhile vd c b          =>
      let pre := match vd with None => "" | Some d => pp_vardecl d ++ "; " end in
      pre ++ "while(" ++ pp_expr c ++ ") " ++ pp_stmt b
  | Sfor i c u bd          =>
      let si := match i with None => "" | Some s0 => pp_stmt s0 end in
      let sc := match c with None => "" | Some e0 => pp_expr e0 end in
      let su := match u with None => "" | Some e0 => pp_expr e0 end in
      "for(" ++ si ++ "; " ++ sc ++ "; " ++ su ++ ") " ++ pp_stmt bd
  | Sdo bd c               => "do " ++ pp_stmt bd ++ " while(" ++ pp_expr c ++ ")"
  | Sswitch vd c bd        =>
      let pre := match vd with None => "" | Some d => pp_vardecl d ++ "; " end in
      pre ++ "switch(" ++ pp_expr c ++ ") " ++ pp_stmt bd
  | Scase sb               => "case " ++ pp_SwitchBranch sb
  | Sdefault               => "default: ;"
  | Sbreak                 => "break;"
  | Scontinue              => "continue;"
  | Sreturn eo             =>
      "return" ++ match eo with None => ";" | Some e0 => " " ++ pp_expr e0 ++ ";" end
  | Sexpr e0               => pp_expr e0 ++ ";"
  | Sattr ids bd           =>
      "[[" ++ pp_list ", " pp_ident ids ++ "]] " ++ pp_stmt bd
  | Sasm str v inps outs clobs =>
      "asm(" ++ pp_pstring str ++ ");"
  | Slabeled id bd         => pp_ident id ++ ": " ++ pp_stmt bd
  | Sgoto id               => "goto " ++ pp_ident id ++ ";"
  | Sunsupported s         => s
  end

with pp_vardecl (d: VarDecl) : string :=
  match d with
  | Dvar nm t0 init       =>
      pp_ident nm ++ ": " ++ pp_type t0
      ++ match init with None => "" | Some e0 => " = " ++ pp_expr e0 end
  | Ddecompose e0 id bs    =>
      "decompose " ++ pp_expr e0 ++ " as " ++ pp_ident id
  | Dinit b nm t0 init     =>
      (if b then "thread_local " else "") ++ pp_name nm ++ ": " ++ pp_type t0
      ++ match init with None => "" | Some e0 => " = " ++ pp_expr e0 end
  end

with pp_bindingdecl (b: BindingDecl) : string :=
  match b with
  | Bvar nm t0 e0         => pp_ident nm ++ ": " ++ pp_type t0 ++ " = " ++ pp_expr e0
  | Bbind nm t0 e0        => pp_ident nm ++ ": " ++ pp_type t0 ++ " = " ++ pp_expr e0
  end

with pp_cast (c: Cast) : string :=
  match c with
  | Cdependent t0          => "static_cast<"      ++ pp_type t0 ++ ">"
  | Cbitcast t0            => "bit_cast<"         ++ pp_type t0 ++ ">"
  | Clvaluebitcast t0      => "lvalue_bitcast<"   ++ pp_type t0 ++ ">"
  | Cl2r                   => "lvalue_to_rvalue"
  | Cl2r_bitcast t0        => "l2r_bitcast<"      ++ pp_type t0 ++ ">"
  | Cnoop t0               => "noop<"             ++ pp_type t0 ++ ">"
  | Carray2ptr             => "array_to_ptr"
  | Cfun2ptr               => "func_to_ptr"
  | Cint2ptr t0            => "int_to_ptr<"       ++ pp_type t0 ++ ">"
  | Cptr2int t0            => "ptr_to_int<"       ++ pp_type t0 ++ ">"
  | Cptr2bool              => "ptr_to_bool"
  | Cintegral t0           => "integral_cast<"    ++ pp_type t0 ++ ">"
  | Cint2bool              => "int_to_bool"
  | Cfloat2int t0          => "float_to_int<"     ++ pp_type t0 ++ ">"
  | Cint2float t0          => "int_to_float<"     ++ pp_type t0 ++ ">"
  | Cfloat t0              => "float_cast<"       ++ pp_type t0 ++ ">"
  | Cnull2ptr t0           => "null_to_ptr<"      ++ pp_type t0 ++ ">"
  | Cnull2memberptr t0     => "null_to_memptr<"   ++ pp_type t0 ++ ">"
  | Cbuiltin2fun t0        => "builtin_to_fun<"   ++ pp_type t0 ++ ">"
  | C2void                 => "void_cast"
  | Cctor t0               => "ctor<"             ++ pp_type t0 ++ ">"
  | Cuser                  => "user_cast"
  | Cdynamic t0            => "dynamic_cast<"     ++ pp_type t0 ++ ">"
  | Cderived2base _ t0     => "derived_to_base"
  | Cbase2derived _ t0     => "base_to_derived"
  | Cunsupported _ _       => "unsupported_cast"
  end.


