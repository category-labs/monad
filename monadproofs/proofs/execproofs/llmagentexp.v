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
I have already opened pstring_scope so you may be able to elide the %pstring part.
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.
*)

(* assume pstring_scope is open *)

(* ========== Helper stubs (to be implemented later) ========== *)
Definition string_of_Z (z: Z) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_N (n: N) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_bool (b: bool) : string :=
  if b then "true" else "false".

Definition string_of_ident (i: bluerock.lang.cpp.syntax.preliminary.ident) : string :=
  i.  (* ident is just PrimString.string *)

Definition string_of_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_RUnOp (op: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_RBinOp (op: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_UnOp (op: bluerock.lang.cpp.syntax.preliminary.UnOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_BinOp (op: bluerock.lang.cpp.syntax.preliminary.BinOp) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_literal_string
  (s: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_cast_style
  (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_new_form
  (n: bluerock.lang.cpp.syntax.preliminary.new_form.t) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_MethodRef
  (m: bluerock.lang.cpp.syntax.preliminary.MethodRef_
         bluerock.lang.cpp.syntax.core.name
         bluerock.lang.cpp.syntax.core.type
         bluerock.lang.cpp.syntax.core.Expr) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_operator_impl
  (o: bluerock.lang.cpp.syntax.preliminary.operator_impl.t
         bluerock.lang.cpp.syntax.core.name
         bluerock.lang.cpp.syntax.core.type) : string.
Admitted. (* TOFIXLATER *)

Definition string_of_OverloadableOperator
  (o: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string.
Admitted. (* TOFIXLATER *)


(* ========== A simple join on PrimString.string ========== *)
Fixpoint join (sep: string) (ss: list string) : string :=
  match ss with
  | [] => ""
  | [s] => s
  | s :: rest => s ++ sep ++ join sep rest
  end.


(* ========== Main mutually‐recursive pretty‐printers ========== *)
Fixpoint pprint_name
         (n: bluerock.lang.cpp.syntax.core.name) : string :=
  match n with
  | bluerock.lang.cpp.syntax.core.Ninst base args =>
      pprint_name base ++ "<" ++ join "," (List.map pprint_temp_arg args) ++ ">"
  | bluerock.lang.cpp.syntax.core.Nglobal a =>
      (* placeholder; actual atomic_name printer below *)
      "<global>"
  | bluerock.lang.cpp.syntax.core.Ndependent t =>
      pprint_type t
  | bluerock.lang.cpp.syntax.core.Nscoped outer a =>
      pprint_name outer ++ "::" ++ "<atomic>"
  | bluerock.lang.cpp.syntax.core.Nunsupported s =>
      s
  end

with pprint_temp_arg
         (ta: bluerock.lang.cpp.syntax.core.temp_arg) : string :=
  match ta with
  | bluerock.lang.cpp.syntax.core.Atype t       => pprint_type t
  | bluerock.lang.cpp.syntax.core.Avalue e       => pprint_Expr e
  | bluerock.lang.cpp.syntax.core.Apack tas      =>
      "pack<" ++ join "," (List.map pprint_temp_arg tas) ++ ">"
  | bluerock.lang.cpp.syntax.core.Atemplate nm   => pprint_name nm
  | bluerock.lang.cpp.syntax.core.Aunsupported s => s
  end

with pprint_type
         (t: bluerock.lang.cpp.syntax.core.type) : string :=
  match t with
  | bluerock.lang.cpp.syntax.core.Tparam id        => string_of_ident id
  | bluerock.lang.cpp.syntax.core.Tresult_param id => string_of_ident id
  | bluerock.lang.cpp.syntax.core.Tresult_global n => pprint_name n
  | bluerock.lang.cpp.syntax.core.Tresult_unop op t1 =>
      string_of_RUnOp op ++ pprint_type t1
  | bluerock.lang.cpp.syntax.core.Tresult_binop op t1 t2 =>
      "(" ++ pprint_type t1 ++ string_of_RBinOp op ++ pprint_type t2 ++ ")"
  | bluerock.lang.cpp.syntax.core.Tresult_call n ts =>
      pprint_name n ++ "<" ++ join "," (List.map pprint_type ts) ++ ">"
  | bluerock.lang.cpp.syntax.core.Tresult_member_call n t0 ts =>
      pprint_name n ++ "<" ++ pprint_type t0 ++ ">("
      ++ join "," (List.map pprint_type ts) ++ ")"
  | bluerock.lang.cpp.syntax.core.Tptr t0       => pprint_type t0 ++ "*"
  | bluerock.lang.cpp.syntax.core.Tref t0       => pprint_type t0 ++ "&"
  | bluerock.lang.cpp.syntax.core.Trv_ref t0    => pprint_type t0 ++ "&&"
  | bluerock.lang.cpp.syntax.core.Tarray t0 n   =>
      pprint_type t0 ++ "[" ++ string_of_N n ++ "]"
  | bluerock.lang.cpp.syntax.core.Tincomplete_array t0 =>
      pprint_type t0 ++ "[]"
  | bluerock.lang.cpp.syntax.core.Tvariable_array t0 e0 =>
      pprint_type t0 ++ "[" ++ pprint_Expr e0 ++ "]"
  | bluerock.lang.cpp.syntax.core.Tnamed n      => pprint_name n
  | bluerock.lang.cpp.syntax.core.Tenum n       => "enum " ++ pprint_name n
  | bluerock.lang.cpp.syntax.core.Tfunction _   => "<fun-type>"    (* TOFIXLATER *)
  | bluerock.lang.cpp.syntax.core.Tbool          => "bool"
  | bluerock.lang.cpp.syntax.core.Tvoid          => "void"
  | bluerock.lang.cpp.syntax.core.Tnullptr       => "nullptr_t"
  | bluerock.lang.cpp.syntax.core.Tunsupported s => s
  | _ => "<TBD>"  (* rest TOFIXLATER *)
  end

with pprint_Expr
         (e: bluerock.lang.cpp.syntax.core.Expr) : string :=
  match e with
  | bluerock.lang.cpp.syntax.core.Eparam id        => string_of_ident id
  | bluerock.lang.cpp.syntax.core.Eunresolved_global n =>
      pprint_name n
  | bluerock.lang.cpp.syntax.core.Eunresolved_unop op e1 =>
      string_of_RUnOp op ++ pprint_Expr e1
  | bluerock.lang.cpp.syntax.core.Eunresolved_binop op l r =>
      "(" ++ pprint_Expr l ++ string_of_RBinOp op ++ pprint_Expr r ++ ")"
  | bluerock.lang.cpp.syntax.core.Eunresolved_call n args =>
      pprint_name n ++ "(" ++ join "," (List.map pprint_Expr args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Evar _ _          => "<var>"       (* TOFIXLATER *)
  | bluerock.lang.cpp.syntax.core.Eint z _          => string_of_Z z
  | bluerock.lang.cpp.syntax.core.Ebool b           => string_of_bool b
  | bluerock.lang.cpp.syntax.core.Ebinop op l r _   =>
      "(" ++ pprint_Expr l ++ string_of_BinOp op ++ pprint_Expr r ++ ")"
  | bluerock.lang.cpp.syntax.core.Ecall f args      =>
      pprint_Expr f ++ "(" ++ join "," (List.map pprint_Expr args) ++ ")"
  | bluerock.lang.cpp.syntax.core.Eexplicit_cast sty ty e1 =>
      string_of_cast_style sty ++ "<" ++ pprint_type ty ++ ">(" ++ pprint_Expr e1 ++ ")"
  | bluerock.lang.cpp.syntax.core.Ecast _ e1         =>
      "(<cast>)" ++ pprint_Expr e1  (* TOFIXLATER *)
  | bluerock.lang.cpp.syntax.core.Eif cond tbranch ebranch _ =>
      "if(" ++ pprint_Expr cond ++ ")"
      ++ pprint_Expr tbranch ++ " else " ++ pprint_Expr ebranch
  | bluerock.lang.cpp.syntax.core.Enew (nm, ty0) args nf ty1 o1 o2 =>
      "new " ++ pprint_name nm ++ "<" ++ pprint_type ty0 ++ ">("
      ++ join "," (List.map pprint_Expr args) ++ ") "
      ++ string_of_new_form nf ++ pprint_type ty1
      ++ match o1 with None => "" | Some e => "[" ++ pprint_Expr e ++ "]" end
      ++ match o2 with None => "" | Some e => "{" ++ pprint_Expr e ++ "}" end
  | bluerock.lang.cpp.syntax.core.Estmt s _         => pprint_Stmt s
  | bluerock.lang.cpp.syntax.core.Eunsupported s _  => s
  | _ => "<eTBD>"  (* rest TOFIXLATER *)
  end

with pprint_Stmt
         (s: bluerock.lang.cpp.syntax.core.Stmt) : string :=
  match s with
  | bluerock.lang.cpp.syntax.core.Sseq ss  =>
      "{" ++ join ";" (List.map pprint_Stmt ss) ++ "}"
  | bluerock.lang.cpp.syntax.core.Sdecl vds =>
      "decl " ++ join ", " (List.map pprint_VarDecl vds)
  | bluerock.lang.cpp.syntax.core.Sif vd_opt cond thn els =>
      "if(" ++ match vd_opt with None => "" | Some vd => pprint_VarDecl vd ++ "; " end
             ++ pprint_Expr cond ++ ") " ++ pprint_Stmt thn
             ++ " else " ++ pprint_Stmt els
  | bluerock.lang.cpp.syntax.core.Sfor init cond incr body =>
      let f o := match o with None => "" | Some e => pprint_Expr e end in
      "for(" ++ match init with None => "" | Some s1 => pprint_Stmt s1 end
              ++ ";" ++ f cond ++ ";" ++ f incr ++ ") " ++ pprint_Stmt body
  | bluerock.lang.cpp.syntax.core.Swhile _ cond body =>
      "while(" ++ pprint_Expr cond ++ ") " ++ pprint_Stmt body
  | bluerock.lang.cpp.syntax.core.Sreturn eo =>
      "return " ++ match eo with None => "" | Some e => pprint_Expr e end
  | bluerock.lang.cpp.syntax.core.Sexpr e    => pprint_Expr e ++ ";"
  | bluerock.lang.cpp.syntax.core.Sunsupported s => s
  | _ => "<sTBD>"  (* rest TOFIXLATER *)
  end

with pprint_VarDecl
         (d: bluerock.lang.cpp.syntax.core.VarDecl) : string :=
  match d with
  | bluerock.lang.cpp.syntax.core.Dvar _ _ _      => "<decl>"  (* TOFIXLATER *)
  | _ => "<vdTBD>"  (* rest TOFIXLATER *)
  end

with pprint_BindingDecl
         (b: bluerock.lang.cpp.syntax.core.BindingDecl) : string :=
  match b with
  | bluerock.lang.cpp.syntax.core.Bvar _ _ _       => "<bind>" (* TOFIXLATER *)
  | _ => "<bdTBD>"  (* rest TOFIXLATER *)
  end

with pprint_Cast
         (c: bluerock.lang.cpp.syntax.core.Cast) : string :=
  match c with
  | bluerock.lang.cpp.syntax.core.Cdependent _    => "<Cdep>"
  | bluerock.lang.cpp.syntax.core.Cnoop _         => ""
  | _ => "<castTBD>"  (* rest TOFIXLATER *)
  end.

