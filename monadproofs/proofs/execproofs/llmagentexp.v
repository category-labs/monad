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
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.
*)


Require Import PrimString.
Local Open Scope pstring.

(* -------------------------------------------------------------------- *)
(* 1. Admitted holes for all external helpers                           *)
Definition string_of_ident
           (i: bluerock.lang.cpp.syntax.preliminary.ident) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_atomic_name
           (an: atomic_name) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_int_rank
           (ir: int_rank) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_signed
           (sg: bluerock.prelude.arith.types.signed) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_bool (b: bool) : string :=
  if b then "true"%pstring else "false"%pstring.
Definition string_of_Z (z: Z) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_N (n: N) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_bitsize (b: bitsize) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_literal_string
           (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : string.
Admitted. (* TOFIXLATER *)
Definition string_of_valcat
           (vc: bluerock.lang.cpp.syntax.preliminary.ValCat) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_UnOp
           (op: bluerock.lang.cpp.syntax.preliminary.UnOp) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_BinOp
           (op: bluerock.lang.cpp.syntax.preliminary.BinOp) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_AtomicOp
           (op: AtomicOp) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_new_form
           (nf: new_form) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_function_type_
           {T} (ft: bluerock.lang.cpp.syntax.core.function_type_ T) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_type_qualifiers
           (q: bluerock.lang.cpp.syntax.preliminary.type_qualifiers) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_MethodRef
           (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : string.
Admitted. (* TOFIXLATER *)
Definition string_of_operator_impl
           (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : string.
Admitted. (* TOFIXLATER *)
Definition string_of_OverloadableOperator
           (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : string.
Admitted. (* TOFIXLATER *)
Definition string_of_RUnOp
           (op: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_RBinOp
           (op: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_char_type
           (ct: bluerock.lang.cpp.syntax.preliminary.char_type) : string.
Admitted. (* TOFIXLATER *)
Definition string_of_switchbranch
           (br: bluerock.lang.cpp.syntax.preliminary.SwitchBranch) : string.
Admitted. (* TOFIXLATER *)

(* -------------------------------------------------------------------- *)
(* 2. Single mutually‐recursive block for all eight printers           *)
Fixpoint string_of_name        (n: name)       : string := ""%pstring
with     string_of_temp_arg   (ta: temp_arg)   : string := ""%pstring
with     string_of_type       (t: type)       : string := ""%pstring
with     string_of_expr       (e: Expr)       : string := ""%pstring
with     string_of_stmt       (s: Stmt)       : string := ""%pstring
with     string_of_vardecl    (d: VarDecl)    : string := ""%pstring
with     string_of_bindingdecl(b: BindingDecl): string := ""%pstring
with     string_of_cast       (c: Cast)       : string := ""%pstring.



