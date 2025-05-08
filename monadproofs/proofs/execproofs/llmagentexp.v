Require Import bluerock.auto.invariants.
Set Printing FullyQualifiedNames.
Require Import bluerock.auto.cpp.proof.
Import linearity.


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

Fixpoint pp_name        (n:name)        : string :=
  match n with
  | Ninst on args    => pp_name on ++ "<"%pstring ++ join "," (map pp_temp_arg args) ++ ">"%pstring
  | Nglobal an       => pp_atomic_name an
  | Ndependent ty    => pp_type ty
  | Nscoped parent an=> pp_name parent ++ "::"%pstring ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg   (a:temp_arg)    : string :=
  match a with
  | Atype ty         => pp_type ty
  | Avalue e         => pp_expr e
  | Apack ps         => "..."%pstring ++ join "," (map pp_temp_arg ps)
  | Atemplate n      => pp_name n
  | Aunsupported s   => s
  end

(* …and so on for pp_type, pp_expr, pp_stmt, etc. … *)


