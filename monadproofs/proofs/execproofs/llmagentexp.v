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

Fixpoint pprint_name (n: bluerock.lang.cpp.syntax.core.name') : Corelib.Strings.PrimString.string :=
  "<name>"

with pprint_temp_arg (ta: bluerock.lang.cpp.syntax.core.temp_arg') : Corelib.Strings.PrimString.string :=
  "<temp_arg>"

with pprint_type (ty: bluerock.lang.cpp.syntax.core.type') : Corelib.Strings.PrimString.string :=
  "<type>"

with pprint_expr (e: bluerock.lang.cpp.syntax.core.Expr') : Corelib.Strings.PrimString.string :=
  "<expr>"

with pprint_stmt (s: bluerock.lang.cpp.syntax.core.Stmt') : Corelib.Strings.PrimString.string :=
  "<stmt>"

with pprint_vardecl (d: bluerock.lang.cpp.syntax.core.VarDecl') : Corelib.Strings.PrimString.string :=
  "<vardecl>"

with pprint_bindingdecl (b: bluerock.lang.cpp.syntax.core.BindingDecl') : Corelib.Strings.PrimString.string :=
  "<bindingdecl>"

with pprint_cast (c: bluerock.lang.cpp.syntax.core.Cast') : Corelib.Strings.PrimString.string :=
  "<cast>".

(* You can now refine each placeholder, e.g.: *)

(*
Fixpoint pprint_name (n: name') : string :=
  match n with
  | Ninst base args =>
      pprint_name base ++ "<" ++ pprint_list pprint_temp_arg "," args ++ ">"
  | Nglobal a      => pprint_atomic_name a
  | Ndependent ty  => "decltype(" ++ pprint_type ty ++ ")"
  | Nscoped n' a   => pprint_name n' ++ "::" ++ pprint_atomic_name a
  | Nunsupported s => s
  end
with ...
*)

(* Helper for printing lists, options, etc. *)
Fixpoint pprint_list {A}
  (f : A -> Corelib.Strings.PrimString.string)
  (sep : Corelib.Strings.PrimString.string)
  (l : Corelib.Init.Datatypes.list A)
  : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""
  | x :: xs =>
     f x ++
     match xs with
     | [] => ""
     | _  => sep ++ pprint_list f sep xs
     end
  end.

Definition pprint_option {A}
  (f : A -> Corelib.Strings.PrimString.string)
  (o : Corelib.Init.Datatypes.option A)
  : Corelib.Strings.PrimString.string :=
  match o with
  | Corelib.Init.Datatypes.None   => ""
  | Corelib.Init.Datatypes.Some x => f x
  end.



