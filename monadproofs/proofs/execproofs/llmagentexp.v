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
