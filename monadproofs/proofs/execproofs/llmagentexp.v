Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Open Scope pstring_scope.



(*
Write a Coq function to pretty print bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
bluerock.lang.cpp.syntax.stmt.Stmt is defined mutually Inductively with many other types like Expr.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be bluerock.lang.cpp.syntax.stmt.Stmt -> PrimString.string.
PrimString.string is a new type in Coq's core standard library. It axiomatizes primitive strings.
It is different from Stdlib.Strings.String.string, which are the non-primitive strings that have been in the Coq stdlib for decades.
The are slower so I avoid using them in this application where speed is important.
 *)

Set Printing All.
Print Stmt.




