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
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.Require Import PrimString.
 *)


Require Import PrimString.
Require Import Corelib.Init.Datatypes.
Require Import bluerock.lang.cpp.syntax.core.
Require Import bluerock.lang.cpp.syntax.pretty.
Import Corelib.Strings.PrimString.PStringNotations.
Local Open Scope pstring.

(* Aliases for existing printers *)
Definition sepBy := bluerock.lang.cpp.syntax.name_notation.printer.sepBy.
Definition printN := bluerock.lang.cpp.syntax.pretty.printN.
Definition printT := bluerock.lang.cpp.syntax.pretty.printT.
Definition printE := bluerock.lang.cpp.syntax.pretty.printE.
Definition angles := bluerock.lang.cpp.syntax.pretty.angles.
Definition parens := bluerock.lang.cpp.syntax.pretty.parens.
Definition showZ := bluerock.lang.cpp.syntax.name_notation.printer.showN.showZ.

(* ---------------------------------------------------------------------- *)
(* Printer for switch‐case branches *)
Definition printSwitchBranch
  (br: bluerock.lang.cpp.syntax.preliminary.SwitchBranch) : string :=
  match br with
  | bluerock.lang.cpp.syntax.preliminary.Exact z =>
      "case " ++ showZ z ++ ":"
  | bluerock.lang.cpp.syntax.preliminary.Range z1 z2 =>
      "case " ++ showZ z1 ++ " ... " ++ showZ z2 ++ ":"
  end.

(* ---------------------------------------------------------------------- *)
(* Template arguments *)
Fixpoint printTempArg (ta: temp_arg) : string :=
  match ta with
  | Atype t        => printT t
  | Avalue e       => printE e
  | Apack args     => angles (sepBy "," (List.map printTempArg args))
  | Atemplate n    => printN n
  | Aunsupported s => s
  end.

(* ---------------------------------------------------------------------- *)
(* Bindings, var‐decls, and statements *)
Fixpoint printBindingDecl (bd: BindingDecl) : string :=
  match bd with
  | Bvar name ty init =>
      "(" ++ name ++ ":" ++ printT ty ++ " = " ++ printE init ++ ")"
  | Bbind name ty init =>
      "(" ++ name ++ ":" ++ printT ty ++ " ← " ++ printE init ++ ")"
  end

with printVarDecl (vd: VarDecl) : string :=
  match vd with
  | Dvar name ty init =>
      "auto " ++ name ++ " : " ++ printT ty ++
        match init with Some e => " = " ++ printE e | None => "" end
  | Ddecompose e anon bindings =>
      "auto [" ++ sepBy "," (List.map printBindingDecl bindings) ++ "] = " ++ printE e
  | Dinit thread_local name ty init =>
      (if thread_local then "thread_local " else "") ++
      "auto " ++ printN name ++ " : " ++ printT ty ++
        match init with Some e => " = " ++ printE e | None => "" end
  end

with printStmt (s: Stmt) : string :=
  match s with
  | Sseq ss =>
      "{ " ++ sepBy "; " (List.map printStmt ss) ++ " }"
  | Sdecl ds =>
      "{ " ++ sepBy "; " (List.map printVarDecl ds) ++ " }"
  | Sif _ e1 s1 s2 =>
      "if (" ++ printE e1 ++ ")" ++ printStmt s1 ++
        " else " ++ printStmt s2
  | Sif_consteval s1 s2 =>
      "if consteval " ++ printStmt s1 ++ " else " ++ printStmt s2
  | Swhile _ e1 body =>
      "while (" ++ printE e1 ++ ") " ++ printStmt body
  | Sfor init cond step body =>
      "for (" ++ (match init with Some si => printStmt si | None => "" end) ++
        "; " ++ (match cond with Some e => printE e | None => "" end) ++
        "; " ++ (match step with Some e => printE e | None => "" end) ++
      ") " ++ printStmt body
  | Sdo body e1 =>
      "do " ++ printStmt body ++ " while (" ++ printE e1 ++ ");"
  | Sswitch _ e1 body =>
      "switch (" ++ printE e1 ++ ") " ++ printStmt body
  | Scase br =>
      printSwitchBranch br
  | Sdefault    => "default:"
  | Sbreak      => "break;"
  | Scontinue   => "continue;"
  | Sreturn oe  =>
      "return" ++ match oe with Some e => " " ++ printE e | None => "" end ++ ";"
  | Sexpr e     => printE e ++ ";"
  | Sattr attrs st =>
      sepBy " " (List.map id_string attrs) ++ " " ++ printStmt st
  | Sasm s _ _ _ _ =>
      "asm(" ++ s ++ ")"
  | Slabeled lbl st =>
      id_string lbl ++ ": " ++ printStmt st
  | Sgoto lbl =>
      "goto " ++ id_string lbl ++ ";"
  | Sunsupported s => s
  end.

