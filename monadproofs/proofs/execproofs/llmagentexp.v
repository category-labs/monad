Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Open Scope pstring_scope.

Locate localname.
Search (bluerock.lang.cpp.syntax.preliminary.localname → PrimString.string).
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

Require Import List.
Import ListNotations.
Require Import PrimString.
Require Import ZArith.
Require Import Coq.NArith.NArith.
Require Import bluerock.lang.cpp.syntax.stmt.  (* adjust to your actual path *)

Local Open Scope pstring.
Local Open Scope Z_scope.

(* join a list of PrimString.string with sep in between *)
Fixpoint join (sep: PrimString.string) (l: list PrimString.string) {struct l}
  : PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    match xs with
    | []    => x
    | _ :: _ => x ++ sep ++ join sep xs
    end
  end.

(* Stubs needed by pprint_name *)
Definition pprint_atomic_name (a: atomic_name) : PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pprint_temp_arg    (a: temp_arg)     : PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pprint_type        (t: type)         : PrimString.string. Admitted.  (* TOFIXLATER *)

(* --- Implemented hole: name printer --- *)
Fixpoint pprint_name (n: name) : PrimString.string :=
  match n with
  | Ninst base args =>
      (* Template instantiation: Base<Arg1, Arg2, …> *)
      pprint_name base
      ++ "<"%pstring
      ++ join ", "%pstring (List.map pprint_temp_arg args)
      ++ ">"%pstring
  | Nglobal a =>
      (* Plain global atomic name *)
      pprint_atomic_name a
  | Ndependent t =>
      (* Dependent name: dependent(type) *)
      "dependent("%pstring ++ pprint_type t ++ ")"%pstring
  | Nscoped parent a =>
      (* Scoped name: Parent::Atomic *)
      pprint_name parent ++ "::"%pstring ++ pprint_atomic_name a
  | Nunsupported s =>
      (* Fallback for unsupported names *)
      "‹unsupported name: "%pstring ++ s ++ "›"%pstring
  end.

(* Stubs for all other printers *)
Definition pprint_Expr          (e: Expr)             : PrimString.string. Admitted. (* TOFIXLATER *)
Definition pprint_BindingDecl   (b: BindingDecl)      : PrimString.string. Admitted. (* TOFIXLATER *)
Definition pprint_Cast          (c: Cast)             : PrimString.string. Admitted. (* TOFIXLATER *)
Definition pprint_switch_branch (b: SwitchBranch)     : PrimString.string. Admitted. (* TOFIXLATER *)

(* VarDecl printer *)
Definition pprint_VarDecl (d: VarDecl) : PrimString.string :=
  match d with
  | Dvar id ty oe =>
      id ++ ": "%pstring ++ pprint_type ty
      ++ match oe with
         | Some e => " = "%pstring ++ pprint_Expr e
         | None   => ""%pstring
         end
  | Ddecompose expr _id binds =>
      "auto ["%pstring
      ++ join ", "%pstring (List.map pprint_BindingDecl binds)
      ++ "] = "%pstring ++ pprint_Expr expr
  | Dinit _ts nm ty oe =>
      pprint_name nm ++ ": "%pstring ++ pprint_type ty
      ++ match oe with
         | Some e => " = "%pstring ++ pprint_Expr e
         | None   => ""%pstring
         end
  end.

(* The main Stmt‐printer *)
Fixpoint pprint_Stmt (s: Stmt) : PrimString.string :=
  match s with
  | Sseq ss     => "(" ++ join "; "%pstring (List.map pprint_Stmt ss) ++ ")"%pstring
  | Sdecl ds    => "decl "%pstring ++ join ", "%pstring (List.map pprint_VarDecl ds)
  | Sif vd e t f =>
      let init := match vd with Some d => pprint_VarDecl d ++ "; "%pstring | None => ""%pstring end in
      "if (" ++ init ++ pprint_Expr e ++ ")"%pstring
      ++ " then "%pstring ++ pprint_Stmt t
      ++ " else "%pstring ++ pprint_Stmt f
  | Sif_consteval t f =>
      "if consteval then "%pstring ++ pprint_Stmt t ++ " else "%pstring ++ pprint_Stmt f
  | Swhile vd e body =>
      let init := match vd with Some d => pprint_VarDecl d ++ "; "%pstring | None => ""%pstring end in
      "while (" ++ init ++ pprint_Expr e ++ ")"%pstring ++ pprint_Stmt body
  | Sfor i c p b =>
      let i' := match i with Some st => pprint_Stmt st | None => ""%pstring end in
      let c' := match c with Some e  => pprint_Expr e   | None => ""%pstring end in
      let p' := match p with Some e  => pprint_Expr e   | None => ""%pstring end in
      "for (" ++ i' ++ "; "%pstring ++ c' ++ "; "%pstring ++ p' ++ ")"%pstring
      ++ pprint_Stmt b
  | Sdo b e      => "do "%pstring ++ pprint_Stmt b ++ " while ("%pstring ++ pprint_Expr e ++ ")"%pstring
  | Sswitch vd e body =>
      let vd' := match vd with Some d => pprint_VarDecl d ++ "; "%pstring | None => ""%pstring end in
      "switch (" ++ vd' ++ pprint_Expr e ++ ")"%pstring ++ pprint_Stmt body
  | Scase br     => "case "%pstring ++ pprint_switch_branch br
  | Sdefault     => "default"%pstring
  | Sbreak       => "break"%pstring
  | Scontinue    => "continue"%pstring
  | Sreturn oe   =>
      "return"%pstring ++ match oe with Some e => " "%pstring ++ pprint_Expr e | None => ""%pstring end
  | Sexpr e      => pprint_Expr e ++ ";"%pstring
  | Sattr as_ b  =>
      "[" ++ join ", "%pstring (List.map (fun id => id)%pstring as_) ++ "] "%pstring ++ pprint_Stmt b
  | Sasm str _ _ _ _ => "asm "%pstring ++ str
  | Slabeled id b   => id ++ ": "%pstring ++ pprint_Stmt b
  | Sgoto id         => "goto "%pstring ++ id
  | Sunsupported s   => "/* unsupported: "%pstring ++ s ++ " */"%pstring
  end.

Definition pretty_print_stmt : Stmt -> PrimString.string := pprint_Stmt.


