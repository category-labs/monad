Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.


Require Import Corelib.Strings.PrimString.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Corelib.Numbers.Cyclic.Int63.Uint63Axioms.
Import ListNotations.

(* ------------------------------------------------------------------- *)
(* Primitive‐int constants for PrimInt63.int *)
Definition zero63 : PrimInt63.int := of_Z 0.
Definition one63  : PrimInt63.int := of_Z 1.

(* Opaque conversion from Coq ascii to the primitive‐char63 type *)
Parameter char63_of_ascii : ascii → PrimString.char63.  (* TOFIXLATER *)

(* Build a single‐character primitive string *)
Definition pstring_of_char (a: ascii) : PrimString.string :=
  let c := char63_of_ascii a in
  PrimString.make one63 c.

(* Convert a Coq `string` into a `PrimString.string` by structural recursion *)
Fixpoint string_to_pstring (s: string) : PrimString.string :=
  match s with
  | EmptyString =>
      PrimString.make zero63 (char63_of_ascii "0"%char)
  | String a rest =>
      PrimString.cat (pstring_of_char a)
                     (string_to_pstring rest)
  end.

(* ------------------------------------------------------------------- *)
(* Generic list‐joining utility *)
Fixpoint pp_list {A:Type} (sep: string)
         (pp: A → PrimString.string)
         (l: list A) : PrimString.string :=
  match l with
  | [] => string_to_pstring ""
  | x :: xs =>
    let init := pp x in
    fold_left
      (fun acc y =>
         PrimString.cat
           (PrimString.cat acc (string_to_pstring sep))
           (pp y))
      xs init
  end.

(* ------------------------------------------------------------------- *)
(* High‐level stubs for sub‐printers; to be implemented later *)
Parameter pp_expr           : Expr → PrimString.string.         (* TOFIXLATER *)
Parameter pp_var_decl       : VarDecl → PrimString.string.      (* TOFIXLATER *)
Parameter pp_switch_branch  : SwitchBranch → PrimString.string. (* TOFIXLATER *)

(* ------------------------------------------------------------------- *)
(* Skeleton pretty‐printer for C++ statements *)
Fixpoint pp_stmt (s: Stmt) : PrimString.string :=
  match s with
  | Sseq ss       => string_to_pstring "{…}"
  | Sdecl ds      => string_to_pstring "decl …"
  | Sif _ _ _ _   => string_to_pstring "if (…) …"
  | Sif_consteval _ _ => string_to_pstring "if constexpr …"
  | Swhile _ _ _  => string_to_pstring "while (…) …"
  | Sfor _ _ _ _  => string_to_pstring "for (…) …"
  | Sdo _ _       => string_to_pstring "do …"
  | Sswitch _ _ _ => string_to_pstring "switch (…) …"
  | Scase _       => string_to_pstring "case …"
  | Sdefault      => string_to_pstring "default:"
  | Sbreak        => string_to_pstring "break;"
  | Scontinue     => string_to_pstring "continue;"
  | Sreturn _     => string_to_pstring "return …;"
  | Sexpr _       => string_to_pstring "expr;"
  | Sattr _ _     => string_to_pstring "[[…]]"
  | Sasm _ _ _ _ _=> string_to_pstring "asm(…);"
  | Slabeled _ _  => string_to_pstring "lbl: …"
  | Sgoto _       => string_to_pstring "goto …;"
  | Sunsupported _=> string_to_pstring "/* unsupported */"
  end.

