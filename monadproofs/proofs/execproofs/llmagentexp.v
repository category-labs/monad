Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.
Open Scope pstring_scope.



(*
Write a Coq function to pretty print bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be `bluerock.lang.cpp.syntax.stmt.Stmt -> string`.
In the current context, `string` refers to `PrimString.string`, which is unusual in non-recent Coq developments. 
PrimString.string is a new type in Coq's core standard library. It axiomatizes primitive strings.
The scope delimiting key for  PrimString.string is pstring.
So, `(a ++ b)%pstring` appends `a:PrimString.string` and `b:PrimString.string`.
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.
 *)



Require Import Coq.Strings.PrimString.
Open Scope pstring.

(** Join a list with a separator, using printer p. *)
Fixpoint join {A} (sep : string) (p : A → string) (ls : list A) : string :=
  match ls with
  | [] =>
      ""%pstring
  | x :: xs =>
      match xs with
      | [] => p x
      | _  => p x ++ sep ++ join sep p xs
      end
  end.

(** Option‐printer *)
Definition p_option {A} (pp : A → string) (o : option A) : string :=
  match o with Some x => pp x | None => ""%pstring end.

(** * Leaf printers (some to be filled in later) *)
(** ident is just PrimString.string, so we can print it directly *)
Definition p_ident        (i : ident)                       : string := i.
Definition p_atomic_name  (an : atomic_name)                : string. Admitted. (* TOFIXLATER *)
Definition p_literal      (s : literal_string.t)            : string. Admitted.
Definition Z_to_string    (z : Z)                           : string. Admitted.
Definition p_char_type    (c : char_type)                   : string. Admitted.
Definition p_int_rank     (r : int_rank)                    : string. Admitted.
Definition p_signed       (sg : signed)                     : string. Admitted.
Definition p_float_type   (ft : float_type.t)               : string. Admitted.
Definition p_qualifiers   (q : type_qualifiers)             : string. Admitted.
Definition p_cast_style   (cs : cast_style.t)               : string. Admitted.
Definition p_atomic_op    (ao : AtomicOp)                   : string. Admitted.
Definition p_new_form     (nf : new_form)                   : string. Admitted.
Definition p_overload_op  (op : OverloadableOperator)       : string. Admitted.
Definition p_op_impl      (impl : operator_impl.t name type): string. Admitted.

(** * SwitchBranch printer **)
Definition p_switchbranch (br : SwitchBranch) : string :=
  match br with
  | Exact n    => "case " ++ Z_to_string n ++ ":"
  | Range l h  => "case " ++ Z_to_string l ++ " ... " ++ Z_to_string h ++ ":"
  end.

(** * Mutual printers for the big inductive family **)
Fixpoint p_name (n : name) : string :=
  match n with
  | Ninst base args    => p_name base ++ "<" ++ join "," p_temp_arg args ++ ">"
  | Nglobal an         => p_atomic_name an
  | Ndependent ty      => p_type ty
  | Nscoped sc an      => p_name sc ++ "::" ++ p_atomic_name an
  | Nunsupported s     => s
  end

with p_temp_arg (a : temp_arg) : string :=
  match a with
  | Atype ty           => p_type ty
  | Avalue e           => p_expr e
  | Apack args         => "pack<" ++ join "," p_temp_arg args ++ ">"
  | Atemplate nm       => p_name nm
  | Aunsupported s     => s
  end

with p_type (t : type) : string :=
  ""%pstring  (* TOFIXLATER *)

with p_expr (e : Expr) : string :=
  ""%pstring  (* TOFIXLATER *)

with p_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss           => "{" ++ join ";" p_stmt ss ++ "}"
  | Sdecl ds          => join ";" p_vardecl ds ++ ";"
  | Sif dv e1 th els  =>
      "if(" ++ p_option p_vardecl dv ++ p_expr e1 ++ ")" ++
      p_stmt th ++ "else" ++ p_stmt els
  | Sif_consteval t f =>
      "if consteval " ++ p_stmt t ++ " else " ++ p_stmt f
  | Swhile dv e bd    =>
      "while(" ++ p_option p_vardecl dv ++ p_expr e ++ ")" ++ p_stmt bd
  | Sfor ini cond post bd =>
      "for(" ++ p_option p_stmt ini ++ ";" ++
              p_option p_expr cond ++ ";" ++
              p_option p_expr post ++ ")" ++ p_stmt bd
  | Sdo bd e          => "do " ++ p_stmt bd ++ " while(" ++ p_expr e ++ ")"
  | Sswitch dv e bd   =>
      "switch(" ++ p_option p_vardecl dv ++ p_expr e ++ ")" ++ p_stmt bd
  | Scase br          => p_switchbranch br
  | Sdefault          => "default:"
  | Sbreak            => "break;"
  | Scontinue         => "continue;"
  | Sreturn oe        => "return " ++ p_option p_expr oe ++ ";"
  | Sexpr e           => p_expr e ++ ";"
  | Sattr attrs s'    => "[[" ++ join "," p_ident attrs ++ "]]" ++ p_stmt s'
  | Sasm str vol inps outs clob =>
      let vol_s := if vol then "volatile "%pstring else ""%pstring in
      "asm " ++ vol_s ++ "(" ++ str ++
      " : " ++ join "," (fun pr => match pr with (id,e) => p_ident id ++ " = " ++ p_expr e end) outs ++
      " : " ++ join "," (fun pr => match pr with (id,e) => p_ident id ++ " = " ++ p_expr e end) inps ++
      " : " ++ join "," p_ident clob ++
      ");"
  | Slabeled lbl s'    => lbl ++ ":" ++ p_stmt s'
  | Sgoto lbl         => "goto " ++ lbl ++ ";"
  | Sunsupported s    => s
  end

with p_vardecl (d : VarDecl) : string :=
  match d with
  | Dvar ln ty init =>
      p_type ty ++ " " ++ ln ++
      p_option (fun e => " = " ++ p_expr e) init

  | Ddecompose e _ binds =>
      "auto [" ++ join "," p_bindingdecl binds ++ "] = " ++ p_expr e

  | Dinit thread nm ty init =>
      (if thread then "thread " else "") ++
      p_type ty ++ " " ++ p_name nm ++
      p_option (fun e => " = " ++ p_expr e) init
  end

with p_bindingdecl (b : BindingDecl) : string :=
  match b with
  | Bvar ln ty e  => p_type ty ++ " " ++ ln ++ " = " ++ p_expr e
  | Bbind ln ty e => p_type ty ++ " " ++ ln ++ " = " ++ p_expr e
  end

with p_cast (c : Cast) : string :=
  "<cast>"               (* TOFIXLATER *).

(** Top‐level entry point **)
Definition pretty_stmt (s : Stmt) : string := p_stmt s.



