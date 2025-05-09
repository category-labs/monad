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
Module LLMSOLN.
Module LLMSOLN.
  Import bluerock.lang.cpp.syntax.core.
  Open Scope pstring_scope.

  (* convert Z to PrimString.string via existing showZ *)
  Definition Ztostring (z : Z) : string :=
    bluerock.lang.cpp.syntax.name_notation.printer.showN.showZ z.

  (* stub: convert byte‐string to PrimString.string *)
  Definition bs_to_string (b : BS.Bytestring_notations.bs) : string. Admitted. (* TOFIXLATER *)

  (* tiny generic fold over lists *)
  Fixpoint list_fold {A B:Type} (f: B->A->B) (l:list A) (b:B) : B :=
    match l with
    | [] => b
    | x::xs => list_fold f xs (f b x)
    end.

  (* printer for lists with separators *)
  Definition pp_list {A:Type} (ppA:A->string) (sep:string) (l:list A) : string :=
    match l with
    | [] => ""%pstring
    | x::xs =>
      list_fold (fun acc a => acc ++ sep ++ ppA a) xs (ppA x)
    end.

  (* structured‐binding printer: print just the names *)
  Definition pp_bind_name (b:BindingDecl) : string :=
    match b with
    | Bvar ln _ _   => ln
    | Bbind ln _ _  => ln
    end.

  (* print a switch‐branch *)
  Definition pp_switch_branch (br: bluerock.lang.cpp.syntax.preliminary.SwitchBranch) : string :=
    match br with
    | bluerock.lang.cpp.syntax.preliminary.Exact z =>
        "case " ++ Ztostring z ++ ":"%pstring
    | bluerock.lang.cpp.syntax.preliminary.Range z1 z2 =>
        "case " ++ Ztostring z1 ++ " ... " ++ Ztostring z2 ++ ":"%pstring
    end.

  Fixpoint pp_name (n : name) : string :=
    match n with
    | Ninst n0 args    => ""%pstring (* TOFIXLATER *)
    | Nglobal an       => ""%pstring
    | Ndependent t     => ""%pstring
    | Nscoped n0 an    => ""%pstring
    | Nunsupported s   => s
    end

  with pp_temp_arg (a : temp_arg) : string :=
    match a with
    | Atype t          => ""%pstring (* TOFIXLATER *)
    | Avalue e         => ""%pstring
    | Apack args       => ""%pstring
    | Atemplate n      => ""%pstring
    | Aunsupported s   => s
    end

  with pp_type (t : type) : string :=
    match t with
    | Tparam id                     => ""%pstring (* TOFIXLATER *)
    | Tresult_param id              => ""%pstring
    | Tresult_global n              => ""%pstring
    | Tresult_unop op t1            => ""%pstring
    | Tresult_binop op t1 t2        => ""%pstring
    | Tresult_call n args           => ""%pstring
    | Tresult_member_call n t0 args => ""%pstring
    | Tresult_parenlist t0 ts       => ""%pstring
    | Tresult_member t0 n           => ""%pstring
    | Tptr t0                       => ""%pstring
    | Tref t0                       => ""%pstring
    | Trv_ref t0                    => ""%pstring
    | Tnum r sgn                    => ""%pstring
    | Tchar_ ct                     => ""%pstring
    | Tvoid                         => ""%pstring
    | Tarray t0 n                   => ""%pstring
    | Tincomplete_array t0          => ""%pstring
    | Tvariable_array t0 sz         => ""%pstring
    | Tnamed n                      => ""%pstring
    | Tenum n                       => ""%pstring
    | Tfunction ft                  => ""%pstring
    | Tbool                         => ""%pstring
    | Tmember_pointer t0 t1         => ""%pstring
    | Tfloat_ ft                    => ""%pstring
    | Tqualified q t0               => ""%pstring
    | Tnullptr                      => ""%pstring
    | Tarch osz s                   => ""%pstring
    | Tdecltype e                   => ""%pstring
    | Texprtype e                   => ""%pstring
    | Tunsupported s                => s
    end

  with pp_expr (e : Expr) : string :=
    match e with
    | Eparam id                        => ""%pstring (* TOFIXLATER *)
    | Eunresolved_global n             => ""%pstring (* TOFIXLATER *)
    | Eunresolved_unop op e1           => ""%pstring (* TOFIXLATER *)
    | Eunresolved_binop op e1 e2       => ""%pstring (* TOFIXLATER *)
    | Eunresolved_call n es            => ""%pstring (* TOFIXLATER *)
    | Eunresolved_member_call n e0 es  => ""%pstring (* TOFIXLATER *)
    | Eunresolved_parenlist to es      => ""%pstring (* TOFIXLATER *)
    | Eunresolved_member e0 n          => ""%pstring (* TOFIXLATER *)
    | Evar ln t0                       => ""%pstring (* TOFIXLATER *)
    | Eenum_const n id                 => ""%pstring (* TOFIXLATER *)
    | Eglobal n t0                     => ""%pstring (* TOFIXLATER *)
    | Eglobal_member n t0              => ""%pstring (* TOFIXLATER *)
    | Echar c t0                       => ""%pstring (* TOFIXLATER *)
    | Estring s t0                     => ""%pstring (* TOFIXLATER *)
    | Eint z t0                        => ""%pstring (* TOFIXლATER*)
    | Ebool b                          => ""%pstring (* TOFIXلATER*)
    | Eunop op e0 t0                   => ""%pstring (* TOFIXლATER*)
    | Ebinop op e1 e2 t0               => ""%pstring (* TOFIXلATER*)
    | Ederef e0 t0                     => ""%pstring (* TOFIXלATER*)
    | Eaddrof e0                       => ""%pstring (* TOFIXลATER*)
    | Eassign e1 e2 t0                 => ""%pstring (* TOFIX․․later*)
    | Eassign_op op e1 e2 t0           => ""%pstring (* TOFIXlater*)
    | Epreinc e0 t0                    => ""%pstring (* TOFIXlater*)
    | Epostinc e0 t0                   => ""%pstring (* TOFIXlater*)
    | Epredec e0 t0                    => ""%pstring (* TOFIXlater*)
    | Epostdec e0 t0                   => ""%pstring (* TOFIXlATER*)
    (* ... remaining Expr constructors stubbed ... *)
    | Estmt s t0                       => ""%pstring (* TOFIXlater *)
    | Eva_arg e0 t0                    => ""%pstring (* TOFIXlater *)
    | Epseudo_destructor arrow t0 e0   => ""%pstring (* TOFIXlater *)
    | Earrayloop_init lvl1 src lvl2 lvl3 init t0 => ""%pstring (* TOFIXlater *)
    | Earrayloop_index lvl t0          => ""%pstring (* TOFIXlater *)
    | Eopaque_ref lvl t0               => ""%pstring (* TOFIXlater *)
    | Eunsupported s t0                => s
    | _                                => ""%pstring (* TOFIXLATER *)
    end

  with pp_stmt (s : Stmt) : string :=
    match s with
    | Sseq ss =>
        "{ " ++ pp_list pp_stmt "; "%pstring ss ++ " }"
    | Sdecl ds =>
        pp_list pp_vardecl ", "%pstring ds
    | Sif dvopt cond thn els =>
        let init_str := match dvopt with Some dv => pp_vardecl dv ++ "; " | None => "" end in
        "if (" ++ init_str ++ pp_expr cond ++ ") " ++ pp_stmt thn ++ " else " ++ pp_stmt els
    | Sif_consteval s1 s2 =>
        "if consteval " ++ pp_stmt s1 ++ " else " ++ pp_stmt s2
    | Swhile dvopt cond body =>
        let init_str := match dvopt with Some dv => pp_vardecl dv ++ "; " | None => "" end in
        "while (" ++ init_str ++ pp_expr cond ++ ") " ++ pp_stmt body
    | Sfor init cond incr body =>
        let init_str := match init with Some s0 => pp_stmt s0 | None => "" end in
        let cond_str := match cond with Some e0 => pp_expr e0 | None => "" end in
        let incr_str := match incr with Some e0 => pp_expr e0 | None => "" end in
        "for (" ++ init_str ++ "; " ++ cond_str ++ "; " ++ incr_str ++ ") " ++ pp_stmt body
    | Sdo body cond =>
        "do " ++ pp_stmt body ++ " while (" ++ pp_expr cond ++ ")"
    | Sswitch dvopt e0 body =>
        let init_str := match dvopt with Some dv => pp_vardecl dv ++ "; " | None => "" end in
        "switch (" ++ init_str ++ pp_expr e0 ++ ") " ++ pp_stmt body
    | Scase br =>
        pp_switch_branch br
    | Sdefault =>
        "default:"%pstring
    | Sbreak                         => "break;"%pstring
    | Scontinue                      => "continue;"%pstring
    | Sreturn eo                     =>
        match eo with Some e => "return " ++ pp_expr e ++ ";"%pstring | None => "return;"%pstring end
    | Sexpr e0                       => pp_expr e0 ++ ";"%pstring
    | Sgoto id                       => "goto " ++ id ++ ";"%pstring
    | Slabeled id s0                 => id ++ ": " ++ pp_stmt s0
    | Sattr attrs s0                 =>
        "__attribute__((" ++ pp_list (fun x=>x) ", " attrs ++ ")) " ++ pp_stmt s0
    | Sasm s volatile inputs outputs clobbers =>
        "asm " ++ (if volatile then "volatile " else "")
             ++ "(" ++ s ++ ")"%pstring
    | Sunsupported s                 => s
    end

  with pp_vardecl (d : VarDecl) : string :=
    match d with
    | Dvar ln t0 eo =>
        let base := pp_type t0 ++ " " ++ ln in
        match eo with Some e => base ++ " = " ++ pp_expr e | None => base end
    | Ddecompose e0 id binds =>
        "auto [" ++ pp_list pp_bind_name ", " binds ++ "] = " ++ pp_expr e0
    | Dinit thread ln t0 eo =>
        (if thread then "thread_safe "%pstring else "")
        ++ pp_type t0 ++ " " ++ pp_name ln
        ++ match eo with Some e => " = " ++ pp_expr e | None => "" end
    end

  with pp_binding (b : BindingDecl) : string :=
    match b with
    | Bvar ln _ _   => ln
    | Bbind ln _ _  => ln
    end

  with pp_cast (c : Cast) : string :=
    match c with
    | Cdependent t0               => ""%pstring (* TOFIXLATER *)
    | Cbitcast t0                 => ""%pstring (* TOFIXLATER *)
    | Clvaluebitcast t0           => ""%pstring (* TOFIXLATER *)
    | Cl2r                        => ""%pstring (* TOFIXLATER *)
    | Cl2r_bitcast t0             => ""%pstring (* TOFIXLATER *)
    | Cnoop t0                    => ""%pstring (* TOFIXLATER *)
    | Carray2ptr                  => ""%pstring (* TOFIXLATER *)
    | Cfun2ptr                    => ""%pstring (* TOFIXלATER *)
    | Cint2ptr t0                 => ""%pstring (* TOFIXלATER *)
    | Cptr2int t0                 => ""%pstring (* TOFIXלATER *)
    | Cptr2bool                   => ""%pstring (* TOFIXלATER *)
    | Cintegral t0                => ""%pstring (* TOFIXלATER *)
    | Cint2bool                   => ""%pstring (* TOFIXלATER *)
    | Cfloat2int t0               => ""%pstring (* TOFIXלATER *)
    | Cint2float t0               => ""%pstring (* TOFIXלATER *)
    | Cfloat t0                   => ""%pstring (* TOFIXלATER *)
    | Cnull2ptr t0                => ""%pstring (* TOFIXלATER *)
    | Cnull2memberptr t0          => ""%pstring (* TOFIXלATER *)
    | Cbuiltin2fun t0             => ""%pstring (* TOFIXלATER *)
    | C2void                      => ""%pstring (* TOFIXלATER *)
    | Cctor t0                    => ""%pstring (* TOFIXلATER *)
    | Cuser                       => ""%pstring (* TOFIXלATER *)
    | Cdynamic t0                 => ""%pstring (* TOFIXלATER *)
    | Cderived2base path t0       => ""%pstring (* TOFIXלATER *)
    | Cbase2derived path t0       => ""%pstring (* TOFIXלATER *)
    | Cunsupported bs t0          => bs_to_string bs
    end.
End LLMSOLN.
End LLMSOLN.

