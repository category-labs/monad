## User 8

# General Background
This is a Coq programming task. First, some general guidelines about Coq programming tasks.

## Admitting holes (defer less critical/important parts)
Complex Coq programs are often written incrementally. 
Coq allows us to "admit" helper functions temporarily so that they can be defined later.
However, in that case, you need to come up with the type of the helper function. 
For example, you admit a helper function to convert a Z to a String.string, as follows:

```coq
Definition Ztostring (z: Z) : String.string. Admitted. (* TOFIXLATER *)
```
This mechanism allows you to get the higher-level details right before implementing the low-level obvious details.
Do not forget the "TOFIXLATER" comment, as this will be used to find the holes to fill in later.

Sometimes you cannot leave some holes for later because that may jeopardize Coq's termination checker for recursive functions, or the hole may need to be defined simultaneously with what you are currently defining. These issues are explained later in this tutorial.

## Error Messages
You are talking to an automated bot that will process your responses. 
If the Coq program you emit has errors, this bot will respond with the errors emitted by Coq.
Here are some general tips to avoid errors:
1. Use qualified names to avoid conflicts
2. Do not make any assumptions about which notation scopes are open. For example, if you mean `Z.add 1 2`, write `(1+2)%Z` instead.

## Coq Vernacular Queries instead of Hallucinations
If you are not sure about the exact name of a definition/fixpoint/inductive in the standard library or the libraries available to you can issue Coq queries to get more information about the available context. Some of the widely used queries are `Search`/`About`/`Check`/`Locate`. Here are some examples of search:

Search (nat -> nat). (* search the library for items of type nat -> nat *)

Search (nat -> list ?a -> list ?a). (* unification variables can be used to constrain occurrences: e.g. here the 2 occurrences of ?a must match the same term *)


Search "add". (* Search all definitions whose name contains "add" *)

Search (nat -> nat -> nat) "add" -"mul". (* Search all functions of type nat->nat and exclude functions whose names contain "add" but not "mul" *)

About Nat.add (* show documentation for an item *)

Check (Nat.add 1 1). (* check type of a term *)

Locate nat. (* print the possible fully qualified name(s) of `nat`. unless the user defined their own `nat` type, this will print `Corelib.Init.Datatypes.nat` . this will print multiple items if there are several items whose fully qualified names have `nat` as the leaf, e.g. `A.nat`, `Corelib.Init.Datatypes.nat`. It would also print shorter names for each fully qualified name. The shorter name depends on the set and order of Imports in the current file. When writing Coq code, you should refer to the located item by a name not any shorter than the shorter name mentioned here: the longer the better as that is robust to moving code around where the order of imports are different. *)

`Search`: can return too many items unless you chose a fairly discriminative query.
However, don't use the `Search ... in module` syntax which only searches in a particular module: instead, search in all modules by not specifying the `in` part.

Queries other than `Locate` need the references to definitions/inductives to be sufficiently qualified depending on the set of `Import`s. For example, you may need to say `A.foo` instead of just `foo` if you havent `Import`ed A. You can can use `Locate` to figure out the missing qualifications.

## Structural Recursion
Beyond the minor surface-level sytax differences, one of the main differences between Coq and other functional programming languages like Ocaml/Haskell is that functions must terminate for every possible argument(s). For example, functions of type `nat -> nat` cannot recurse forever. To ensure that, Coq follows a very simple approach, which unfortunately can make life harder for programmers.
For any `Fixpoint` definition, Coq must identify one argument that is decreasing in all recursive calls to the function being defined.
That argument must be of an `Inductive` type. A term `a` of an Inductive type `I` is a structural subterm of another term `b` if `a` is obtained by peeling off one or more constructors of the type `I`, possibly after computational reductions on open terms.

For example, a function to compute sum of a list of numbers can be defined as:
```gallina
Fixpoint listsum (l: list nat) : nat :=
  match l with
  | [] => 0
  | h::tl => h + listsum tl
  end.
```
The recursive call is on `tl` which is a structural subterm of `h::tl` which is the first argument (`l`). 

In contrast, the following definition, which is logically equivalent and also terminating, is not allowed by Coq:

```gallina
Fixpoint listsum (l: list nat) : nat :=
  match l with
  | [] => 0
  | h::tl => h + listsum (rev tl)
  end.
(*
Error:
Recursive definition of listsum is ill-formed.
In environment
listsum : list nat → nat
l : list nat
h : nat
tl : list nat
Recursive call to listsum has principal argument equal to "rev tl" instead of "tl".
Recursive definition is: "λ l : list nat, match l with
                                          | [] => 0
                                          | h :: tl => h + listsum (rev tl)
                                          end".
*)
```
`rev tl` is not a *structural* subterm of `h::tl`.

### Nested Inductives
Constructor arguments of some inductive types can themselves be of Inductive types, e.g. the last (`children`) argument below of the `node` constructor:
```gallina
Inductive Tree (T:Type) : Type :=
| node : T -> list (Tree T) (* children *) -> Tree T
| empty : Tree T.

Arguments node {_} _ _. (* make the T argument implicit *)
Arguments empty {_}. (* make the T argument implicit *)

```

In such cases, Coq allows us to define nested recursive functions, e.g.
```gallina
Fixpoint sum (t: Tree nat) : nat :=
  match t with
  | empty => 0
  | node nodeVal children => nodeVal + list_sum (List.map sum children)
  end.
```
Coq unfolds the definition of List.map, which is itself a structurally recursive function, to observe that `sum` is only 
called on subterms of `children` which itself is a subterm of `node nodeVal children`.
More concretely, Coq expands `nodeVal + list_sum (List.map sum children)` in the definition of `sum` to:
```gallina
nodeVal + list_sum ((fix map (l : list (Tree nat)) : list nat := match l with
                                                                   | [] => []
                                                                   | a :: l0 => sum a :: map l0
                                                                   end) children)
```
and then observes the only recursive call is on `a`, which is a subterm of `children`.

This unfolding of `List.map` is essential for Coq to figure out that this is valid structural recursion. 
If List.map were opaque or an `Axiom`, Coq would not be able to figure that out and Coq would reject that definition.
Thus, when leaving out admitted holes in the strategy in the previous section, please be mindful to not leave out holes around the recursive calls.

### Well-founded recursion
Coq provides the `Program Fixpoint` mechanism to workaround the rather restrictive syntactic criteria above. With `Program Fixpoint`
a user can define an arbitrary measure function but then Coq asks the user to prove that all recursive calls are on an argument with a smaller measure. You are already aware of this mechanism but you tend to overuse it. 
`Program Fixpoint` is not a primitive construct in Coq. Instead it encodes the user-supplied recursive function into a typicall 100x larger function that actually does *structural recursion* on proofs of measure decrements. Functions defined using `Program Fixpoint` often do not reduce well or at all, especially when the proof of measure reduction in recursive call arguments are opaque or have opaque subterms.
`Program Fixpoint` does prove unfolding equational lemmas (propositional equality) but that is not as convenient as reduction (definitional equality). So only `Program Fixpoint` if a structurally recursive formulation would be much much more complex.
Definitely PREFER IMPLEMENTING ADMITTED HOLES if they get in the way of Coq seeing structural recursion, instead of switching to `Program Fixpoint`.



## Mutual Inductives and Fixpoints (recursion)
If you want to define a function that recurses on inductive data, you typically use the `Fixpoint` keyword. If the inductive type is mutually indutive with other types, often the needed recursion is also mutually recursive. In such cases, you need to define your function using mutual Fixpoints. Below is an exampe:

```gallina
Inductive Expr : Type :=
| EConst : nat -> Expr
| EAdd : Expr -> Expr -> Expr
| ELet : string -> Com -> Expr -> Expr

with Com : Type :=
| CSkip : Com
| CAssign : string -> Expr -> Com
| CSeq : Com -> Com -> Com
| CIf : Expr -> Com -> Com -> Com.


Definition env := string -> nat.

(* Update environment *)
Definition update (ρ : env) (x : string) (v : nat) : env :=
  fun y => if String.eqb x y then v else ρ y.
  
Fixpoint eval_expr (ρ : env) (e : Expr) : nat :=
  match e with
  | EConst n => n
  | EAdd e1 e2 => eval_expr ρ e1 + eval_expr ρ e2
  | ELet x c e' =>
      let ρ' := eval_com ρ c in
      eval_expr ρ' e'
  end

with eval_com (ρ : env) (c : Com) : env :=
  match c with
  | CSkip => ρ
  | CAssign x e => update ρ x (eval_expr ρ e)
  | CSeq c1 c2 => let ρ' := eval_com ρ c1 in eval_com ρ' c2
  | CIf e c1 c2 =>
      if Nat.eqb (eval_expr ρ e) 0 then eval_com ρ c2 else eval_com ρ c1
  end.
```
In the above example, `eval_expr` calls `eval_com` (`ELet` case) and `eval_com` calls `eval_expr` (`CAssign` case).
Thus, neither of these functions can be defined before the other and they need to be defined together, using mutual recursion.
WHILE DECIDING WHAT TO LEAVE ADMITTED FOR LATER, ENSURE THAT WHAT YOU DECIDE TO LEAVE FOR LATER DOESNT NEED TO BE DEFINED MUTUALLY RECURSIVELY WITH WHAT YOU ARE CURRENTLY DEFINING.

## Common mistakes

In Coq, string escaping works non-intuitively. 
You would expect the following to define a string containing just the double quote character.

```gallina
Definition doubleQuote : String.string := "\"".
```

But that is not valid Coq syntax. Instead, the following works:
```gallina
Definition doubleQuote : String.string := """".
Compute (String.length doubleQuote). (* returns 1 *)
```
If this is confusing, you can just add the above `doubleQuote` definition and use it
when producing strings.

# Current Task
Write a Coq function to pretty print bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be `bluerock.lang.cpp.syntax.stmt.Stmt -> string`.
In the current context, `string` refers to `PrimString.string`, which is unusual in non-recent Coq developments. 
PrimString.string is a new type in Coq's core standard library. It axiomatizes primitive strings.
It is different from Stdlib.Strings.String.string, which are the non-primitive strings that have been in the Coq stdlib for decades.
The are slower so I avoid using them in this application where speed is important.


# Response Format (IMPORTANT)
You can either give me the answer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```. 
If you do not follow this format, my automated engine cannot parse your response.
An example of a valid response is:
```coqquery
Print Stmt.
```
An example of an answer (not to the the current task) is:
```gallina
Definition foo : nat := 1+2.
```

Please include exactly one query in a ```coqquery block.

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasn't available in the queries you have issued so far.


## Assistant 7

We need to see the exact constructors of `bluerock.lang.cpp.syntax.stmt.Stmt` (and its mutually defined siblings) before writing the pretty‐printer. Since we don’t yet know its form, let’s inspect it:

```coqquery
Print bluerock.lang.cpp.syntax.stmt.Stmt.
```

## User 9

Notation Stmt := Stmt

Inductive name' : Set :=
    Ninst : name → list temp_arg → name
  | Nglobal : atomic_name → name
  | Ndependent : type → name
  | Nscoped : name → atomic_name → name
  | Nunsupported : string → name
  with temp_arg' : Set :=
    Atype : type → temp_arg
  | Avalue : Expr → temp_arg
  | Apack : list temp_arg → temp_arg
  | Atemplate : name → temp_arg
  | Aunsupported : string → temp_arg
  with type' : Set :=
    Tparam : ident → type
  | Tresult_param : ident → type
  | Tresult_global : name → type
  | Tresult_unop : RUnOp → type → type
  | Tresult_binop : RBinOp → type → type → type
  | Tresult_call : name → list type → type
  | Tresult_member_call : name → type → list type → type
  | Tresult_parenlist : type → list type → type
  | Tresult_member : type → name → type
  | Tptr : type → type
  | Tref : type → type
  | Trv_ref : type → type
  | Tnum : int_rank → signed → type
  | Tchar_ : char_type → type
  | Tvoid : type
  | Tarray : type → N → type
  | Tincomplete_array : type → type
  | Tvariable_array : type → Expr → type
  | Tnamed : name → type
  | Tenum : name → type
  | Tfunction : function_type_ type → type
  | Tbool : type
  | Tmember_pointer : type → type → type
  | Tfloat_ : float_type.t → type
  | Tqualified : type_qualifiers → type → type
  | Tnullptr : type
  | Tarch : option bitsize → string → type
  | Tdecltype : Expr → type
  | Texprtype : Expr → type
  | Tunsupported : string → type
  with Expr' : Set :=
    Eparam : ident → Expr
  | Eunresolved_global : name → Expr
  | Eunresolved_unop : RUnOp → Expr → Expr
  | Eunresolved_binop : RBinOp → Expr → Expr → Expr
  | Eunresolved_call : name → list Expr → Expr
  | Eunresolved_member_call : name → Expr → list Expr → Expr
  | Eunresolved_parenlist : option type → list Expr → Expr
  | Eunresolved_member : Expr → name → Expr
  | Evar : localname → type → Expr
  | Eenum_const : name → ident → Expr
  | Eglobal : name → type → Expr
  | Eglobal_member : name → type → Expr
  | Echar : N → type → Expr
  | Estring : literal_string.t → type → Expr
  | Eint : Z → type → Expr
  | Ebool : bool → Expr
  | Eunop : UnOp → Expr → type → Expr
  | Ebinop : BinOp → Expr → Expr → type → Expr
  | Ederef : Expr → type → Expr
  | Eaddrof : Expr → Expr
  | Eassign : Expr → Expr → type → Expr
  | Eassign_op : BinOp → Expr → Expr → type → Expr
  | Epreinc : Expr → type → Expr
  | Epostinc : Expr → type → Expr
  | Epredec : Expr → type → Expr
  | Epostdec : Expr → type → Expr
  | Eseqand : Expr → Expr → Expr
  | Eseqor : Expr → Expr → Expr
  | Ecomma : Expr → Expr → Expr
  | Ecall : Expr → list Expr → Expr
  | Eexplicit_cast : cast_style.t → type → Expr → Expr
  | Ecast : Cast → Expr → Expr
  | Emember : bool → Expr → atomic_name → bool → type → Expr
  | Emember_ignore : bool → Expr → Expr → Expr
  | Emember_call : bool → MethodRef_ name type Expr → Expr → list Expr → Expr
  | Eoperator_call : OverloadableOperator → operator_impl.t name type → list Expr → Expr
  | Esubscript : Expr → Expr → type → Expr
  | Esizeof : type + Expr → type → Expr
  | Ealignof : type + Expr → type → Expr
  | Eoffsetof : type → ident → type → Expr
  | Econstructor : name → list Expr → type → Expr
  | Elambda : name → list Expr → Expr
  | Eimplicit : Expr → Expr
  | Eimplicit_init : type → Expr
  | Eif : Expr → Expr → Expr → type → Expr
  | Eif2 : N → Expr → Expr → Expr → Expr → type → Expr
  | Ethis : type → Expr
  | Enull : Expr
  | Einitlist : list Expr → option Expr → type → Expr
  | Einitlist_union : atomic_name → option Expr → type → Expr
  | Enew : name * type → list Expr → new_form → type → option Expr → option Expr → Expr
  | Edelete : bool → name → Expr → type → Expr
  | Eandclean : Expr → Expr
  | Ematerialize_temp : Expr → ValCat → Expr
  | Eatomic : AtomicOp → list Expr → type → Expr
  | Estmt : Stmt → type → Expr
  | Eva_arg : Expr → type → Expr
  | Epseudo_destructor : bool → type → Expr → Expr
  | Earrayloop_init : N → Expr → N → N → Expr → type → Expr
  | Earrayloop_index : N → type → Expr
  | Eopaque_ref : N → type → Expr
  | Eunsupported : string → type → Expr
  with Stmt' : Set :=
    Sseq : list Stmt → Stmt
  | Sdecl : list VarDecl → Stmt
  | Sif : option VarDecl → Expr → Stmt → Stmt → Stmt
  | Sif_consteval : Stmt → Stmt → Stmt
  | Swhile : option VarDecl → Expr → Stmt → Stmt
  | Sfor : option Stmt → option Expr → option Expr → Stmt → Stmt
  | Sdo : Stmt → Expr → Stmt
  | Sswitch : option VarDecl → Expr → Stmt → Stmt
  | Scase : SwitchBranch → Stmt
  | Sdefault : Stmt
  | Sbreak : Stmt
  | Scontinue : Stmt
  | Sreturn : option Expr → Stmt
  | Sexpr : Expr → Stmt
  | Sattr : list ident → Stmt → Stmt
  | Sasm : string → bool → list (ident * Expr) → list (ident * Expr) → list ident → Stmt
  | Slabeled : ident → Stmt → Stmt
  | Sgoto : ident → Stmt
  | Sunsupported : string → Stmt
  with VarDecl' : Set :=
    Dvar : localname → type → option Expr → VarDecl
  | Ddecompose : Expr → ident → list BindingDecl → VarDecl
  | Dinit : bool → name → type → option Expr → VarDecl
  with BindingDecl' : Set :=
    Bvar : localname → type → Expr → BindingDecl | Bbind : localname → type → Expr → BindingDecl
  with Cast' : Set :=
    Cdependent : type → Cast
  | Cbitcast : type → Cast
  | Clvaluebitcast : type → Cast
  | Cl2r : Cast
  | Cl2r_bitcast : type → Cast
  | Cnoop : type → Cast
  | Carray2ptr : Cast
  | Cfun2ptr : Cast
  | Cint2ptr : type → Cast
  | Cptr2int : type → Cast
  | Cptr2bool : Cast
  | Cintegral : type → Cast
  | Cint2bool : Cast
  | Cfloat2int : type → Cast
  | Cint2float : type → Cast
  | Cfloat : type → Cast
  | Cnull2ptr : type → Cast
  | Cnull2memberptr : type → Cast
  | Cbuiltin2fun : type → Cast
  | C2void : Cast
  | Cctor : type → Cast
  | Cuser : Cast
  | Cdynamic : type → Cast
  | Cderived2base : list type → type → Cast
  | Cbase2derived : list type → type → Cast
  | Cunsupported : bs → type → Cast.

Arguments Ninst c%_cpp_name_scope _%_list_scope
Arguments Nglobal c
Arguments Ndependent t%_cpp_type_scope
Arguments Nscoped n%_cpp_name_scope c
Arguments Nunsupported _%_pstring_scope
Arguments Atype _%_cpp_type_scope
Arguments Avalue _%_CPP_expr_scope
Arguments Apack _%_list_scope
Arguments Atemplate _%_cpp_name_scope
Arguments Aunsupported _%_pstring_scope
Arguments Tparam _%_pstring_scope
Arguments Tresult_param _%_pstring_scope
Arguments Tresult_global on%_cpp_name_scope
Arguments Tresult_unop _ _%_cpp_type_scope
Arguments Tresult_binop _ (_ _)%_cpp_type_scope
Arguments Tresult_call on%_cpp_name_scope _%_list_scope
Arguments Tresult_member_call on%_cpp_name_scope _%_cpp_type_scope _%_list_scope
Arguments Tresult_parenlist _%_cpp_type_scope _%_list_scope
Arguments Tresult_member _%_cpp_type_scope _%_cpp_name_scope
Arguments Tptr t%_cpp_type_scope
Arguments Tref t%_cpp_type_scope
Arguments Trv_ref t%_cpp_type_scope
Arguments Tnum sz sgn
Arguments Tarray t%_cpp_type_scope n%_N_scope
Arguments Tincomplete_array t%_cpp_type_scope
Arguments Tvariable_array t%_cpp_type_scope e%_CPP_expr_scope
Arguments Tnamed gn%_cpp_name_scope
Arguments Tenum gn%_cpp_name_scope
Arguments Tfunction t
Arguments Tmember_pointer (gn t)%_cpp_type_scope
Arguments Tqualified (q t)%_cpp_type_scope
Arguments Tarch osz name%_pstring_scope
Arguments Tdecltype _%_CPP_expr_scope
Arguments Texprtype _%_CPP_expr_scope
Arguments Tunsupported _%_pstring_scope
Arguments Eparam _%_pstring_scope
Arguments Eunresolved_global _%_cpp_name_scope
Arguments Eunresolved_unop _ e%_CPP_expr_scope
Arguments Eunresolved_binop _ (l r)%_CPP_expr_scope
Arguments Eunresolved_call on%_cpp_name_scope _%_list_scope
Arguments Eunresolved_member_call on%_cpp_name_scope _%_CPP_expr_scope _%_list_scope
Arguments Eunresolved_parenlist _ _%_list_scope
Arguments Eunresolved_member _%_CPP_expr_scope _%_cpp_name_scope
Arguments Evar _%_pstring_scope _%_cpp_type_scope
Arguments Eenum_const gn%_cpp_name_scope _%_pstring_scope
Arguments Eglobal on%_cpp_name_scope _%_cpp_type_scope
Arguments Eglobal_member gn%_cpp_name_scope ty%_cpp_type_scope
Arguments Echar c%_N_scope t%_cpp_type_scope
Arguments Estring s t%_cpp_type_scope
Arguments Eint n%_Z_scope t%_cpp_type_scope
Arguments Ebool b%_bool_scope
Arguments Eunop (op e)%_CPP_expr_scope t%_cpp_type_scope
Arguments Ebinop (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Ederef e%_CPP_expr_scope t%_cpp_type_scope
Arguments Eaddrof e%_CPP_expr_scope
Arguments Eassign (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eassign_op (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Epreinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epostinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epredec e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epostdec e%_CPP_expr_scope t%_cpp_type_scope
Arguments Eseqand (e1 e2)%_CPP_expr_scope
Arguments Eseqor (e1 e2)%_CPP_expr_scope
Arguments Ecomma (e1 e2)%_CPP_expr_scope
Arguments Ecall f%_CPP_expr_scope es%_list_scope
Arguments Eexplicit_cast c _%_cpp_type_scope e%_CPP_expr_scope
Arguments Ecast c e%_CPP_expr_scope
Arguments Emember arrow%_bool_scope obj%_CPP_expr_scope f mut%_bool_scope t%_cpp_type_scope
Arguments Emember_ignore arrow%_bool_scope (obj res)%_CPP_expr_scope
Arguments Emember_call arrow%_bool_scope method obj%_CPP_expr_scope args%_list_scope
Arguments Eoperator_call _ _ _%_list_scope
Arguments Esubscript (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Esizeof _ t%_cpp_type_scope
Arguments Ealignof _ t%_cpp_type_scope
Arguments Eoffsetof gn%_cpp_type_scope _%_pstring_scope t%_cpp_type_scope
Arguments Econstructor on%_cpp_name_scope args%_list_scope t%_cpp_type_scope
Arguments Elambda _%_cpp_name_scope captures%_list_scope
Arguments Eimplicit e%_CPP_expr_scope
Arguments Eimplicit_init t%_cpp_type_scope
Arguments Eif (e1 e2 e3)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eif2 n%_N_scope (common cond thn els)%_CPP_expr_scope _%_cpp_type_scope
Arguments Ethis t%_cpp_type_scope
Arguments Einitlist args%_list_scope default t%_cpp_type_scope
Arguments Einitlist_union _ _ t%_cpp_type_scope
Arguments Enew new_fn new_args%_list_scope pass_align alloc_ty%_cpp_type_scope array_size init
Arguments Edelete is_array%_bool_scope del_fn%_cpp_name_scope arg%_CPP_expr_scope deleted_type%_cpp_type_scope
Arguments Eandclean e%_CPP_expr_scope
Arguments Ematerialize_temp e%_CPP_expr_scope vc
Arguments Eatomic op%_pstring_scope args%_list_scope t%_cpp_type_scope
Arguments Estmt _%_CPP_stmt_scope _%_cpp_type_scope
Arguments Eva_arg e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epseudo_destructor is_arrow%_bool_scope t%_cpp_type_scope e%_CPP_expr_scope
Arguments Earrayloop_init oname%_N_scope src%_CPP_expr_scope (level length)%_N_scope init%_CPP_expr_scope t%_cpp_type_scope
Arguments Earrayloop_index level%_N_scope t%_cpp_type_scope
Arguments Eopaque_ref name%_N_scope t%_cpp_type_scope
Arguments Eunsupported s%_pstring_scope t%_cpp_type_scope
Arguments Sseq _%_list_scope
Arguments Sdecl _%_list_scope
Arguments Sif _ _%_CPP_expr_scope (_ _)%_CPP_stmt_scope
Arguments Sif_consteval (_ _)%_CPP_stmt_scope
Arguments Swhile _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments Sfor _ _ _ _%_CPP_stmt_scope
Arguments Sdo _%_CPP_stmt_scope _%_CPP_expr_scope
Arguments Sswitch _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments Sexpr _%_CPP_expr_scope
Arguments Sattr _%_list_scope _%_CPP_stmt_scope
Arguments Sasm _%_pstring_scope volatile%_bool_scope (inputs outputs clobbers)%_list_scope
Arguments Slabeled _%_pstring_scope _%_CPP_stmt_scope
Arguments Sgoto _%_pstring_scope
Arguments Sunsupported _%_pstring_scope
Arguments Dvar name%_pstring_scope _%_cpp_type_scope init
Arguments Ddecompose _%_CPP_expr_scope anon_var%_pstring_scope _%_list_scope
Arguments Dinit thread_safe%_bool_scope name%_cpp_name_scope _%_cpp_type_scope init
Arguments Bvar name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments Bbind name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments Cdependent _%_cpp_type_scope
Arguments Cbitcast _%_cpp_type_scope
Arguments Clvaluebitcast _%_cpp_type_scope
Arguments Cl2r_bitcast _%_cpp_type_scope
Arguments Cnoop _%_cpp_type_scope
Arguments Cint2ptr _%_cpp_type_scope
Arguments Cptr2int _%_cpp_type_scope
Arguments Cintegral _%_cpp_type_scope
Arguments Cfloat2int _%_cpp_type_scope
Arguments Cint2float _%_cpp_type_scope
Arguments Cfloat _%_cpp_type_scope
Arguments Cnull2ptr _%_cpp_type_scope
Arguments Cnull2memberptr _%_cpp_type_scope
Arguments Cbuiltin2fun _%_cpp_type_scope
Arguments Cctor _%_cpp_type_scope
Arguments Cdynamic to%_cpp_type_scope
Arguments Cderived2base path%_list_scope END%_cpp_type_scope
Arguments Cbase2derived path%_list_scope END%_cpp_type_scope
Arguments Cunsupported _%_bs_scope _%_cpp_type_scope

## Assistant 8

I need to know what string‐concat operator is available for the primitive `string` (i.e. `PrimString.string`) so I can assemble sub‐strings in the pretty‐printer. This isn’t evident yet, so let me look up the usual `++` notation:

```coqquery
Search (_ ++ _) (string -> string -> string).
```

## User 10

That query has no errors but returned an empty result. For `Search` queries, this means nothing in the current context matches the search criteria. Before assuming non-existence of what you are looking for, try relaxing some constraints. Consider the possibility of argument order being different, or names being different (e.g. `toString` vs `to_string` vs `print` vs `showString`). Make the most minimal assumptions about how stuff is named.

## Assistant 9

I expect the `String` module’s `append` function works on the primitive `string` (i.e. `PrimString.string`), so we can concatenate pieces via `String.append`. Let me confirm:

```coqquery
Check String.append.
```

## User 11

String.app
     : String.string → String.string → String.string

## Assistant 10

I’ll provide a lightweight pretty‐printer for `Stmt` that focuses on statement structure and leaves expression and variable‐decl printing to admitted stubs (marked `TOFIXLATER`).  We use a small list‐printer and only recurse structurally on `Stmt`.  Once the expression and decl printers are filled in, this will give a working `pp_stmt : Stmt → string`.

```gallina
Require Import Coq.Strings.PrimString.
Import String.StringSyntax.

(* stubs for sub-printers *)
Definition pp_expr (e : Expr) : string. Admitted.  (* TOFIXLATER *)
Definition pp_vardecl (d : VarDecl) : string. Admitted.  (* TOFIXLATER *)

(* a small list‐printer combinator *)
Fixpoint pp_list {A} (ppA : A → string) (sep : string) (l : list A) : string :=
  match l with
  | [] => ""
  | [x] => ppA x
  | x :: xs => String.app (ppA x) (String.app sep (pp_list ppA sep xs))
  end.

(* two mutually recursive functions for printing Stmt and list of Stmt *)
Fixpoint pp_stmt_list (l : list Stmt) : string :=
  match l with
  | [] => ""
  | [s] => pp_stmt s
  | s :: ss =>
      String.app (pp_stmt s)
                 (String.app "; " (pp_stmt_list ss))
  end

with pp_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      String.app "{ " (String.app (pp_stmt_list ss) " }")
  | Sdecl ds =>
      String.app (pp_list pp_vardecl "; " ds) ";"
  | Sif vd_opt cond then_br else_br =>
      let vd_s := match vd_opt with
                  | None => ""
                  | Some vd => String.app (pp_vardecl vd) " "
                  end in
      String.app "if ("
                 (String.app (pp_expr cond) ") "
                   (String.app vd_s
                     (String.app (pp_stmt then_br)
                       (String.app " else " (pp_stmt else_br)))))
  | Sif_consteval thn els =>
      String.app "if consteval " (String.app (pp_stmt thn) (String.app " else " (pp_stmt els)))
  | Swhile vd_opt cond body =>
      let vd_s := match vd_opt with
                  | None => ""
                  | Some vd => String.app (pp_vardecl vd) " "
                  end in
      String.app "while ("
                 (String.app (pp_expr cond) ") "
                   (String.app vd_s (pp_stmt body)))
  | Sfor init cond incr body =>
      let i1 := match init with None => "" | Some st => pp_stmt st end in
      let c2 := match cond with None => "" | Some e => pp_expr e end in
      let i3 := match incr with None => "" | Some e => pp_expr e end in
      String.app "for ("
                 (String.app i1
                   (String.app "; "
                     (String.app c2
                       (String.app "; "
                         (String.app i3 (String.app ") " (pp_stmt body)))))))
  | Sdo body cond =>
      String.app "do " (String.app (pp_stmt body) (String.app " while (" (String.app (pp_expr cond) ");")))
  | Sswitch vd_opt e br =>
      let vd_s := match vd_opt with None => "" | Some vd => String.app (pp_vardecl vd) " " end in
      String.app "switch (" (String.app (pp_expr e) (String.app ") " (String.app vd_s (pp_stmt br))))
  | Scase sb => String.app "case " (String.app (pp_expr sb.1) (String.app ": " (pp_stmt sb.2)))
  | Sdefault => "default:;"
  | Sbreak => "break;"
  | Scontinue => "continue;"
  | Sreturn eo =>
      String.app "return"
                 (match eo with None => ";" | Some e => String.app " " (String.app (pp_expr e) ";") end)
  | Sexpr e => String.app (pp_expr e) ";"
  | Sattr attrs st =>
      String.app "[["
                 (String.app (String.app (pp_list (fun i => i) ", ") "]] ")
                   (pp_stmt st))
  | Sasm txt vol inouts outouts clobs =>
      let in_s  := pp_list (fun io => String.app io.1 ("(" ++ pp_expr io.2 ++ ")")) ", " inouts in
      let out_s := pp_list (fun io => String.app io.1 ("(" ++ pp_expr io.2 ++ ")")) ", " outouts in
      let clob_s := pp_list (fun i => i) ", " clobs in
      String.app "asm "
                 (String.app txt
                   (String.app " "
                     (String.app (if vol then "volatile " else "")
                       (String.app "("
                         (String.app in_s
                           (String.app ") ("
                             (String.app out_s
                               (String.app ") {"
                                 (String.app clob_s "};")))))))))
  | Slabeled lbl st => String.app lbl (String.app ": " (pp_stmt st))
  | Sgoto lbl => String.app "goto " (String.app lbl ";")
  | Sunsupported txt => txt
  end.
```

## User 12

Toplevel input, characters 154-159:
>   | x :: xs => String.app (ppA x) (String.app sep (pp_list ppA sep xs))
>                            ^^^^^
Error:
In environment
pp_list : ∀ A : Type, (A → string) → string → list A → string
A : Type
ppA : A → string
sep : string
l : list A
x : A
xs : list A
a : A
l0 : list A
xs0 := a :: l0 : list A
The term "ppA x" has type "string" while it is expected to have type "String.string".


## Assistant 11

We need the primitive‐string concatenation function from `PrimString`. Let’s check its name:

```coqquery
Check PrimString.append.
```

## User 13

Toplevel input, characters 6-23:
> Check PrimString.append.
>       ^^^^^^^^^^^^^^^^^
Error: The reference PrimString.append was not found in the current environment.

## Assistant 12

`pp_list`’s result type is our primitive `string`, but `String.app` takes `String.string` (the old non-primitive strings). We need a concatenation for primitive `string`. 

That lives in the module `PrimitiveString`: 

```coqquery
Search _ (_ ^ _)%string.
```

## User 14

Nat.pow_1_r: ∀ a : nat, a ^ 1 = a
Nat.pow_0_r: ∀ a : nat, a ^ 0 = 1
Nat.pow_1_l: ∀ a : nat, 1 ^ a = 1
Nat.pow_le_mono_l: ∀ a b c : nat, a ≤ b → a ^ c ≤ b ^ c
Nat.pow_neg_r: ∀ a b : nat, b < 0 → a ^ b = 0
Nat.pow_0_l: ∀ a : nat, a ≠ 0 → 0 ^ a = 0
Nat.pow_gt_lin_r: ∀ a b : nat, 1 < a → b < a ^ b
Nat.pow_mul_r: ∀ a b c : nat, a ^ (b * c) = (a ^ b) ^ c
Nat.pow_2_r: ∀ a : nat, a ^ 2 = a * a
Nat.pow_succ_r': ∀ a b : nat, a ^ S b = a * a ^ b
Nat.shiftl_1_l: ∀ n : nat, Nat.shiftl 1 n = 2 ^ n
Nat.pow_nonzero: ∀ a b : nat, a ≠ 0 → a ^ b ≠ 0
RIneq.pow_INR: ∀ m n : nat, Raxioms.INR (m ^ n) = Rpow_def.pow (Raxioms.INR m) n
Nat.pow_mul_l: ∀ a b c : nat, (a * b) ^ c = a ^ c * b ^ c
Nat2N.inj_pow: ∀ n n' : nat, N.of_nat (n ^ n') = (N.of_nat n ^ N.of_nat n')%N
Nat.ones_equiv: ∀ n : nat, Nat.ones n = Nat.pred (2 ^ n)
N2Nat.inj_pow: ∀ a a' : N, N.to_nat (a ^ a') = N.to_nat a ^ N.to_nat a'
Pos2Nat.inj_pow: ∀ p q : positive, Pos.to_nat (p ^ q) = Pos.to_nat p ^ Pos.to_nat q
Nat2Z.inj_pow: ∀ n m : nat, n ^ m = (n ^ m)%Z
Z2Nat.inj_pow: ∀ x y : nat, x ^ y = (x ^ y)%Z
Nat.pow_eq_0: ∀ a b : nat, b ≠ 0 → a ^ b = 0 → a = 0
Nat.pow_add_r: ∀ a b c : nat, a ^ (b + c) = a ^ b * a ^ c
Nat.pow2_bits_true: ∀ n : nat, Nat.testbit (2 ^ n) n = true
Nat.log2_pow2: ∀ a : nat, 0 ≤ a → Nat.log2 (2 ^ a) = a
Nat.pow_lower_bound: ∀ a b : nat, a ≠ 0 → 1 ≤ a ^ b
Nat.log2_up_pow2: ∀ a : nat, 0 ≤ a → Nat.log2_up (2 ^ a) = a
Nat.setbit_spec': ∀ a n : nat, Nat.setbit a n = Nat.lor a (2 ^ n)
Nat.shiftr_div_pow2: ∀ a n : nat, Nat.shiftr a n = a `div` 2 ^ n
Nat.pow_lt_mono_r: ∀ a b c : nat, 1 < a → b < c → a ^ b < a ^ c
Nat.clearbit_spec': ∀ a n : nat, Nat.clearbit a n = Nat.ldiff a (2 ^ n)
Nat.shiftl_mul_pow2: ∀ a n : nat, Nat.shiftl a n = a * 2 ^ n
Nat.odd_pow: ∀ a b : nat, b ≠ 0 → Nat.odd (a ^ b) = Nat.odd a
Nat.even_pow: ∀ a b : nat, b ≠ 0 → Nat.even (a ^ b) = Nat.even a
Nat.log2_up_succ_pow2: ∀ a : nat, 0 ≤ a → Nat.log2_up (S (2 ^ a)) = S a
Nat.pow_inj_l: ∀ a b c : nat, c ≠ 0 → a ^ c = b ^ c → a = b
Nat.pow_succ_r: ∀ a b : nat, 0 ≤ b → a ^ S b = a * a ^ b
Nat.pow2_bits_eqb: ∀ n m : nat, Nat.testbit (2 ^ n) m = (n =? m)
Nat.pow_le_mono_r: ∀ a b c : nat, a ≠ 0 → b ≤ c → a ^ b ≤ a ^ c
Nat.pow_lt_mono_r_iff: ∀ a b c : nat, 1 < a → b < c ↔ a ^ b < a ^ c
Nat.pow_lt_mono_l: ∀ a b c : nat, c ≠ 0 → a < b → a ^ c < b ^ c
Nat.pow_inj_r: ∀ a b c : nat, 1 < a → a ^ b = a ^ c → b = c
Nat.land_ones: ∀ a n : nat, Nat.land a (Nat.ones n) = a `mod` 2 ^ n
Nat.log2_lt_pow2: ∀ a b : nat, 0 < a → a < 2 ^ b ↔ Nat.log2 a < b
Nat.pow_gt_1: ∀ a b : nat, 1 < a → b ≠ 0 → 1 < a ^ b
Nat.log2_pred_pow2: ∀ a : nat, 0 < a → Nat.log2 (Nat.pred (2 ^ a)) = Nat.pred a
Nat.pow_eq_0_iff: ∀ a b : nat, a ^ b = 0 ↔ b ≠ 0 ∧ a = 0
Nat.log2_up_lt_pow2: ∀ a b : nat, 0 < a → 2 ^ b < a ↔ b < Nat.log2_up a
Nat.pow_le_mono_r_iff: ∀ a b c : nat, 1 < a → b ≤ c ↔ a ^ b ≤ a ^ c
Nat.pow_lt_mono_l_iff: ∀ a b c : nat, c ≠ 0 → a < b ↔ a ^ c < b ^ c
Nat.pow_le_mono_l_iff: ∀ a b c : nat, c ≠ 0 → a ≤ b ↔ a ^ c ≤ b ^ c
Nat.ones_mod_pow2: ∀ n m : nat, m ≤ n → Nat.ones n `mod` 2 ^ m = Nat.ones m
Nat.log2_le_pow2: ∀ a b : nat, 0 < a → 2 ^ b ≤ a ↔ b ≤ Nat.log2 a
Nat.log2_up_le_pow2: ∀ a b : nat, 0 < a → a ≤ 2 ^ b ↔ Nat.log2_up a ≤ b
Nat2Pos.inj_pow: ∀ n m : nat, m ≠ 0 → Pos.of_nat (n ^ m) = (Pos.of_nat n ^ Pos.of_nat m)%positive
Nat.pow_le_mono: ∀ a b c d : nat, a ≠ 0 → a ≤ c → b ≤ d → a ^ b ≤ c ^ d
Nat.log2_up_eq_succ_is_pow2: ∀ a : nat, Nat.log2_up (S a) = S (Nat.log2_up a) → ∃ b : nat, a = 2 ^ b
Nat.pow_add_lower: ∀ a b c : nat, c ≠ 0 → a ^ c + b ^ c ≤ (a + b) ^ c
Nat.pow2_bits_false: ∀ n m : nat, n ≠ m → Nat.testbit (2 ^ n) m = false
Znat.Z2Nat.inj_pow: ∀ n m : Z, (0 ≤ n)%Z → (0 ≤ m)%Z → Z.to_nat (n ^ m) = Z.to_nat n ^ Z.to_nat m
Nat.pow_lt_mono: ∀ a b c d : nat, 0 < a < c → 0 < b < d → a ^ b < c ^ d
Nat.ones_add: ∀ n m : nat, Nat.ones (m + n) = 2 ^ m * Nat.ones n + Nat.ones m
Nat.log2_eq_succ_is_pow2: ∀ a : nat, Nat.log2 (S a) = S (Nat.log2 a) → ∃ b : nat, S a = 2 ^ b
Nat.mul_pow2_bits_add: ∀ a n m : nat, Nat.testbit (a * 2 ^ n) (m + n) = Nat.testbit a m
Nat.div_pow2_bits: ∀ a n m : nat, Nat.testbit (a `div` 2 ^ n) m = Nat.testbit a (m + n)
Nat.testbit_spec': ∀ a n : nat, Nat.b2n (Nat.testbit a n) = (a `div` 2 ^ n) `mod` 2
Nat.ones_div_pow2: ∀ n m : nat, m ≤ n → Nat.ones n `div` 2 ^ m = Nat.ones (n - m)
Nat.mul_pow2_bits_low: ∀ a n m : nat, m < n → Nat.testbit (a * 2 ^ n) m = false
Nat.mod_pow2_bits_high: ∀ a n m : nat, n ≤ m → Nat.testbit (a `mod` 2 ^ n) m = false
Nat.mod_pow2_bits_low: ∀ a n m : nat, m < n → Nat.testbit (a `mod` 2 ^ n) m = Nat.testbit a m
length_list_power: ∀ [A B : Type] (l : list A) (l' : list B), length (list_power l l') = length l' ^ length l
Nat.log2_spec: ∀ n : nat, 0 < n → 2 ^ Nat.log2 n <= n < 2 ^ S (Nat.log2 n)
Nat.log2_log2_up_spec: ∀ a : nat, 0 < a → 2 ^ Nat.log2 a <= a <= 2 ^ Nat.log2_up a
Nat.pow_sub_r: ∀ a b c : nat, a ≠ 0 → c ≤ b → a ^ (b - c) = a ^ b `div` a ^ c
Nat.testbit_eqb: ∀ a n : nat, Nat.testbit a n = ((a `div` 2 ^ n) `mod` 2 =? 1)
Nat.pow_div_l: ∀ a b c : nat, b ≠ 0 → a `mod` b = 0 → (a `div` b) ^ c = a ^ c `div` b ^ c
Nat.mul_pow2_bits_high: ∀ a n m : nat, n ≤ m → Nat.testbit (a * 2 ^ n) m = Nat.testbit a (m - n)
Nat.log2_log2_up_exact: ∀ a : nat, 0 < a → Nat.log2 a = Nat.log2_up a ↔ ∃ b : nat, a = 2 ^ b
Nat.log2_up_mul_pow2: ∀ a b : nat, 0 < a → 0 ≤ b → Nat.log2_up (a * 2 ^ b) = b + Nat.log2_up a
Nat.log2_up_eq_succ_iff_pow2: ∀ a : nat, 0 < a → Nat.log2_up (S a) = S (Nat.log2_up a) ↔ ∃ b : nat, a = 2 ^ b
Nat.log2_mul_pow2: ∀ a b : nat, 0 < a → 0 ≤ b → Nat.log2 (a * 2 ^ b) = b + Nat.log2 a
Nat.log2_up_spec: ∀ a : nat, 1 < a → 2 ^ Nat.pred (Nat.log2_up a) < a <= 2 ^ Nat.log2_up a
Nat.log2_eq_succ_iff_pow2: ∀ a : nat, 0 < a → Nat.log2 (S a) = S (Nat.log2 a) ↔ ∃ b : nat, S a = 2 ^ b
Nat.testbit_false: ∀ a n : nat, Nat.testbit a n = false ↔ (a `div` 2 ^ n) `mod` 2 = 0
Nat.log2_unique: ∀ a b : nat, 0 ≤ b → 2 ^ b <= a < 2 ^ S b → Nat.log2 a = b
Nat.testbit_true: ∀ a n : nat, Nat.testbit a n = true ↔ (a `div` 2 ^ n) `mod` 2 = 1
vec_card: ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Finite A} (n : nat), card (vec A n) = card A ^ n
ClassicalDedekindReals.Qpower_2_invneg_le_pow: ∀ n : Z, (1 # Pos.of_nat (2 ^ Z.to_nat (- n)) <= 2 ^ n)%Q
Nat.log2_up_unique: ∀ a b : nat, 0 < b → 2 ^ Nat.pred b < a <= 2 ^ b → Nat.log2_up a = b
ClassicalDedekindReals.Qpower_2_neg_eq_natpow_inv: ∀ n : nat, (2 ^ (- n) == 1 # Pos.of_nat (2 ^ n))%Q
Nat.pow_add_upper: ∀ a b c : nat, c ≠ 0 → (a + b) ^ c ≤ 2 ^ Nat.pred c * (a ^ c + b ^ c)
Nat.add_nocarry_mod_lt_pow2: ∀ a b n : nat, Nat.land a b = 0 → a `mod` 2 ^ n + b `mod` 2 ^ n < 2 ^ n
Nat.add_nocarry_lt_pow2: ∀ a b n : nat, Nat.land a b = 0 → a < 2 ^ n → b < 2 ^ n → a + b < 2 ^ n
Nat.log2_unique': ∀ a b c : nat, 0 ≤ b → 0 <= c < 2 ^ b → a = 2 ^ b + c → Nat.log2 a = b
Nat.log2_spec_alt: ∀ a : nat, 0 < a → ∃ r : nat, a = 2 ^ Nat.log2 a + r ∧ 0 <= r < 2 ^ Nat.log2 a
Nat.testbit_unique: ∀ (a n : nat) (a0 : bool) (l h : nat), l < 2 ^ n → a = l + (Nat.b2n a0 + 2 * h) * 2 ^ n → Nat.testbit a n = a0
Nat.testbit_spec: ∀ a n : nat, ∃ l h : nat, 0 <= l < 2 ^ n ∧ a = l + (Nat.b2n (Nat.testbit a n) + 2 * h) * 2 ^ n
Nat.log2_iter_spec: ∀ k p q r : nat, 2 ^ S p = q + S r → r < 2 ^ p → let s := Nat.log2_iter k p q r in 2 ^ s <= k + q < 2 ^ S s
ClassicalDedekindReals.DRealQlimExp2:
  ∀ (x : ClassicalDedekindReals.DReal) (n : nat), {q : Q | (`x) q = true ∧ (`x) (q + (1 # Pos.of_nat (2 ^ n)))%Q = false}
list_card: ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Finite A} (n : nat), card {l : list A | length l = n} = card A ^ n

## Assistant 13

I need to see the contents of the `PrimString` module to find its concatenation function (and perhaps empty‐string). Let’s inspect it:

```coqquery
Print PrimString.
```

## User 15

Module PrimString := Struct  End

## Assistant 14

To find the primitive‐string concatenation operator, let’s locate the notation for `^` on `string`:

```coqquery
Locate "^".
```

## User 16

Notation "x ^ y" := (N.pow x y) (* x in scope _N_scope, y in scope _N_scope *) : N_scope (from Stdlib.NArith.BinNat)
Notation " q ^ z " := (Qpower q z) (* q in scope _Q_scope, z in scope _Z_scope *) : Q_scope (from Stdlib.QArith.QArith_base)
Notation "x ^ y" := (Z.pow x y) (* x in scope _Z_scope, y in scope _Z_scope *) : Z_scope (from Stdlib.ZArith.BinInt)
Notation "x ^ y" := (Nat.pow x y) (* x in scope _nat_scope, y in scope _nat_scope *) : nat_scope (default interpretation)
  (from Stdlib.Arith.PeanoNat)
Notation "x ^ y" := (Pos.pow x y) (* x in scope _positive_scope, y in scope _positive_scope *) : positive_scope (from Stdlib.PArith.BinPos)

## Assistant 15

I need to see what `string` refers to in our file: whether it’s `String.string` or `PrimString.string`. This will clarify the concatenation mismatch. Let’s ask:

```coqquery
About string.
```

## User 17

string : Set

string is not universe polymorphic
Expands to: Constant Corelib.Strings.PrimString.string
Declared in library Corelib.Strings.PrimString, line 5, characters 10-16

## Assistant 16

To find the primitive‐string concatenator, let’s search for any function of type `string → string → string` (where `string` is the primitive `PrimString.string`):

```coqquery
Search (string -> string -> string).
```

## User 18

printer.postfix: string → string → string
printer.prefix: string → string → string
cat: string → string → string

## Assistant 17

Here is the same pretty‐printer revised to use the primitive‐string `cat` for concatenation.  Once you fill in the `pp_expr` and `pp_vardecl` stubs, you will have a working `pp_stmt : Stmt → string`.

```gallina
Require Import Corelib.Strings.PrimString.
Open Scope string.

(* stubs for sub-printers *)
Definition pp_expr (e : Expr) : string. Admitted.  (* TOFIXLATER *)
Definition pp_vardecl (d : VarDecl) : string. Admitted.  (* TOFIXLATER *)

(* a small list‐printer combinator *)
Fixpoint pp_list {A} (ppA : A → string) (sep : string) (l : list A) : string :=
  match l with
  | [] => ""
  | [x] => ppA x
  | x :: xs => cat (ppA x) (cat sep (pp_list ppA sep xs))
  end.

(* mutually recursive printing of Stmt and list of Stmt *)
Fixpoint pp_stmt_list (l : list Stmt) : string :=
  match l with
  | [] => ""
  | [s] => pp_stmt s
  | s :: ss => cat (pp_stmt s) (cat "; " (pp_stmt_list ss))
  end

with pp_stmt (s : Stmt) : string :=
  match s with
  | Sseq ss =>
      cat "{ " (cat (pp_stmt_list ss) " }")
  | Sdecl ds =>
      cat (pp_list pp_vardecl "; " ds) ";"
  | Sif vd_opt cond thn els =>
      let vd_s := match vd_opt with
                  | None => ""
                  | Some vd => cat (pp_vardecl vd) " "
                  end in
      cat "if (" (cat (pp_expr cond) (cat ") " (cat vd_s (cat (pp_stmt thn) (cat " else " (pp_stmt els))))))
  | Sif_consteval thn els =>
      cat "if consteval " (cat (pp_stmt thn) (cat " else " (pp_stmt els)))
  | Swhile vd_opt cond body =>
      let vd_s := match vd_opt with
                  | None => ""
                  | Some vd => cat (pp_vardecl vd) " "
                  end in
      cat "while (" (cat (pp_expr cond) (cat ") " (cat vd_s (pp_stmt body))))
  | Sfor init cond incr body =>
      let i1 := match init with None => "" | Some st => pp_stmt st end in
      let c2 := match cond with None => "" | Some e => pp_expr e end in
      let i3 := match incr with None => "" | Some e => pp_expr e end in
      cat "for (" (cat i1 (cat "; " (cat c2 (cat "; " (cat i3 (cat ") " (pp_stmt body))))))
  | Sdo body cond =>
      cat "do " (cat (pp_stmt body) (cat " while (" (cat (pp_expr cond) ");")))
  | Sswitch vd_opt e br =>
      let vd_s := match vd_opt with None => "" | Some vd => cat (pp_vardecl vd) " " end in
      cat "switch (" (cat (pp_expr e) (cat ") " (cat vd_s (pp_stmt br))))
  | Scase sb =>
      cat "case " (cat (pp_expr sb.1) (cat ": " (pp_stmt sb.2)))
  | Sdefault => "default:;"
  | Sbreak => "break;"
  | Scontinue => "continue;"
  | Sreturn eo =>
      cat "return" (match eo with None => ";" | Some e => cat " " (cat (pp_expr e) ";") end)
  | Sexpr e => cat (pp_expr e) ";"
  | Sattr attrs st =>
      cat "[[" (cat (pp_list (fun i => i) ", ") (cat "]] " (pp_stmt st)))
  | Sasm txt vol inouts outouts clobs =>
      let in_s  := pp_list (fun io => cat io.1 (cat "(" (cat (pp_expr io.2) ")"))) ", " inouts in
      let out_s := pp_list (fun io => cat io.1 (cat "(" (cat (pp_expr io.2) ")"))) ", " outouts in
      let clob_s := pp_list (fun i => i) ", " clobs in
      cat "asm " (cat txt (cat " " (cat (if vol then "volatile " else "")
        (cat "(" (cat in_s (cat ") (" (cat out_s (cat ") {" (cat clob_s "};")))))))))
  | Slabeled lbl st => cat lbl (cat ": " (pp_stmt st))
  | Sgoto lbl => cat "goto " (cat lbl ";")
  | Sunsupported txt => txt
  end.
```

## User 19

Toplevel input, characters 1342-1344:
>   | Sdo body cond =>
>                   ^^
Error: Syntax error: ')' expected after [term level 200] (in [term]).


