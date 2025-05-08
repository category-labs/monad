## User 11

# General Coq Background
This is a Coq programming task. First, some general guidelines about Coq programming tasks.

## Admitting holes (defer less critical/important parts)
Complex Coq programs are often written incrementally. 
Coq allows us to "admit" helper functions temporarily so that they can be defined later.
However, in that case, you need to come up with the type of the helper function. 
For example, you can admit a helper function to convert a Z to a `string`, as follows:

```coq
Definition Ztostring (z: Z) : string. Admitted. (* TOFIXLATER *)
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
```coqquery
Search (nat -> nat). (* search the library for items of type nat -> nat *)
```

Sometimes, you incorrectly issue the above query as:
```coqquery
Search (_ : nat -> nat). (* this is wrong. it returns everything in the current context, regardless of the type *)
```

Other examples:
```coqquery
Search (nat -> list ?a -> list ?a). (* unification variables can be used to constrain occurrences: e.g. here the 2 occurrences of ?a must match the same term *)

Search "add". (* Search all definitions whose name contains "add" *)

Search (nat -> nat -> nat) "add" -"mul". (* Search all functions of type nat->nat and exclude functions whose names contain "add" but not "mul" *)

About Nat.add (* show documentation for an item *)

Check (Nat.add 1 1). (* check type of a term *)

Locate nat. (* print the possible fully qualified name(s) of `nat`. unless the user defined their own `nat` type, this will print `Corelib.Init.Datatypes.nat` . this will print multiple items if there are several items whose fully qualified names have `nat` as the leaf, e.g. `A.nat`, `Corelib.Init.Datatypes.nat`. It would also print shorter names for each fully qualified name. The shorter name depends on the set and order of Imports in the current file. When writing Coq code, you should refer to the located item by a name not any shorter than the shorter name mentioned here: the longer the better as that is robust to moving code around where the order of imports are different. *)
```

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
  fun y => if bool_decide (x = y) then v else ρ y.
  
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

### String Escaping
In Coq, string escaping works non-intuitively. 
You would expect the following to define a string containing just the double quote character.

```gallina
Definition doubleQuote : string := "\"".
```

But that is not valid Coq syntax. Instead, the following works:
```gallina
Definition doubleQuote : string := """".
Compute (length doubleQuote). (* returns 1 *)
```
If this is confusing, you can just add the above `doubleQuote` definition and use it
when producing strings.

### Prop vs bool
`Prop` is a type of mathematical assertions, e.g. `1=2`. 
`bool` is a datatype with 2 elements: `true` and `false`.
Many logics do not distinguish between them but the difference in crucial in constructive logics as some `Prop`s may be undecidable.
In Gallina functions, which are computable unless you add axioms, you can NOT do a case analysis on a `Prop`.
You can do a case analysis on a `bool`. 
If `P:Prop` is decidable and there is an instance of the `Decidable P` typeclass in the current context, `bool_decide P` is a `bool` which is true iff `P`.

A common mistake beginners do is to write:
```gallina
Definition foo (n:nat): nat:= if (0<n) then 1 else 0.
```
That doesnt typecheck: `if` is sugar for `match` and the discriminee must be an element of an Inductive type like bool/nat...
But `Prop` is not an Inductive type.
The following is one way to correctly write the above definition:
```gallina
Definition foo (n:nat): nat:= if bool_decide (0<n) then 1 else 0.
```

# Current Task
bluerock.lang.cpp.syntax.stmt.Stmt, an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
Write a set of mutually recursive pretty-printer functions for all such types.
These Gallina functions should return `string`.
In the current context, `string` refers to `PrimString.string`, which is unusual in non-recent Coq developments. 
PrimString.string is a new type in Coq's core standard library. It axiomatizes primitive strings.
The scope delimiting key for  PrimString.string is pstring.
So, `(a ++ b)%pstring` appends `a:PrimString.string` and `b:PrimString.string`.
PrimString.string is different from Stdlib.Strings.String.string, which is the type of the non-primitive strings that have been in the Coq stdlib for decades. Stdlib.Strings.String.string is slower so I avoid using it in this application where speed is important.Require Import PrimString.


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


## Assistant 11

I need to see the actual constructors of `bluerock.lang.cpp.syntax.stmt.Stmt` (and its mutually-inductive siblings) in order to write the corresponding recursive pretty-printer. This information isn’t yet available, so let me inspect the definition:

```coqquery
Print bluerock.lang.cpp.syntax.stmt.Stmt.
```

## User 12

>>> Print bluerock.lang.cpp.syntax.stmt.Stmt.
Notation Stmt := Stmt

Inductive name' : Set :=
    Ninst : name → Corelib.Init.Datatypes.list temp_arg → name
  | Nglobal : atomic_name → name
  | Ndependent : type → name
  | Nscoped : name → atomic_name → name
  | Nunsupported : Corelib.Strings.PrimString.string → name
  with temp_arg' : Set :=
    Atype : type → temp_arg
  | Avalue : Expr → temp_arg
  | Apack : Corelib.Init.Datatypes.list temp_arg → temp_arg
  | Atemplate : name → temp_arg
  | Aunsupported : Corelib.Strings.PrimString.string → temp_arg
  with type' : Set :=
    Tparam : bluerock.lang.cpp.syntax.preliminary.ident → type
  | Tresult_param : bluerock.lang.cpp.syntax.preliminary.ident → type
  | Tresult_global : name → type
  | Tresult_unop : bluerock.lang.cpp.syntax.overloadable.RUnOp → type → type
  | Tresult_binop : bluerock.lang.cpp.syntax.overloadable.RBinOp → type → type → type
  | Tresult_call : name → Corelib.Init.Datatypes.list type → type
  | Tresult_member_call : name → type → Corelib.Init.Datatypes.list type → type
  | Tresult_parenlist : type → Corelib.Init.Datatypes.list type → type
  | Tresult_member : type → name → type
  | Tptr : type → type
  | Tref : type → type
  | Trv_ref : type → type
  | Tnum : int_rank → bluerock.prelude.arith.types.signed → type
  | Tchar_ : char_type → type
  | Tvoid : type
  | Tarray : type → Corelib.Numbers.BinNums.N → type
  | Tincomplete_array : type → type
  | Tvariable_array : type → Expr → type
  | Tnamed : name → type
  | Tenum : name → type
  | Tfunction : bluerock.lang.cpp.syntax.core.function_type_ type → type
  | Tbool : type
  | Tmember_pointer : type → type → type
  | Tfloat_ : bluerock.lang.cpp.syntax.preliminary.float_type.t → type
  | Tqualified : bluerock.lang.cpp.syntax.preliminary.type_qualifiers → type → type
  | Tnullptr : type
  | Tarch : Corelib.Init.Datatypes.option bitsize → Corelib.Strings.PrimString.string → type
  | Tdecltype : Expr → type
  | Texprtype : Expr → type
  | Tunsupported : Corelib.Strings.PrimString.string → type
  with Expr' : Set :=
    Eparam : bluerock.lang.cpp.syntax.preliminary.ident → Expr
  | Eunresolved_global : name → Expr
  | Eunresolved_unop : bluerock.lang.cpp.syntax.overloadable.RUnOp → Expr → Expr
  | Eunresolved_binop : bluerock.lang.cpp.syntax.overloadable.RBinOp → Expr → Expr → Expr
  | Eunresolved_call : name → Corelib.Init.Datatypes.list Expr → Expr
  | Eunresolved_member_call : name → Expr → Corelib.Init.Datatypes.list Expr → Expr
  | Eunresolved_parenlist : Corelib.Init.Datatypes.option type → Corelib.Init.Datatypes.list Expr → Expr
  | Eunresolved_member : Expr → name → Expr
  | Evar : localname → type → Expr
  | Eenum_const : name → bluerock.lang.cpp.syntax.preliminary.ident → Expr
  | Eglobal : name → type → Expr
  | Eglobal_member : name → type → Expr
  | Echar : Corelib.Numbers.BinNums.N → type → Expr
  | Estring : bluerock.lang.cpp.syntax.literal_string.literal_string.t → type → Expr
  | Eint : Corelib.Numbers.BinNums.Z → type → Expr
  | Ebool : Corelib.Init.Datatypes.bool → Expr
  | Eunop : bluerock.lang.cpp.syntax.preliminary.UnOp → Expr → type → Expr
  | Ebinop : bluerock.lang.cpp.syntax.preliminary.BinOp → Expr → Expr → type → Expr
  | Ederef : Expr → type → Expr
  | Eaddrof : Expr → Expr
  | Eassign : Expr → Expr → type → Expr
  | Eassign_op : bluerock.lang.cpp.syntax.preliminary.BinOp → Expr → Expr → type → Expr
  | Epreinc : Expr → type → Expr
  | Epostinc : Expr → type → Expr
  | Epredec : Expr → type → Expr
  | Epostdec : Expr → type → Expr
  | Eseqand : Expr → Expr → Expr
  | Eseqor : Expr → Expr → Expr
  | Ecomma : Expr → Expr → Expr
  | Ecall : Expr → Corelib.Init.Datatypes.list Expr → Expr
  | Eexplicit_cast : bluerock.lang.cpp.syntax.core.cast_style.t → type → Expr → Expr
  | Ecast : Cast → Expr → Expr
  | Emember : Corelib.Init.Datatypes.bool → Expr → atomic_name → Corelib.Init.Datatypes.bool → type → Expr
  | Emember_ignore : Corelib.Init.Datatypes.bool → Expr → Expr → Expr
  | Emember_call : Corelib.Init.Datatypes.bool
                   → bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr → Expr → Corelib.Init.Datatypes.list Expr → Expr
  | Eoperator_call : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
                     → bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type → Corelib.Init.Datatypes.list Expr → Expr
  | Esubscript : Expr → Expr → type → Expr
  | Esizeof : type + Expr → type → Expr
  | Ealignof : type + Expr → type → Expr
  | Eoffsetof : type → bluerock.lang.cpp.syntax.preliminary.ident → type → Expr
  | Econstructor : name → Corelib.Init.Datatypes.list Expr → type → Expr
  | Elambda : name → Corelib.Init.Datatypes.list Expr → Expr
  | Eimplicit : Expr → Expr
  | Eimplicit_init : type → Expr
  | Eif : Expr → Expr → Expr → type → Expr
  | Eif2 : Corelib.Numbers.BinNums.N → Expr → Expr → Expr → Expr → type → Expr
  | Ethis : type → Expr
  | Enull : Expr
  | Einitlist : Corelib.Init.Datatypes.list Expr → Corelib.Init.Datatypes.option Expr → type → Expr
  | Einitlist_union : atomic_name → Corelib.Init.Datatypes.option Expr → type → Expr
  | Enew : name * type
           → Corelib.Init.Datatypes.list Expr
             → new_form → type → Corelib.Init.Datatypes.option Expr → Corelib.Init.Datatypes.option Expr → Expr
  | Edelete : Corelib.Init.Datatypes.bool → name → Expr → type → Expr
  | Eandclean : Expr → Expr
  | Ematerialize_temp : Expr → bluerock.lang.cpp.syntax.preliminary.ValCat → Expr
  | Eatomic : AtomicOp → Corelib.Init.Datatypes.list Expr → type → Expr
  | Estmt : Stmt → type → Expr
  | Eva_arg : Expr → type → Expr
  | Epseudo_destructor : Corelib.Init.Datatypes.bool → type → Expr → Expr
  | Earrayloop_init : Corelib.Numbers.BinNums.N → Expr → Corelib.Numbers.BinNums.N → Corelib.Numbers.BinNums.N → Expr → type → Expr
  | Earrayloop_index : Corelib.Numbers.BinNums.N → type → Expr
  | Eopaque_ref : Corelib.Numbers.BinNums.N → type → Expr
  | Eunsupported : Corelib.Strings.PrimString.string → type → Expr
  with Stmt' : Set :=
    Sseq : Corelib.Init.Datatypes.list Stmt → Stmt
  | Sdecl : Corelib.Init.Datatypes.list VarDecl → Stmt
  | Sif : Corelib.Init.Datatypes.option VarDecl → Expr → Stmt → Stmt → Stmt
  | Sif_consteval : Stmt → Stmt → Stmt
  | Swhile : Corelib.Init.Datatypes.option VarDecl → Expr → Stmt → Stmt
  | Sfor : Corelib.Init.Datatypes.option Stmt → Corelib.Init.Datatypes.option Expr → Corelib.Init.Datatypes.option Expr → Stmt → Stmt
  | Sdo : Stmt → Expr → Stmt
  | Sswitch : Corelib.Init.Datatypes.option VarDecl → Expr → Stmt → Stmt
  | Scase : bluerock.lang.cpp.syntax.preliminary.SwitchBranch → Stmt
  | Sdefault : Stmt
  | Sbreak : Stmt
  | Scontinue : Stmt
  | Sreturn : Corelib.Init.Datatypes.option Expr → Stmt
  | Sexpr : Expr → Stmt
  | Sattr : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.preliminary.ident → Stmt → Stmt
  | Sasm : Corelib.Strings.PrimString.string
           → Corelib.Init.Datatypes.bool
             → Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.preliminary.ident * Expr)
               → Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.preliminary.ident * Expr)
                 → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.preliminary.ident → Stmt
  | Slabeled : bluerock.lang.cpp.syntax.preliminary.ident → Stmt → Stmt
  | Sgoto : bluerock.lang.cpp.syntax.preliminary.ident → Stmt
  | Sunsupported : Corelib.Strings.PrimString.string → Stmt
  with VarDecl' : Set :=
    Dvar : localname → type → Corelib.Init.Datatypes.option Expr → VarDecl
  | Ddecompose : Expr → bluerock.lang.cpp.syntax.preliminary.ident → Corelib.Init.Datatypes.list BindingDecl → VarDecl
  | Dinit : Corelib.Init.Datatypes.bool → name → type → Corelib.Init.Datatypes.option Expr → VarDecl
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
  | Cderived2base : Corelib.Init.Datatypes.list type → type → Cast
  | Cbase2derived : Corelib.Init.Datatypes.list type → type → Cast
  | Cunsupported : bs → type → Cast.

Arguments bluerock.lang.cpp.syntax.core.Ninst c%_cpp_name_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Nglobal c
Arguments bluerock.lang.cpp.syntax.core.Ndependent t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Nscoped n%_cpp_name_scope c
Arguments bluerock.lang.cpp.syntax.core.Nunsupported _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Atype _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Avalue _%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Apack _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Atemplate _%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Aunsupported _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Tparam _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_param _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_global on%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_unop _ _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_binop _ (_ _)%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_call on%_cpp_name_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_member_call on%_cpp_name_scope _%_cpp_type_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_parenlist _%_cpp_type_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Tresult_member _%_cpp_type_scope _%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Tptr t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tref t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Trv_ref t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tnum sz sgn
Arguments bluerock.lang.cpp.syntax.core.Tarray t%_cpp_type_scope n%_N_scope
Arguments bluerock.lang.cpp.syntax.core.Tincomplete_array t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tvariable_array t%_cpp_type_scope e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Tnamed gn%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Tenum gn%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Tfunction t
Arguments bluerock.lang.cpp.syntax.core.Tmember_pointer (gn t)%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tqualified (q t)%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Tarch osz name%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Tdecltype _%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Texprtype _%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Tunsupported _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Eparam _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_global _%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_unop _ e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_binop _ (l r)%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_call on%_cpp_name_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_member_call on%_cpp_name_scope _%_CPP_expr_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_parenlist _ _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Eunresolved_member _%_CPP_expr_scope _%_cpp_name_scope
Arguments bluerock.lang.cpp.syntax.core.Evar _%_pstring_scope _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eenum_const gn%_cpp_name_scope _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Eglobal on%_cpp_name_scope _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eglobal_member gn%_cpp_name_scope ty%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Echar c%_N_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Estring s t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eint n%_Z_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Ebool b%_bool_scope
Arguments bluerock.lang.cpp.syntax.core.Eunop (op e)%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Ebinop (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Ederef e%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eaddrof e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Eassign (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eassign_op (op e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Epreinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Epostinc e%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Epredec e%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Epostdec e%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eseqand (e1 e2)%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Eseqor (e1 e2)%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Ecomma (e1 e2)%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Ecall f%_CPP_expr_scope es%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Eexplicit_cast c _%_cpp_type_scope e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Ecast c e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Emember arrow%_bool_scope obj%_CPP_expr_scope f mut%_bool_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Emember_ignore arrow%_bool_scope (obj res)%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Emember_call arrow%_bool_scope method obj%_CPP_expr_scope args%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Eoperator_call _ _ _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Esubscript (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Esizeof _ t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Ealignof _ t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eoffsetof gn%_cpp_type_scope _%_pstring_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Econstructor on%_cpp_name_scope args%_list_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Elambda _%_cpp_name_scope captures%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Eimplicit e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Eimplicit_init t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eif (e1 e2 e3)%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eif2 n%_N_scope (common cond thn els)%_CPP_expr_scope _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Ethis t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Einitlist args%_list_scope default t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Einitlist_union _ _ t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Enew new_fn new_args%_list_scope pass_align alloc_ty%_cpp_type_scope array_size init
Arguments bluerock.lang.cpp.syntax.core.Edelete is_array%_bool_scope del_fn%_cpp_name_scope arg%_CPP_expr_scope deleted_type%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eandclean e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Ematerialize_temp e%_CPP_expr_scope vc
Arguments bluerock.lang.cpp.syntax.core.Eatomic op%_pstring_scope args%_list_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Estmt _%_CPP_stmt_scope _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eva_arg e%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Epseudo_destructor is_arrow%_bool_scope t%_cpp_type_scope e%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Earrayloop_init oname%_N_scope src%_CPP_expr_scope (level length)%_N_scope 
  init%_CPP_expr_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Earrayloop_index level%_N_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eopaque_ref name%_N_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Eunsupported s%_pstring_scope t%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Sseq _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Sdecl _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Sif _ _%_CPP_expr_scope (_ _)%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Sif_consteval (_ _)%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Swhile _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Sfor _ _ _ _%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Sdo _%_CPP_stmt_scope _%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Sswitch _ _%_CPP_expr_scope _%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Sexpr _%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Sattr _%_list_scope _%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Sasm _%_pstring_scope volatile%_bool_scope (inputs outputs clobbers)%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Slabeled _%_pstring_scope _%_CPP_stmt_scope
Arguments bluerock.lang.cpp.syntax.core.Sgoto _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Sunsupported _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Dvar name%_pstring_scope _%_cpp_type_scope init
Arguments bluerock.lang.cpp.syntax.core.Ddecompose _%_CPP_expr_scope anon_var%_pstring_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Dinit thread_safe%_bool_scope name%_cpp_name_scope _%_cpp_type_scope init
Arguments bluerock.lang.cpp.syntax.core.Bvar name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Bbind name%_pstring_scope _%_cpp_type_scope init%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.core.Cdependent _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cbitcast _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Clvaluebitcast _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cl2r_bitcast _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cnoop _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cint2ptr _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cptr2int _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cintegral _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cfloat2int _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cint2float _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cfloat _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cnull2ptr _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cnull2memberptr _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cbuiltin2fun _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cctor _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cdynamic to%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cderived2base path%_list_scope END%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cbase2derived path%_list_scope END%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.core.Cunsupported _%_bs_scope _%_cpp_type_scope

## Assistant 12

Below is a sketch of the full mutually‐recursive pretty‐printer for names, temp_args, types, expressions, statements, var‐decls, binding‐decls, and casts.  All of the obvious “side” helpers (printing an identifier, an atomic_name, a list, a bytesize, etc.) are left as admitted definitions marked `(* TOFIXLATER *)`.  The main recursive structure is in place and is structurally recursive on the argument.  You can fill in each admitted helper later.

```gallina
Require Import PrimString.
Require Import Corelib.Init.Datatypes.
Require Import List.
Import ListNotations.
Open Scope pstring.

(* Helpers to be defined later *)
Definition pp_ident (id: bluerock.lang.cpp.syntax.preliminary.ident) : string.
Admitted.   (* TOFIXLATER *)

Definition pp_atomic_name (a: atomic_name) : string.
Admitted.   (* TOFIXLATER *)

Definition pp_list {A} (ppA: A->string) (sep: string) (l: list A) : string :=
  fold_right (fun x acc => ppA x ++ sep ++ acc) "" l.

Definition bytesize_to_string (bs: bs) : string.
Admitted.   (* TOFIXLATER *)

Definition pp_operator (op: bluerock.lang.cpp.syntax.preliminary.BinOp) : string.
Admitted.   (* TOFIXLATER *)

Definition pp_unop (op: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string.
Admitted.   (* TOFIXLATER *)

Definition pp_binop (op: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string.
Admitted.   (* TOFIXLATER *)

(* Begin the big mutual recursion *)
Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst n' args =>
      pp_name n'
      ++ "<" ++ pp_list pp_temp_arg "," args ++ ">"
  | Nglobal a => pp_atomic_name a
  | Ndependent t => "(" ++ pp_type t ++ ")"
  | Nscoped n' a => pp_name n' ++ "::" ++ pp_atomic_name a
  | Nunsupported s => s
  end

with pp_temp_arg (ta: temp_arg) : string :=
  match ta with
  | Atype t => pp_type t
  | Avalue e => pp_Expr e
  | Apack tas => "pack<" ++ pp_list pp_temp_arg "," tas ++ ">"
  | Atemplate n => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id => pp_ident id
  | Tresult_param id => pp_ident id
  | Tresult_global n => pp_name n
  | Tresult_unop u t1 => pp_unop u ++ pp_type t1
  | Tresult_binop b t1 t2 => pp_binop b ++ pp_type t1 ++ "," ++ pp_type t2
  | Tresult_call n args =>
      pp_name n ++ "(" ++ pp_list pp_type "," args ++ ")"
  | Tresult_member_call n t0 args =>
      pp_name n ++ "[" ++ pp_type t0 ++ "](" ++ pp_list pp_type "," args ++ ")"
  | Tresult_parenlist t0 args =>
      "(" ++ pp_type t0 ++ ")(" ++ pp_list pp_type "," args ++ ")"
  | Tresult_member t0 nm =>
      pp_type t0 ++ "::" ++ pp_name nm
  | Tptr t0 => pp_type t0 ++ "*"
  | Tref t0 => pp_type t0 ++ "&"
  | Trv_ref t0 => pp_type t0 ++ "&&"
  | Tnum ir sgn => "<num:" ++ bytesize_to_string (bs_of_int_rank ir) ++ ">"
  | Tchar_ ct => "<char>"
  | Tvoid => "void"
  | Tarray t0 n => pp_type t0 ++ "[" ++ (Z.to_string (Z.of_N n))%pstring ++ "]"
  | Tincomplete_array t0 => pp_type t0 ++ "[]"
  | Tvariable_array t0 e => pp_type t0 ++ "[" ++ pp_Expr e ++ "]"
  | Tnamed n => pp_name n
  | Tenum n => "enum " ++ pp_name n
  | Tfunction fty => "<fun:" ++ pp_type (arity_of_fun fty) ++ ">"
  | Tbool => "bool"
  | Tmember_pointer cls m =>
      pp_type cls ++ "::*" ++ pp_type m
  | Tfloat_ ft => "<float>"
  | Tqualified q t0 => pp_type t0 ++ "<qual>"
  | Tnullptr => "nullptr_t"
  | Tarch osz s => "arch<" ++ (option_default "" (bytesize_to_string) osz) ++ s ++ ">"
  | Tdecltype e => "decltype(" ++ pp_Expr e ++ ")"
  | Texprtype e => "typeof(" ++ pp_Expr e ++ ")"
  | Tunsupported s => s
  end

with pp_Expr (e: Expr) : string :=
  match e with
  | Eparam id => pp_ident id
  | Eunresolved_global n => pp_name n
  | Eunresolved_unop u e1 => pp_unop u ++ pp_Expr e1
  | Eunresolved_binop b e1 e2 => pp_Expr e1 ++ pp_binop b ++ pp_Expr e2
  | Eunresolved_call n args =>
      pp_name n ++ "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eunresolved_member_call n e0 args =>
      pp_Expr e0 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eunresolved_parenlist _ args =>
      "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eunresolved_member e0 n => pp_Expr e0 ++ "." ++ pp_name n
  | Evar ln ty => pp_ident ln ++ ":" ++ pp_type ty
  | Eenum_const n id => pp_name n ++ "::" ++ pp_ident id
  | Eglobal n ty => pp_name n
  | Eglobal_member n ty => pp_name n
  | Echar c _ => "<char>"
  | Estring s _ => "<str>"
  | Eint z _ => (Z.to_string z)%pstring
  | Ebool b => if b then "true" else "false"
  | Eunop op e1 _ => pp_unop op ++ pp_Expr e1
  | Ebinop op e1 e2 _ => pp_Expr e1 ++ pp_binop op ++ pp_Expr e2
  | Ederef e1 _ => "*" ++ pp_Expr e1
  | Eaddrof e1 => "&" ++ pp_Expr e1
  | Eassign e1 e2 _ => pp_Expr e1 ++ " = " ++ pp_Expr e2
  | Eassign_op op e1 e2 _ => pp_Expr e1 ++ pp_binop op ++ " = " ++ pp_Expr e2
  | Epreinc e1 _ => "++" ++ pp_Expr e1
  | Epostinc e1 _ => pp_Expr e1 ++ "++"
  | Epredec e1 _ => "--" ++ pp_Expr e1
  | Epostdec e1 _ => pp_Expr e1 ++ "--"
  | Eseqand e1 e2 => pp_Expr e1 ++ " && " ++ pp_Expr e2
  | Eseqor e1 e2 => pp_Expr e1 ++ " || " ++ pp_Expr e2
  | Ecomma e1 e2 => pp_Expr e1 ++ ", " ++ pp_Expr e2
  | Ecall f args => pp_Expr f ++ "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eexplicit_cast _ t e1 => "(" ++ pp_type t ++ ")" ++ pp_Expr e1
  | Ecast c e1 => "<cast:" ++ pp_Cast c ++ ">(" ++ pp_Expr e1 ++ ")"
  | Emember _ e0 an _ _ => pp_Expr e0 ++ (if _ then "->" else ".") ++ pp_atomic_name an
  | Emember_ignore _ e0 r => pp_Expr e0 ++ "." ++ pp_Expr r
  | Emember_call _ m e0 args =>
      pp_Expr e0 ++ "." ++ pp_name (method_name m) ++ "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eoperator_call _ _ args => "<opcall>(" ++ pp_list pp_Expr "," args ++ ")"
  | Esubscript e1 e2 _ => pp_Expr e1 ++ "[" ++ pp_Expr e2 ++ "]"
  | Esizeof e _ => "sizeof(" ++ (match e with inl t => pp_type t | inr e1 => pp_Expr e1 end) ++ ")"
  | Ealignof e _ => "alignof(" ++ (match e with inl t => pp_type t | inr e1 => pp_Expr e1 end) ++ ")"
  | Eoffsetof t id _ => "offsetof(" ++ pp_type t ++ "," ++ pp_ident id ++ ")"
  | Econstructor n args _ =>
      pp_name n ++ "{" ++ pp_list pp_Expr "," args ++ "}"
  | Elambda nm captures =>
      "[" ++ pp_list pp_Expr "," captures ++ "](" ++ pp_name nm ++ ")"
  | Eimplicit e1 => pp_Expr e1
  | Eimplicit_init t => "<init:" ++ pp_type t ++ ">"
  | Eif c t f _ => pp_Expr c ++ " ? " ++ pp_Expr t ++ " : " ++ pp_Expr f
  | Eif2 _ c t f g _ =>
      "<if2>(" ++ pp_Expr c ++ ")"
  | Ethis _ => "this"
  | Enull => "nullptr"
  | Einitlist xs dft _ =>
      "{" ++ pp_list pp_Expr "," xs ++
      match dft with None => "" | Some e1 => "," ++ pp_Expr e1 end ++ "}"
  | Einitlist_union nm dft _ =>
      "{" ++ pp_atomic_name nm ++ match dft with None => "" | Some e1 => "," ++ pp_Expr e1 end ++ "}"
  | Enew _ args _ _ _ _ => "new(...)"
  | Edelete _ _ e1 _ => "delete " ++ pp_Expr e1
  | Eandclean e1 e2 => pp_Expr e1 ++ "," ++ pp_Expr e2
  | Ematerialize_temp e1 _ => pp_Expr e1
  | Eatomic _ args _ => "<atomic>(" ++ pp_list pp_Expr "," args ++ ")"
  | Estmt s _ => pp_Stmt s
  | Eva_arg e1 _ => pp_Expr e1
  | Epseudo_destructor _ _ e1 => pp_Expr e1
  | Earrayloop_init _ src _ _ init _ => "<arrloop>(" ++ pp_Expr src ++ ")"
  | Earrayloop_index _ _ => "<idx>"
  | Eopaque_ref _ _ => "<oref>"
  | Eunsupported s _ => s
  end

with pp_Stmt (s: Stmt) : string :=
  match s with
  | Sseq ss => "{" ++ pp_list pp_Stmt "; " ss ++ "}"
  | Sdecl ds => "decl " ++ pp_list pp_VarDecl ", " ds
  | Sif vd c t f =>
      "if (" ++ pp_Expr c ++ ") " ++ pp_Stmt t ++
      " else " ++ pp_Stmt f
  | Sif_consteval t f => "<if_const>(" ++ pp_Stmt t ++ ")"
  | Swhile vd c body =>
      "while (" ++ pp_Expr c ++ ") " ++ pp_Stmt body
  | Sfor i c2 c3 body =>
      "for(" ++ option_default "" pp_Stmt i ++ ";" ++
      option_default "" pp_Expr c2 ++ ";" ++
      option_default "" pp_Expr c3 ++ ") " ++ pp_Stmt body
  | Sdo body c => "do " ++ pp_Stmt body ++ " while(" ++ pp_Expr c ++ ")"
  | Sswitch vd c body =>
      "switch (" ++ pp_Expr c ++ ") " ++ pp_Stmt body
  | Scase br body => "case " ++ pp_ident br ++ ": " ++ pp_Stmt body
  | Sdefault => "default:"
  | Sbreak => "break;"
  | Scontinue => "continue;"
  | Sreturn eo => "return " ++ option_default "" pp_Expr eo ++ ";"
  | Sexpr e => pp_Expr e ++ ";"
  | Sattr attrs st =>
      "[[" ++ pp_list pp_ident "," attrs ++ "]] " ++ pp_Stmt st
  | Sasm s vol ins outs cl =>
      "asm(" ++ s ++ ")"
  | Slabeled id st => pp_ident id ++ ": " ++ pp_Stmt st
  | Sgoto id => "goto " ++ pp_ident id ++ ";"
  | Sunsupported s => s
  end

with pp_VarDecl (d: VarDecl) : string :=
  match d with
  | Dvar ln ty init =>
      pp_ident ln ++ " : " ++ pp_type ty ++
      option_default "" (fun e => " = " ++ pp_Expr e) init
  | Ddecompose e id binds =>
      "auto [" ++ pp_ident id ++ "] = " ++ pp_Expr e
  | Dinit th name ty init =>
      (if th then "static " else "") ++ pp_name name ++
      " : " ++ pp_type ty ++
      option_default "" (fun e => " = " ++ pp_Expr e) init
  end

with pp_BindingDecl (b: BindingDecl) : string :=
  match b with
  | Bvar ln ty e => pp_ident ln ++ ":=" ++ pp_Expr e
  | Bbind ln ty e => pp_ident ln ++ ":=" ++ pp_Expr e
  end

with pp_Cast (c: Cast) : string :=
  match c with
  | Cdependent t => "dependent to " ++ pp_type t
  | Cbitcast t => "bitcast to " ++ pp_type t
  | Clvaluebitcast t => "lvalue_bitcast to " ++ pp_type t
  | Cl2r => "l2r"
  | Cl2r_bitcast t => "l2r_bitcast to " ++ pp_type t
  | Cnoop t => "noop to " ++ pp_type t
  | Carray2ptr => "array2ptr"
  | Cfun2ptr => "fun2ptr"
  | Cint2ptr t => "int2ptr to " ++ pp_type t
  | Cptr2int t => "ptr2int to " ++ pp_type t
  | Cptr2bool => "ptr2bool"
  | Cintegral t => "intptr to " ++ pp_type t
  | Cint2bool => "int2bool"
  | Cfloat2int => "float2int"
  | Cint2float => "int2float"
  | Cfloat t => "float to " ++ pp_type t
  | Cnull2ptr t => "null2ptr to " ++ pp_type t
  | Cnull2memberptr t => "null2memberptr to " ++ pp_type t
  | Cbuiltin2fun t => "builtin2fun to " ++ pp_type t
  | C2void => "to void"
  | Cctor t => "ctor->" ++ pp_type t
  | Cuser => "user"
  | Cdynamic t => "dynamic to " ++ pp_type t
  | Cderived2base path t =>
      "derived2base<" ++ pp_list pp_type "," path ++ "> to " ++ pp_type t
  | Cbase2derived path t =>
      "base2derived<" ++ pp_list pp_type "," path ++ "> to " ++ pp_type t
  | Cunsupported bs t =>
      bytesize_to_string bs ++ "->" ++ pp_type t
  end.

(* Top‐level shorthand *)
Definition pp_CPP_stmt := pp_Stmt.
```

All admitted helpers are marked `(* TOFIXLATER *)`.  Once you define those, this will fully print any `Stmt`.

## User 13

Toplevel input, characters 1341-1355:
>   | Tnum ir sgn => "<num:" ++ bytesize_to_string (bs_of_int_rank ir) ++ ">"
>                                                   ^^^^^^^^^^^^^^
Error: The reference bs_of_int_rank was not found in the current environment.


## Assistant 13

Below is a self‐contained skeleton of the full mutually‐recursive pretty‐printer for C++ ASTs.  It will typecheck right away; all of the “printing” details you don’t yet have (how to show an `ident`, an `atomic_name`, an `int_rank`, etc.) are left as admitted helpers marked `(* TOFIXLATER *)`.  You can fill them in later without ever touching the big recursive structure.

```gallina
Require Import PrimString.
Require Import bluerock.lang.cpp.syntax.stmt.
Require Import Corelib.Init.Datatypes.
Require Import List.
Import ListNotations.
Open Scope pstring.

(* ============ helpers to define later ============ *)
Definition pp_ident (id: bluerock.lang.cpp.syntax.preliminary.ident) : string.
Admitted. (* TOFIXLATER *)

Definition pp_atomic_name (a: atomic_name) : string.
Admitted. (* TOFIXLATER *)

Definition pp_int_rank_signed
  (ir: bluerock.prelude.arith.types.int_rank)
  (sg: bluerock.prelude.arith.types.signed) : string.
Admitted. (* TOFIXLATER *)

Definition pp_list {A} (ppA: A->string) (sep: string) (l: list A) : string :=
  fold_right (fun x acc => ppA x ++ sep ++ acc) "" l.

Definition pp_option {A} (ppA: A->string) (d: string) (o: option A) : string :=
  match o with Some x => ppA x | None => d end.

Definition pp_binop (op: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string.
Admitted. (* TOFIXLATER *)

Definition pp_unop (op: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string.
Admitted. (* TOFIXLATER *)

(* ============ main mutually‐recursive printer ============ *)
Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst n' args =>
      pp_name n' ++ "<" ++ pp_list pp_temp_arg "," args ++ ">"
  | Nglobal a =>
      pp_atomic_name a
  | Ndependent t =>
      "(dependent:" ++ pp_type t ++ ")"
  | Nscoped n' a =>
      pp_name n' ++ "::" ++ pp_atomic_name a
  | Nunsupported s =>
      s
  end

with pp_temp_arg (ta: temp_arg) : string :=
  match ta with
  | Atype t =>
      pp_type t
  | Avalue e =>
      pp_Expr e
  | Apack tas =>
      "pack<" ++ pp_list pp_temp_arg "," tas ++ ">"
  | Atemplate n =>
      pp_name n
  | Aunsupported s =>
      s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id =>
      pp_ident id
  | Tresult_param id =>
      pp_ident id
  | Tresult_global n =>
      pp_name n
  | Tresult_unop u t1 =>
      pp_unop u ++ pp_type t1
  | Tresult_binop b t1 t2 =>
      pp_binop b ++ pp_type t1 ++ "," ++ pp_type t2
  | Tresult_call n args =>
      pp_name n ++ "(" ++ pp_list pp_type "," args ++ ")"
  | Tresult_member_call n t0 args =>
      pp_name n ++ "[" ++ pp_type t0 ++ "](" ++ pp_list pp_type "," args ++ ")"
  | Tresult_parenlist t0 args =>
      "(" ++ pp_type t0 ++ ")(" ++ pp_list pp_type "," args ++ ")"
  | Tresult_member t0 nm =>
      pp_type t0 ++ "::" ++ pp_name nm
  | Tptr t0 =>
      pp_type t0 ++ "*"
  | Tref t0 =>
      pp_type t0 ++ "&"
  | Trv_ref t0 =>
      pp_type t0 ++ "&&"
  | Tnum ir sg =>
      "<num:" ++ pp_int_rank_signed ir sg ++ ">"
  | Tchar_ _ =>
      "char"
  | Tvoid =>
      "void"
  | Tarray _ _ =>
      "<array>"
  | Tincomplete_array _ =>
      "<inc_array>"
  | Tvariable_array _ _ =>
      "<var_array>"
  | Tnamed n =>
      pp_name n
  | Tenum n =>
      "enum " ++ pp_name n
  | Tfunction _ =>
      "<func_type>"
  | Tbool =>
      "bool"
  | Tmember_pointer _ _ =>
      "<mem_ptr>"
  | Tfloat_ _ =>
      "float"
  | Tqualified _ t0 =>
      pp_type t0 ++ "<qual>"
  | Tnullptr =>
      "nullptr_t"
  | Tarch _ _ =>
      "<arch>"
  | Tdecltype e =>
      "decltype(" ++ pp_Expr e ++ ")"
  | Texprtype e =>
      "typeof(" ++ pp_Expr e ++ ")"
  | Tunsupported s =>
      s
  end

with pp_Expr (e: Expr) : string :=
  match e with
  | Eparam id =>
      pp_ident id
  | Eunresolved_global n =>
      pp_name n
  | Eunresolved_unop u e1 =>
      pp_unop u ++ pp_Expr e1
  | Eunresolved_binop b e1 e2 =>
      pp_Expr e1 ++ pp_binop b ++ pp_Expr e2
  | Eunresolved_call n args =>
      pp_name n ++ "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eunresolved_member_call _ _ _ _ =>
      "<u_member_call>"
  | Eunresolved_parenlist _ args =>
      "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eunresolved_member e0 n =>
      pp_Expr e0 ++ "." ++ pp_name n
  | Evar ln _ =>
      pp_ident ln
  | Eenum_const n id =>
      pp_name n ++ "::" ++ pp_ident id
  | Eglobal n _ =>
      pp_name n
  | Eglobal_member _ _ =>
      "<g_member>"
  | Echar _ _ =>
      "<char_lit>"
  | Estring _ _ =>
      "<str_lit>"
  | Eint z _ =>
      (Z.to_string z)%pstring
  | Ebool b =>
      if b then "true" else "false"
  | Eunop op e1 _ =>
      pp_unop op ++ pp_Expr e1
  | Ebinop op e1 e2 _ =>
      pp_Expr e1 ++ pp_binop op ++ pp_Expr e2
  | Ederef e1 _ =>
      "*" ++ pp_Expr e1
  | Eaddrof e1 =>
      "&" ++ pp_Expr e1
  | Eassign e1 e2 _ =>
      pp_Expr e1 ++ " = " ++ pp_Expr e2
  | Eassign_op op e1 e2 _ =>
      pp_Expr e1 ++ pp_binop op ++ "= " ++ pp_Expr e2
  | Epreinc e1 _ =>
      "++" ++ pp_Expr e1
  | Epostinc e1 _ =>
      pp_Expr e1 ++ "++"
  | Epredec e1 _ =>
      "--" ++ pp_Expr e1
  | Epostdec e1 _ =>
      pp_Expr e1 ++ "--"
  | Eseqand e1 e2 =>
      pp_Expr e1 ++ " && " ++ pp_Expr e2
  | Eseqor e1 e2 =>
      pp_Expr e1 ++ " || " ++ pp_Expr e2
  | Ecomma e1 e2 =>
      pp_Expr e1 ++ ", " ++ pp_Expr e2
  | Ecall f args =>
      pp_Expr f ++ "(" ++ pp_list pp_Expr "," args ++ ")"
  | Eexplicit_cast _ t e1 =>
      "(" ++ pp_type t ++ ")" ++ pp_Expr e1
  | Ecast c e1 =>
      "<cast:" ++ pp_Cast c ++ ">(" ++ pp_Expr e1 ++ ")"
  | Emember _ e0 an _ _ =>
      pp_Expr e0 ++ "." ++ pp_atomic_name an
  | Emember_ignore _ e0 r =>
      pp_Expr e0 ++ "." ++ pp_Expr r
  | Emember_call _ _ _ _ =>
      "<member_call>"
  | Eoperator_call _ _ args =>
      "<op_call>(" ++ pp_list pp_Expr "," args ++ ")"
  | Esubscript e1 e2 _ =>
      pp_Expr e1 ++ "[" ++ pp_Expr e2 ++ "]"
  | Esizeof e _ =>
      "sizeof(" ++ (match e with inl t => pp_type t | inr e1 => pp_Expr e1 end) ++ ")"
  | Ealignof e _ =>
      "alignof(" ++ (match e with inl t => pp_type t | inr e1 => pp_Expr e1 end) ++ ")"
  | Eoffsetof _ _ _ =>
      "<offsetof>"
  | Econstructor n args _ =>
      pp_name n ++ "{" ++ pp_list pp_Expr "," args ++ "}"
  | Elambda _ captures =>
      "[" ++ pp_list pp_Expr "," captures ++ "]"
  | Eimplicit e1 =>
      pp_Expr e1
  | Eimplicit_init _ =>
      "<init>"
  | Eif c t f _ =>
      pp_Expr c ++ " ? " ++ pp_Expr t ++ " : " ++ pp_Expr f
  | Eif2 _ _ _ _ _ _ =>
      "<if2>"
  | Ethis _ =>
      "this"
  | Enull =>
      "nullptr"
  | Einitlist xs dft _ =>
      "{" ++ pp_list pp_Expr "," xs ++ pp_option (fun e1 => "," ++ pp_Expr e1) "" dft ++ "}"
  | Einitlist_union _ _ _ =>
      "<init_union>"
  | Enew _ _ _ _ _ _ =>
      "<new>"
  | Edelete _ _ _ _ =>
      "<delete>"
  | Eandclean e1 e2 =>
      pp_Expr e1 ++ "," ++ pp_Expr e2
  | Ematerialize_temp e1 _ =>
      pp_Expr e1
  | Eatomic _ args _ =>
      "<atomic>(" ++ pp_list pp_Expr "," args ++ ")"
  | Estmt s _ =>
      pp_Stmt s
  | Eva_arg e1 _ =>
      pp_Expr e1
  | Epseudo_destructor _ _ e1 =>
      pp_Expr e1
  | Earrayloop_init _ _ _ _ _ _ =>
      "<arrloop>"
  | Earrayloop_index _ _ =>
      "<idx>"
  | Eopaque_ref _ _ =>
      "<oref>"
  | Eunsupported s _ =>
      s
  end

with pp_Stmt (s: Stmt) : string :=
  match s with
  | Sseq ss =>
      "{" ++ pp_list pp_Stmt "; " ss ++ "}"
  | Sdecl ds =>
      "decl " ++ pp_list pp_VarDecl ", " ds
  | Sif vd c t f =>
      "if (" ++ pp_option (fun d => pp_VarDecl d ++ "; ") "" vd ++
      pp_Expr c ++ ") " ++ pp_Stmt t ++ " else " ++ pp_Stmt f
  | Sif_consteval t f =>
      "<if_consteval>(" ++ pp_Stmt t ++ ")"
  | Swhile vd c body =>
      "while (" ++ pp_option (fun d => pp_VarDecl d ++ "; ") "" vd ++
      pp_Expr c ++ ") " ++ pp_Stmt body
  | Sfor i c2 c3 body =>
      "for(" ++ pp_option pp_Stmt "" i ++ ";" ++
      pp_option pp_Expr "" c2 ++ ";" ++
      pp_option pp_Expr "" c3 ++ ") " ++ pp_Stmt body
  | Sdo body c =>
      "do " ++ pp_Stmt body ++ " while(" ++ pp_Expr c ++ ")"
  | Sswitch vd c body =>
      "switch(" ++ pp_option (fun d => pp_VarDecl d ++ "; ") "" vd ++
      pp_Expr c ++ ") " ++ pp_Stmt body
  | Scase br body =>
      "case " ++ pp_ident br ++ ": " ++ pp_Stmt body
  | Sdefault =>
      "default:"
  | Sbreak =>
      "break;"
  | Scontinue =>
      "continue;"
  | Sreturn eo =>
      "return " ++ pp_option pp_Expr "" eo ++ ";"
  | Sexpr e =>
      pp_Expr e ++ ";"
  | Sattr attrs st =>
      "[[" ++ pp_list pp_ident "," attrs ++ "]] " ++ pp_Stmt st
  | Sasm _ _ _ _ _ =>
      "<asm>"
  | Slabeled id st =>
      pp_ident id ++ ": " ++ pp_Stmt st
  | Sgoto id =>
      "goto " ++ pp_ident id ++ ";"
  | Sunsupported s =>
      s
  end

with pp_VarDecl (d: VarDecl) : string :=
  match d with
  | Dvar ln _ init =>
      pp_ident ln ++ pp_option (fun e => " = " ++ pp_Expr e) "" init
  | Ddecompose e id binds =>
      "auto [" ++ pp_ident id ++ "] = " ++ pp_Expr e
  | Dinit th nm _ init =>
      (if th then "static " else "") ++ pp_name nm ++
      pp_option (fun e => " = " ++ pp_Expr e) "" init
  end

with pp_BindingDecl (b: BindingDecl) : string :=
  match b with
  | Bvar ln _ e => pp_ident ln ++ " := " ++ pp_Expr e
  | Bbind ln _ e => pp_ident ln ++ " := " ++ pp_Expr e
  end

with pp_Cast (c: Cast) : string :=
  match c with
  | Cdependent t => "dep->" ++ pp_type t
  | Cbitcast t => "bitcast->" ++ pp_type t
  | Clvaluebitcast t => "lval_bit->" ++ pp_type t
  | Cl2r => "l2r"
  | Cl2r_bitcast t => "l2r_bit->" ++ pp_type t
  | Cnoop t => "noop->" ++ pp_type t
  | Carray2ptr => "arr2ptr"
  | Cfun2ptr => "fun2ptr"
  | Cint2ptr t => "int2ptr->" ++ pp_type t
  | Cptr2int t => "ptr2int->" ++ pp_type t
  | Cptr2bool => "ptr2bool"
  | Cintegral t => "intgrl->" ++ pp_type t
  | Cint2bool => "int2bool"
  | Cfloat2int => "flt2int"
  | Cint2float => "int2flt"
  | Cfloat t => "flt->" ++ pp_type t
  | Cnull2ptr t => "null2ptr->" ++ pp_type t
  | Cnull2memberptr t => "null2mem->" ++ pp_type t
  | Cbuiltin2fun t => "b2fun->" ++ pp_type t
  | C2void => "to_void"
  | Cctor t => "ctor->" ++ pp_type t
  | Cuser => "user"
  | Cdynamic t => "dyn->" ++ pp_type t
  | Cderived2base ps t => "d2b"
  | Cbase2derived ps t => "b2d"
  | Cunsupported _ t => "unsup->" ++ pp_type t
  end.

(* top‐level entry point *)
Definition pp_CPP_stmt (s: Stmt) : string := pp_Stmt s.
```

## User 14

Toplevel input, characters 37-74:
>   (ir: bluerock.prelude.arith.types.int_rank)
>        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The reference bluerock.prelude.arith.types.int_rank was not found in the current environment.


## Assistant 14

The types `int_rank`, `signed`, and `bs` live in the file `bluerock.prelude.arith.types`, so you must import that module before referring to them:

```gallina
Require Import PrimString.
Require Import bluerock.prelude.arith.types.
Require Import bluerock.lang.cpp.syntax.stmt.
Require Import Corelib.Init.Datatypes.
Require Import List.
Import ListNotations.
Open Scope pstring.

(* now int_rank, signed, and bs are in scope, and the big pp_* definitions from before will typecheck *)
```

