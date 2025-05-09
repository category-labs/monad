## User 31

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

Locate nat. (* print fully qualified name(s) of all items whose fully qualified name ends in `.nat`. *)
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

### confusing Arguments output of Print on Inductives
Below an example showing the output of the `Print` query on `Inductive` types.
```
Inductive pairnat: Set :=
  pairn (l: nat) (r: nat).
Print pairnat.

(*
Inductive pairnat : Set :=  pairn : Corelib.Init.Datatypes.nat → Corelib.Init.Datatypes.nat → monad.proofs.execproofs.test.pairnat.

Arguments monad.proofs.execproofs.test.pairn (l r)%_nat_scope
 *)
```
The `(l r)%_nat_scope` part in may be confusing to you. It should actually be read as:
```
Arguments monad.proofs.execproofs.test.pairn l%_nat_scope r%_nat_scope
```
When printing, Coq puts consequetive arguments in a pair of parentheses if they have the same notation scope, so as to only print the notation scope once for all of them.
But DO NOT GET CONFUSED into thinking that the contents inside the parentheses are a single (e.g. tuple) argument: they are different arguments. Keep this in mind when generating pattern matching on constructors of inductive types.
For example, the following 2 pattern matches are WRONG:

```gallina
match p with 
| pairn (l,r) =>...
end
```

```gallina
match p with 
| pairn lr  => let '(l,r) := lr in ...
end
```

The correct way to write the pattern match is:
```gallina
match p with 
| pairn l r  => ...
end
```
## Corelib.Strings.PrimString.string vs Stdlib.Strings.String.string
Coq now provides 2 definitions string libraries. 
`Stdlib.Strings.String.string` is inductively defined has has been around for decades and used by most Coq developments.
`Corelib.Strings.PrimString.string` is a very recent addition. 
It axiomatizes primitive strings. The scope delimiting key for `PrimString.string` is `pstring`.
So, `(a ++ b)%pstring` appends `a:PrimString.string` and `b:PrimString.string`.
The key for `String.string` is just `string`.
You can open `pstring_scope` to elide the %pstring part.
In applications where speed is important and you are given a choice to chose between the 2, you probably want to choose 
`Corelib.Strings.PrimString.string`.

# Current Task
bluerock.lang.cpp.syntax.stmt.Stmt is an Inductive type I have defined for C++ statements.
`bluerock.lang.cpp.syntax.stmt.Stmt` is defined mutually Inductively with many other types like `Expr`.
Write a set of mutually recursive pretty-printer functions for all such types.
These Gallina functions should return `PrimString.string`.

# Response Format (IMPORTANT)
You can either give me (an elisp chat loop) the answer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```.
If you do not follow this format, I would not be able to respond to you properly.
Although I log and publish your responses in entirety, to respond to you, I ONLY LOOK AT THE LAST CODE BLOCK (```gallina or ```coqquery) IN YOUR RESPONSE.
If that is a ```coqquery block, I will send the queries to coqtop and give you back the responses.
If that is a ```gallina block, I will insert it into emacs+proof-general+company-coq and ask proof-general to check till the end.
If there are coq errors, I will respond with the errors.

An example of a valid response is:
```coqquery
Print Stmt.
Print Expr.
```
An example of an answer (not to the the current task) is:
```gallina
Definition foo : nat := 1+2.
Definition bar : nat := 1+3.
```

You can include multiple queries in a ```coqquery block: one in each line.

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasn't available in the queries you have issued so far.
DO NOT emit any `Require Import/Export` commands. All the availble libraries have already been `Require`d, so they are availble, at least with fully qualified names. If needed, you can Import (but not `Require Import`) modules defining notations.

In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.



## Assistant 31

I need to see exactly how `Stmt` (and its sibling types like `Expr`) are defined in your development so I can generate the appropriate `match` clauses and handle all constructors.  Please dump their definitions for me:

```coqquery
Locate Stmt.
Print bluerock.lang.cpp.syntax.stmt.Stmt.
Print bluerock.lang.cpp.syntax.expr.Expr.
```

## User 32

>>> Locate Stmt.
Notation bluerock.lang.cpp.syntax.stmt.Stmt
Notation bluerock.lang.cpp.syntax.core.Stmt (shorter name to refer to it in current context is core.Stmt)
Module Type bluerock.lang.cpp.logic.stmt.Stmt
Module bluerock.lang.cpp.syntax.compare.Stmt (shorter name to refer to it in current context is compare.Stmt)

>>> Print bluerock.lang.cpp.syntax.stmt.Stmt.
Notation Stmt := Stmt

Inductive name' : Set :=
    Ninst : name → Corelib.Init.Datatypes.list temp_arg → name
  | Nglobal : bluerock.lang.cpp.syntax.core.atomic_name_ type → name
  | Ndependent : type → name
  | Nscoped : name → bluerock.lang.cpp.syntax.core.atomic_name_ type → name
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
  | Emember : Corelib.Init.Datatypes.bool
              → Expr → bluerock.lang.cpp.syntax.core.atomic_name_ type → Corelib.Init.Datatypes.bool → type → Expr
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
  | Einitlist_union : bluerock.lang.cpp.syntax.core.atomic_name_ type → Corelib.Init.Datatypes.option Expr → type → Expr
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

>>> Print bluerock.lang.cpp.syntax.expr.Expr.
Toplevel input, characters 6-40:
> Print bluerock.lang.cpp.syntax.expr.Expr.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.lang.cpp.syntax.expr.Expr not a defined object.

## Assistant 32

I need to know the exact definitions of all the subsidiary types (localname, ident, UnOp, BinOp, operator_impl.t, MethodRef_, OverloadableOperator, float_type.t, cast_style.t, literal_string.t, AtomicOp, new_form, etc.) so I can write correct `match`‐clauses and recursive calls. These were not included in the big mutual block for `Stmt`/`Expr`/… above. Please dump them for me:

```coqquery
Print bluerock.lang.cpp.syntax.preliminary.ident.
Print bluerock.lang.cpp.syntax.preliminary.UnOp.
Print bluerock.lang.cpp.syntax.preliminary.BinOp.
Print bluerock.lang.cpp.syntax.preliminary.operator_impl.t.
Print bluerock.lang.cpp.syntax.preliminary.MethodRef_.
Print bluerock.lang.cpp.syntax.preliminary.OverloadableOperator.
Print bluerock.lang.cpp.syntax.preliminary.float_type.t.
Print bluerock.lang.cpp.syntax.core.cast_style.t.
Print bluerock.lang.cpp.syntax.literal_string.literal_string.t.
Print bluerock.lang.cpp.syntax.core.new_form.
Print bluerock.lang.cpp.syntax.core.AtomicOp.
Print bluerock.lang.cpp.syntax.preliminary.localname.
```

## User 33

>>> Print bluerock.lang.cpp.syntax.preliminary.ident.
bluerock.lang.cpp.syntax.preliminary.ident = Corelib.Strings.PrimString.string
     : Set

>>> Print bluerock.lang.cpp.syntax.preliminary.UnOp.
Variant UnOp : Set :=
    Uminus : bluerock.lang.cpp.syntax.preliminary.UnOp
  | Uplus : bluerock.lang.cpp.syntax.preliminary.UnOp
  | Unot : bluerock.lang.cpp.syntax.preliminary.UnOp
  | Ubnot : bluerock.lang.cpp.syntax.preliminary.UnOp
  | Uunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.preliminary.UnOp.

Arguments bluerock.lang.cpp.syntax.preliminary.Uunsupported _%_pstring_scope

>>> Print bluerock.lang.cpp.syntax.preliminary.BinOp.
Variant BinOp : Set :=
    Badd : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Band : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bcmp : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bdiv : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Beq : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bge : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bgt : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Ble : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Blt : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bmul : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bneq : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bor : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bmod : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bshl : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bshr : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bsub : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bxor : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bdotp : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bdotip : bluerock.lang.cpp.syntax.preliminary.BinOp
  | Bunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.preliminary.BinOp.

Arguments bluerock.lang.cpp.syntax.preliminary.Bunsupported _%_pstring_scope

>>> Print bluerock.lang.cpp.syntax.preliminary.operator_impl.t.
Variant t (obj_name type : Set) : Set :=
    Func : obj_name → type → bluerock.lang.cpp.syntax.preliminary.operator_impl.t obj_name type
  | MFunc : obj_name
            → bluerock.lang.cpp.syntax.preliminary.dispatch_type → type → bluerock.lang.cpp.syntax.preliminary.operator_impl.t obj_name type.

Arguments bluerock.lang.cpp.syntax.preliminary.operator_impl.t (obj_name type)%_type_scope
Arguments bluerock.lang.cpp.syntax.preliminary.operator_impl.Func {obj_name type}%_type_scope fn_name fn_type
Arguments bluerock.lang.cpp.syntax.preliminary.operator_impl.MFunc {obj_name type}%_type_scope fn_name _ fn_type

>>> Print bluerock.lang.cpp.syntax.preliminary.MethodRef_.
bluerock.lang.cpp.syntax.preliminary.MethodRef_ =
λ obj_name functype Expr : Set, (obj_name * bluerock.lang.cpp.syntax.preliminary.dispatch_type * functype + Expr)%type
     : Set → Set → Set → Set

Arguments bluerock.lang.cpp.syntax.preliminary.MethodRef_ (obj_name functype Expr)%_type_scope

>>> Print bluerock.lang.cpp.syntax.preliminary.OverloadableOperator.
Variant OverloadableOperator : Set :=
    OOTilde : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOExclaim : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPlusPlus : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOMinusMinus : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOStar : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPlus : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOMinus : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOSlash : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPercent : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOCaret : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOAmp : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPipe : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOLessLess : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOGreaterGreater : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPlusEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOMinusEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOStarEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOSlashEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPercentEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOCaretEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOAmpEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPipeEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOLessLessEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOGreaterGreaterEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOEqualEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOExclaimEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOLess : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOGreater : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOLessEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOGreaterEqual : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOSpaceship : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOComma : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOArrowStar : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOArrow : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOSubscript : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOAmpAmp : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOPipePipe : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OONew : Corelib.Init.Datatypes.bool → bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OODelete : Corelib.Init.Datatypes.bool → bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOCall : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
  | OOCoawait : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator.

Arguments bluerock.lang.cpp.syntax.preliminary.OONew array%_bool_scope
Arguments bluerock.lang.cpp.syntax.preliminary.OODelete array%_bool_scope

>>> Print bluerock.lang.cpp.syntax.preliminary.float_type.t.
Variant t : Set :=
    Ffloat16 : bluerock.lang.cpp.syntax.preliminary.float_type.t
  | Ffloat : bluerock.lang.cpp.syntax.preliminary.float_type.t
  | Fdouble : bluerock.lang.cpp.syntax.preliminary.float_type.t
  | Flongdouble : bluerock.lang.cpp.syntax.preliminary.float_type.t
  | Ffloat128 : bluerock.lang.cpp.syntax.preliminary.float_type.t.

>>> Print bluerock.lang.cpp.syntax.core.cast_style.t.
Variant t : Set :=
    functional : bluerock.lang.cpp.syntax.core.cast_style.t
  | c : bluerock.lang.cpp.syntax.core.cast_style.t
  | static : bluerock.lang.cpp.syntax.core.cast_style.t
  | dynamic : bluerock.lang.cpp.syntax.core.cast_style.t
  | reinterpret : bluerock.lang.cpp.syntax.core.cast_style.t
  | const : bluerock.lang.cpp.syntax.core.cast_style.t.

>>> Print bluerock.lang.cpp.syntax.literal_string.literal_string.t.
Record t : Set := Build_t { bytes : Corelib.Strings.PrimString.string;  bytes_per_char : Corelib.Numbers.BinNums.N }.

Arguments bluerock.lang.cpp.syntax.literal_string.literal_string.Build_t bytes%_pstring_scope bytes_per_char%_N_scope
Arguments bluerock.lang.cpp.syntax.literal_string.literal_string.bytes t
Arguments bluerock.lang.cpp.syntax.literal_string.literal_string.bytes_per_char t

>>> Print bluerock.lang.cpp.syntax.core.new_form.
Toplevel input, characters 6-44:
> Print bluerock.lang.cpp.syntax.core.new_form.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.lang.cpp.syntax.core.new_form not a defined object.

>>> Print bluerock.lang.cpp.syntax.core.AtomicOp.
Toplevel input, characters 6-44:
> Print bluerock.lang.cpp.syntax.core.AtomicOp.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.lang.cpp.syntax.core.AtomicOp not a defined object.

>>> Print bluerock.lang.cpp.syntax.preliminary.localname.
Notation localname := bluerock.lang.cpp.syntax.preliminary.localname.t

bluerock.lang.cpp.syntax.preliminary.localname.t = bluerock.lang.cpp.syntax.preliminary.ident
     : Set

## Assistant 33

I still need the definitions of a few core types to pattern‐match on them:

- `bluerock.lang.cpp.syntax.core.atomic_name_`
- `bluerock.lang.cpp.syntax.core.new_form`
- `bluerock.lang.cpp.syntax.core.AtomicOp`
- `bluerock.lang.cpp.syntax.preliminary.dispatch_type`

Once I have those, I can write the full mutually recursive `pp_…` functions over your entire syntax. Currently I cannot see those four, so please dump them:

```coqquery
Search "atomic_name_".
Print bluerock.lang.cpp.syntax.core.atomic_name_.
Search "new_form".
Print bluerock.lang.cpp.syntax.core.new_form.
Search "AtomicOp".
Print bluerock.lang.cpp.syntax.core.AtomicOp.
Print bluerock.lang.cpp.syntax.preliminary.dispatch_type.
```

## User 34

>>> Search "atomic_name_".
bluerock.lang.cpp.syntax.core.atomic_name_: Set → Set
bluerock.lang.cpp.syntax.core.atomic_name__inhabited: ∀ {A : Set}, stdpp.base.Inhabited (bluerock.lang.cpp.syntax.core.atomic_name_ A)
bluerock.lang.cpp.syntax.compare.atomic_name_compare:
  ∀ {A : Set}, bluerock.prelude.base.Compare A → bluerock.prelude.base.Compare (bluerock.lang.cpp.syntax.core.atomic_name_ A)
bluerock.lang.cpp.syntax.extras.atomic_name__eq_dec: ∀ {A : Set}, EqDecision A → EqDecision (bluerock.lang.cpp.syntax.core.atomic_name_ A)
bluerock.auto.cpp.name_pattern.atomic_name_sind:
  ∀ P : bluerock.auto.cpp.name_pattern.atomic_name → SProp,
    (∀ s : Corelib.Strings.PrimString.string, P (bluerock.auto.cpp.name_pattern.Aid s))
    → P bluerock.auto.cpp.name_pattern.Aany → ∀ a : bluerock.auto.cpp.name_pattern.atomic_name, P a
bluerock.auto.cpp.name_pattern.atomic_name_ind:
  ∀ P : bluerock.auto.cpp.name_pattern.atomic_name → Prop,
    (∀ s : Corelib.Strings.PrimString.string, P (bluerock.auto.cpp.name_pattern.Aid s))
    → P bluerock.auto.cpp.name_pattern.Aany → ∀ a : bluerock.auto.cpp.name_pattern.atomic_name, P a
bluerock.auto.cpp.name_pattern.atomic_name_rect:
  ∀ P : bluerock.auto.cpp.name_pattern.atomic_name → Type,
    (∀ s : Corelib.Strings.PrimString.string, P (bluerock.auto.cpp.name_pattern.Aid s))
    → P bluerock.auto.cpp.name_pattern.Aany → ∀ a : bluerock.auto.cpp.name_pattern.atomic_name, P a
bluerock.auto.cpp.name_pattern.atomic_name_rec:
  ∀ P : bluerock.auto.cpp.name_pattern.atomic_name → Set,
    (∀ s : Corelib.Strings.PrimString.string, P (bluerock.auto.cpp.name_pattern.Aid s))
    → P bluerock.auto.cpp.name_pattern.Aany → ∀ a : bluerock.auto.cpp.name_pattern.atomic_name, P a

>>> Print bluerock.lang.cpp.syntax.core.atomic_name_.
Variant atomic_name_ (type : Set) : Set :=
    Nid : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nfunction : bluerock.lang.cpp.syntax.core.function_qualifiers.t
                → bluerock.lang.cpp.syntax.preliminary.ident
                  → Corelib.Init.Datatypes.list type → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nctor : Corelib.Init.Datatypes.list type → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Ndtor : bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nop : bluerock.lang.cpp.syntax.core.function_qualifiers.t
          → bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
            → Corelib.Init.Datatypes.list type → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nop_conv : bluerock.lang.cpp.syntax.core.function_qualifiers.t → type → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nop_lit : bluerock.lang.cpp.syntax.preliminary.ident
              → Corelib.Init.Datatypes.list type → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nanon : Corelib.Numbers.BinNums.N → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nanonymous : bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nfirst_decl : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nfirst_child : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.atomic_name_ type
  | Nunsupported_atomic : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.core.atomic_name_ type.

Arguments bluerock.lang.cpp.syntax.core.atomic_name_ type%_type_scope
Arguments bluerock.lang.cpp.syntax.core.Nid {type}%_type_scope _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Nfunction {type}%_type_scope _ _%_pstring_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Nctor {type}%_type_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Ndtor {type}%_type_scope
Arguments bluerock.lang.cpp.syntax.core.Nop {type}%_type_scope _ _ _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Nop_conv {type}%_type_scope _ _
Arguments bluerock.lang.cpp.syntax.core.Nop_lit {type}%_type_scope _%_pstring_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.core.Nanon {type}%_type_scope _%_N_scope
Arguments bluerock.lang.cpp.syntax.core.Nanonymous {type}%_type_scope
Arguments bluerock.lang.cpp.syntax.core.Nfirst_decl {type}%_type_scope _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Nfirst_child {type}%_type_scope _%_pstring_scope
Arguments bluerock.lang.cpp.syntax.core.Nunsupported_atomic {type}%_type_scope _%_pstring_scope

>>> Search "new_form".
bluerock.lang.cpp.syntax.compare.new_form_compare: bluerock.prelude.base.Compare new_form

>>> Print bluerock.lang.cpp.syntax.core.new_form.
Toplevel input, characters 6-44:
> Print bluerock.lang.cpp.syntax.core.new_form.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.lang.cpp.syntax.core.new_form not a defined object.

>>> Search "AtomicOp".
bluerock.lang.cpp.syntax.compare.AtomicOp_compare: bluerock.prelude.base.Compare AtomicOp

>>> Print bluerock.lang.cpp.syntax.core.AtomicOp.
Toplevel input, characters 6-44:
> Print bluerock.lang.cpp.syntax.core.AtomicOp.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.lang.cpp.syntax.core.AtomicOp not a defined object.

>>> Print bluerock.lang.cpp.syntax.preliminary.dispatch_type.
Variant dispatch_type : Set :=
    Virtual : bluerock.lang.cpp.syntax.preliminary.dispatch_type | Direct : bluerock.lang.cpp.syntax.preliminary.dispatch_type.

## Assistant 34

I still need to locate and print the definitions of the two remaining syntax types `new_form` and `AtomicOp`.  Let’s ask Coq directly:

```coqquery
Locate AtomicOp.
Print AtomicOp.
Locate new_form.
Print new_form.
Search _ new_form.
```

## User 35

>>> Locate AtomicOp.
Notation bluerock.lang.cpp.syntax.preliminary.AtomicOp
Module bluerock.lang.cpp.syntax.preliminary.AtomicOp

>>> Print AtomicOp.
Notation AtomicOp := bluerock.lang.cpp.syntax.preliminary.AtomicOp.t

bluerock.lang.cpp.syntax.preliminary.AtomicOp.t = Corelib.Strings.PrimString.string
     : Set

>>> Locate new_form.
Notation bluerock.lang.cpp.syntax.preliminary.new_form
Module bluerock.lang.cpp.syntax.preliminary.new_form
Module bluerock.lang.cpp.syntax.compare.new_form (shorter name to refer to it in current context is compare.new_form)

>>> Print new_form.
Notation new_form := bluerock.lang.cpp.syntax.preliminary.new_form.t

Variant t : Set :=  Allocating : Corelib.Init.Datatypes.bool → new_form | NonAllocating : new_form.

Arguments bluerock.lang.cpp.syntax.preliminary.new_form.Allocating pass_align%_bool_scope

>>> Search _ new_form.
bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating: new_form
bluerock.lang.cpp.syntax.compare.Expr.box_Enew_2: bluerock.lang.cpp.syntax.compare.Expr.box_Enew → new_form
bluerock.lang.cpp.syntax.preliminary.new_form.Allocating: Corelib.Init.Datatypes.bool → new_form
bluerock.lang.cpp.syntax.compare.new_form_compare: bluerock.prelude.base.Compare new_form
bluerock.lang.cpp.syntax.compare.new_form.compare: new_form → new_form → Corelib.Init.Datatypes.comparison
bluerock.lang.cpp.syntax.preliminary.new_form.RelDecision_instance_0: EqDecision new_form
bluerock.lang.cpp.syntax.core.Enew:
  name * type
  → Corelib.Init.Datatypes.list Expr → new_form → type → Corelib.Init.Datatypes.option Expr → Corelib.Init.Datatypes.option Expr → Expr
bluerock.lang.cpp.syntax.compare.Expr.Box_Enew:
  name * type
  → Corelib.Init.Datatypes.list Expr
    → new_form
      → type → Corelib.Init.Datatypes.option Expr → Corelib.Init.Datatypes.option Expr → bluerock.lang.cpp.syntax.compare.Expr.box_Enew
bluerock.lang.cpp.syntax.core.Expr'_ind:
  ∀ P : Expr → Prop,
    (∀ i : bluerock.lang.cpp.syntax.preliminary.ident, P (bluerock.lang.cpp.syntax.core.Eparam i))
    → (∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_global n))
      → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RUnOp) (e : Expr), P e → P (bluerock.lang.cpp.syntax.core.Eunresolved_unop r e))
        → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RBinOp) (l : Expr),
             P l → ∀ r0 : Expr, P r0 → P (bluerock.lang.cpp.syntax.core.Eunresolved_binop r l r0))
          → (∀ (on : name) (l : Corelib.Init.Datatypes.list Expr), P (bluerock.lang.cpp.syntax.core.Eunresolved_call on l))
            → (∀ (on : name) (e : Expr),
                 P e → ∀ l : Corelib.Init.Datatypes.list Expr, P (bluerock.lang.cpp.syntax.core.Eunresolved_member_call on e l))
              → (∀ (o : Corelib.Init.Datatypes.option type) (l : Corelib.Init.Datatypes.list Expr),
                   P (bluerock.lang.cpp.syntax.core.Eunresolved_parenlist o l))
                → (∀ e : Expr, P e → ∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_member e n))
                  → (∀ (t : localname) (t0 : type), P (bluerock.lang.cpp.syntax.core.Evar t t0))
                    → (∀ (gn : name) (i : bluerock.lang.cpp.syntax.preliminary.ident), P (bluerock.lang.cpp.syntax.core.Eenum_const gn i))
                      → (∀ (on : name) (t : type), P (bluerock.lang.cpp.syntax.core.Eglobal on t))
                        → (∀ (gn : name) (ty : type), P (bluerock.lang.cpp.syntax.core.Eglobal_member gn ty))
                          → (∀ (c : Corelib.Numbers.BinNums.N) (t : type), P (bluerock.lang.cpp.syntax.core.Echar c t))
                            → (∀ (s : bluerock.lang.cpp.syntax.literal_string.literal_string.t) (t : type),
                                 P (bluerock.lang.cpp.syntax.core.Estring s t))
                              → (∀ (n : Corelib.Numbers.BinNums.Z) (t : type), P (bluerock.lang.cpp.syntax.core.Eint n t))
                                → (∀ b : Corelib.Init.Datatypes.bool, P (bluerock.lang.cpp.syntax.core.Ebool b))
                                  → (∀ (op : bluerock.lang.cpp.syntax.preliminary.UnOp) (e : Expr),
                                       P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eunop op e t))
                                    → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                         P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ebinop op e1 e2 t))
                                      → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ederef e t))
                                        → (∀ e : Expr, P e → P (bluerock.lang.cpp.syntax.core.Eaddrof e))
                                          → (∀ e1 : Expr,
                                               P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign e1 e2 t))
                                            → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                                 P e1
                                                 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign_op op e1 e2 t))
                                              → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epreinc e t))
                                                → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostinc e t))
                                                  → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epredec e t))
                                                    → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostdec e t))
                                                      → (∀ e1 : Expr,
                                                           P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqand e1 e2))
                                                        → (∀ e1 : Expr,
                                                             P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqor e1 e2))
                                                          → (∀ e1 : Expr,
                                                               P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Ecomma e1 e2))
                                                            → (∀ f : Expr,
                                                                 P f
                                                                 → ∀ es : Corelib.Init.Datatypes.list Expr,
                                                                     P (bluerock.lang.cpp.syntax.core.Ecall f es))
                                                              → (∀ (c : bluerock.lang.cpp.syntax.core.cast_style.t) (t : type) (e : Expr),
                                                                   P e → P (bluerock.lang.cpp.syntax.core.Eexplicit_cast c t e))
                                                                → (∀ (c : Cast) (e : Expr),
                                                                     P e → P (bluerock.lang.cpp.syntax.core.Ecast c e))
                                                                  → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                       P obj
                                                                       → ∀ (f : bluerock.lang.cpp.syntax.core.atomic_name_ type) 
                                                                           (mut : Corelib.Init.Datatypes.bool) (t : type),
                                                                           P (bluerock.lang.cpp.syntax.core.Emember arrow obj f mut t))
                                                                    → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                         P obj
                                                                         → ∀ res : Expr,
                                                                             P res
                                                                             → P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_ignore arrow obj res))
                                                                      → (∀ (arrow : Corelib.Init.Datatypes.bool) 
                                                                           (method : bluerock.lang.cpp.syntax.preliminary.MethodRef_ name
                                                                                       type Expr) (obj : Expr),
                                                                           P obj
                                                                           → ∀ args : Corelib.Init.Datatypes.list Expr,
                                                                               P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_call arrow method
                                                                                    obj args))
                                                                        → (∀ (o : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) 
                                                                             (t : bluerock.lang.cpp.syntax.preliminary.operator_impl.t name
                                                                                    type) (l : Corelib.Init.Datatypes.list Expr),
                                                                             P (bluerock.lang.cpp.syntax.core.Eoperator_call o t l))
                                                                          → (∀ e1 : Expr, P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (...))
                                                                            → (∀ (s : type + Expr) (t : type),
                                                                                 P (bluerock.lang.cpp.syntax.core.Esizeof s t))
                                                                              → (∀ (s : type + Expr) (t : type),
                                                                                   P (bluerock.lang.cpp.syntax.core.Ealignof s t))
                                                                                → (∀ (gn : type) (i : bluerock.lang.cpp.syntax.preliminary.ident) 
                                                                                     (t : type),
                                                                                     P (bluerock.lang.cpp.syntax.core.Eoffsetof gn i t))
                                                                                  → (∀ (on : name) (args : ...) (t : type), P (...))
                                                                                    → (∀ ... ..., P ...) → (..., ...) → (...) → ... → ...
bluerock.lang.cpp.syntax.core.Expr'_rec:
  ∀ P : Expr → Set,
    (∀ i : bluerock.lang.cpp.syntax.preliminary.ident, P (bluerock.lang.cpp.syntax.core.Eparam i))
    → (∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_global n))
      → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RUnOp) (e : Expr), P e → P (bluerock.lang.cpp.syntax.core.Eunresolved_unop r e))
        → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RBinOp) (l : Expr),
             P l → ∀ r0 : Expr, P r0 → P (bluerock.lang.cpp.syntax.core.Eunresolved_binop r l r0))
          → (∀ (on : name) (l : Corelib.Init.Datatypes.list Expr), P (bluerock.lang.cpp.syntax.core.Eunresolved_call on l))
            → (∀ (on : name) (e : Expr),
                 P e → ∀ l : Corelib.Init.Datatypes.list Expr, P (bluerock.lang.cpp.syntax.core.Eunresolved_member_call on e l))
              → (∀ (o : Corelib.Init.Datatypes.option type) (l : Corelib.Init.Datatypes.list Expr),
                   P (bluerock.lang.cpp.syntax.core.Eunresolved_parenlist o l))
                → (∀ e : Expr, P e → ∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_member e n))
                  → (∀ (t : localname) (t0 : type), P (bluerock.lang.cpp.syntax.core.Evar t t0))
                    → (∀ (gn : name) (i : bluerock.lang.cpp.syntax.preliminary.ident), P (bluerock.lang.cpp.syntax.core.Eenum_const gn i))
                      → (∀ (on : name) (t : type), P (bluerock.lang.cpp.syntax.core.Eglobal on t))
                        → (∀ (gn : name) (ty : type), P (bluerock.lang.cpp.syntax.core.Eglobal_member gn ty))
                          → (∀ (c : Corelib.Numbers.BinNums.N) (t : type), P (bluerock.lang.cpp.syntax.core.Echar c t))
                            → (∀ (s : bluerock.lang.cpp.syntax.literal_string.literal_string.t) (t : type),
                                 P (bluerock.lang.cpp.syntax.core.Estring s t))
                              → (∀ (n : Corelib.Numbers.BinNums.Z) (t : type), P (bluerock.lang.cpp.syntax.core.Eint n t))
                                → (∀ b : Corelib.Init.Datatypes.bool, P (bluerock.lang.cpp.syntax.core.Ebool b))
                                  → (∀ (op : bluerock.lang.cpp.syntax.preliminary.UnOp) (e : Expr),
                                       P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eunop op e t))
                                    → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                         P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ebinop op e1 e2 t))
                                      → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ederef e t))
                                        → (∀ e : Expr, P e → P (bluerock.lang.cpp.syntax.core.Eaddrof e))
                                          → (∀ e1 : Expr,
                                               P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign e1 e2 t))
                                            → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                                 P e1
                                                 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign_op op e1 e2 t))
                                              → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epreinc e t))
                                                → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostinc e t))
                                                  → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epredec e t))
                                                    → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostdec e t))
                                                      → (∀ e1 : Expr,
                                                           P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqand e1 e2))
                                                        → (∀ e1 : Expr,
                                                             P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqor e1 e2))
                                                          → (∀ e1 : Expr,
                                                               P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Ecomma e1 e2))
                                                            → (∀ f : Expr,
                                                                 P f
                                                                 → ∀ es : Corelib.Init.Datatypes.list Expr,
                                                                     P (bluerock.lang.cpp.syntax.core.Ecall f es))
                                                              → (∀ (c : bluerock.lang.cpp.syntax.core.cast_style.t) (t : type) (e : Expr),
                                                                   P e → P (bluerock.lang.cpp.syntax.core.Eexplicit_cast c t e))
                                                                → (∀ (c : Cast) (e : Expr),
                                                                     P e → P (bluerock.lang.cpp.syntax.core.Ecast c e))
                                                                  → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                       P obj
                                                                       → ∀ (f : bluerock.lang.cpp.syntax.core.atomic_name_ type) 
                                                                           (mut : Corelib.Init.Datatypes.bool) (t : type),
                                                                           P (bluerock.lang.cpp.syntax.core.Emember arrow obj f mut t))
                                                                    → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                         P obj
                                                                         → ∀ res : Expr,
                                                                             P res
                                                                             → P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_ignore arrow obj res))
                                                                      → (∀ (arrow : Corelib.Init.Datatypes.bool) 
                                                                           (method : bluerock.lang.cpp.syntax.preliminary.MethodRef_ name
                                                                                       type Expr) (obj : Expr),
                                                                           P obj
                                                                           → ∀ args : Corelib.Init.Datatypes.list Expr,
                                                                               P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_call arrow method
                                                                                    obj args))
                                                                        → (∀ (o : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) 
                                                                             (t : bluerock.lang.cpp.syntax.preliminary.operator_impl.t name
                                                                                    type) (l : Corelib.Init.Datatypes.list Expr),
                                                                             P (bluerock.lang.cpp.syntax.core.Eoperator_call o t l))
                                                                          → (∀ e1 : Expr, P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (...))
                                                                            → (∀ (s : type + Expr) (t : type),
                                                                                 P (bluerock.lang.cpp.syntax.core.Esizeof s t))
                                                                              → (∀ (s : type + Expr) (t : type),
                                                                                   P (bluerock.lang.cpp.syntax.core.Ealignof s t))
                                                                                → (∀ (gn : type) (i : bluerock.lang.cpp.syntax.preliminary.ident) 
                                                                                     (t : type),
                                                                                     P (bluerock.lang.cpp.syntax.core.Eoffsetof gn i t))
                                                                                  → (∀ (on : name) (args : ...) (t : type), P (...))
                                                                                    → (∀ ... ..., P ...) → (..., ...) → (...) → ... → ...
bluerock.lang.cpp.syntax.core.Expr'_rect:
  ∀ P : Expr → Type,
    (∀ i : bluerock.lang.cpp.syntax.preliminary.ident, P (bluerock.lang.cpp.syntax.core.Eparam i))
    → (∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_global n))
      → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RUnOp) (e : Expr), P e → P (bluerock.lang.cpp.syntax.core.Eunresolved_unop r e))
        → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RBinOp) (l : Expr),
             P l → ∀ r0 : Expr, P r0 → P (bluerock.lang.cpp.syntax.core.Eunresolved_binop r l r0))
          → (∀ (on : name) (l : Corelib.Init.Datatypes.list Expr), P (bluerock.lang.cpp.syntax.core.Eunresolved_call on l))
            → (∀ (on : name) (e : Expr),
                 P e → ∀ l : Corelib.Init.Datatypes.list Expr, P (bluerock.lang.cpp.syntax.core.Eunresolved_member_call on e l))
              → (∀ (o : Corelib.Init.Datatypes.option type) (l : Corelib.Init.Datatypes.list Expr),
                   P (bluerock.lang.cpp.syntax.core.Eunresolved_parenlist o l))
                → (∀ e : Expr, P e → ∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_member e n))
                  → (∀ (t : localname) (t0 : type), P (bluerock.lang.cpp.syntax.core.Evar t t0))
                    → (∀ (gn : name) (i : bluerock.lang.cpp.syntax.preliminary.ident), P (bluerock.lang.cpp.syntax.core.Eenum_const gn i))
                      → (∀ (on : name) (t : type), P (bluerock.lang.cpp.syntax.core.Eglobal on t))
                        → (∀ (gn : name) (ty : type), P (bluerock.lang.cpp.syntax.core.Eglobal_member gn ty))
                          → (∀ (c : Corelib.Numbers.BinNums.N) (t : type), P (bluerock.lang.cpp.syntax.core.Echar c t))
                            → (∀ (s : bluerock.lang.cpp.syntax.literal_string.literal_string.t) (t : type),
                                 P (bluerock.lang.cpp.syntax.core.Estring s t))
                              → (∀ (n : Corelib.Numbers.BinNums.Z) (t : type), P (bluerock.lang.cpp.syntax.core.Eint n t))
                                → (∀ b : Corelib.Init.Datatypes.bool, P (bluerock.lang.cpp.syntax.core.Ebool b))
                                  → (∀ (op : bluerock.lang.cpp.syntax.preliminary.UnOp) (e : Expr),
                                       P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eunop op e t))
                                    → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                         P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ebinop op e1 e2 t))
                                      → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ederef e t))
                                        → (∀ e : Expr, P e → P (bluerock.lang.cpp.syntax.core.Eaddrof e))
                                          → (∀ e1 : Expr,
                                               P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign e1 e2 t))
                                            → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                                 P e1
                                                 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign_op op e1 e2 t))
                                              → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epreinc e t))
                                                → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostinc e t))
                                                  → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epredec e t))
                                                    → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostdec e t))
                                                      → (∀ e1 : Expr,
                                                           P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqand e1 e2))
                                                        → (∀ e1 : Expr,
                                                             P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqor e1 e2))
                                                          → (∀ e1 : Expr,
                                                               P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Ecomma e1 e2))
                                                            → (∀ f : Expr,
                                                                 P f
                                                                 → ∀ es : Corelib.Init.Datatypes.list Expr,
                                                                     P (bluerock.lang.cpp.syntax.core.Ecall f es))
                                                              → (∀ (c : bluerock.lang.cpp.syntax.core.cast_style.t) (t : type) (e : Expr),
                                                                   P e → P (bluerock.lang.cpp.syntax.core.Eexplicit_cast c t e))
                                                                → (∀ (c : Cast) (e : Expr),
                                                                     P e → P (bluerock.lang.cpp.syntax.core.Ecast c e))
                                                                  → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                       P obj
                                                                       → ∀ (f : bluerock.lang.cpp.syntax.core.atomic_name_ type) 
                                                                           (mut : Corelib.Init.Datatypes.bool) (t : type),
                                                                           P (bluerock.lang.cpp.syntax.core.Emember arrow obj f mut t))
                                                                    → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                         P obj
                                                                         → ∀ res : Expr,
                                                                             P res
                                                                             → P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_ignore arrow obj res))
                                                                      → (∀ (arrow : Corelib.Init.Datatypes.bool) 
                                                                           (method : bluerock.lang.cpp.syntax.preliminary.MethodRef_ name
                                                                                       type Expr) (obj : Expr),
                                                                           P obj
                                                                           → ∀ args : Corelib.Init.Datatypes.list Expr,
                                                                               P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_call arrow method
                                                                                    obj args))
                                                                        → (∀ (o : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) 
                                                                             (t : bluerock.lang.cpp.syntax.preliminary.operator_impl.t name
                                                                                    type) (l : Corelib.Init.Datatypes.list Expr),
                                                                             P (bluerock.lang.cpp.syntax.core.Eoperator_call o t l))
                                                                          → (∀ e1 : Expr, P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (...))
                                                                            → (∀ (s : type + Expr) (t : type),
                                                                                 P (bluerock.lang.cpp.syntax.core.Esizeof s t))
                                                                              → (∀ (s : type + Expr) (t : type),
                                                                                   P (bluerock.lang.cpp.syntax.core.Ealignof s t))
                                                                                → (∀ (gn : type) (i : bluerock.lang.cpp.syntax.preliminary.ident) 
                                                                                     (t : type),
                                                                                     P (bluerock.lang.cpp.syntax.core.Eoffsetof gn i t))
                                                                                  → (∀ (on : name) (args : ...) (t : type), P (...))
                                                                                    → (∀ ... ..., P ...) → (..., ...) → (...) → ... → ...
bluerock.lang.cpp.syntax.core.Expr'_sind:
  ∀ P : Expr → SProp,
    (∀ i : bluerock.lang.cpp.syntax.preliminary.ident, P (bluerock.lang.cpp.syntax.core.Eparam i))
    → (∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_global n))
      → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RUnOp) (e : Expr), P e → P (bluerock.lang.cpp.syntax.core.Eunresolved_unop r e))
        → (∀ (r : bluerock.lang.cpp.syntax.overloadable.RBinOp) (l : Expr),
             P l → ∀ r0 : Expr, P r0 → P (bluerock.lang.cpp.syntax.core.Eunresolved_binop r l r0))
          → (∀ (on : name) (l : Corelib.Init.Datatypes.list Expr), P (bluerock.lang.cpp.syntax.core.Eunresolved_call on l))
            → (∀ (on : name) (e : Expr),
                 P e → ∀ l : Corelib.Init.Datatypes.list Expr, P (bluerock.lang.cpp.syntax.core.Eunresolved_member_call on e l))
              → (∀ (o : Corelib.Init.Datatypes.option type) (l : Corelib.Init.Datatypes.list Expr),
                   P (bluerock.lang.cpp.syntax.core.Eunresolved_parenlist o l))
                → (∀ e : Expr, P e → ∀ n : name, P (bluerock.lang.cpp.syntax.core.Eunresolved_member e n))
                  → (∀ (t : localname) (t0 : type), P (bluerock.lang.cpp.syntax.core.Evar t t0))
                    → (∀ (gn : name) (i : bluerock.lang.cpp.syntax.preliminary.ident), P (bluerock.lang.cpp.syntax.core.Eenum_const gn i))
                      → (∀ (on : name) (t : type), P (bluerock.lang.cpp.syntax.core.Eglobal on t))
                        → (∀ (gn : name) (ty : type), P (bluerock.lang.cpp.syntax.core.Eglobal_member gn ty))
                          → (∀ (c : Corelib.Numbers.BinNums.N) (t : type), P (bluerock.lang.cpp.syntax.core.Echar c t))
                            → (∀ (s : bluerock.lang.cpp.syntax.literal_string.literal_string.t) (t : type),
                                 P (bluerock.lang.cpp.syntax.core.Estring s t))
                              → (∀ (n : Corelib.Numbers.BinNums.Z) (t : type), P (bluerock.lang.cpp.syntax.core.Eint n t))
                                → (∀ b : Corelib.Init.Datatypes.bool, P (bluerock.lang.cpp.syntax.core.Ebool b))
                                  → (∀ (op : bluerock.lang.cpp.syntax.preliminary.UnOp) (e : Expr),
                                       P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eunop op e t))
                                    → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                         P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ebinop op e1 e2 t))
                                      → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Ederef e t))
                                        → (∀ e : Expr, P e → P (bluerock.lang.cpp.syntax.core.Eaddrof e))
                                          → (∀ e1 : Expr,
                                               P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign e1 e2 t))
                                            → (∀ (op : bluerock.lang.cpp.syntax.preliminary.BinOp) (e1 : Expr),
                                                 P e1
                                                 → ∀ e2 : Expr, P e2 → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Eassign_op op e1 e2 t))
                                              → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epreinc e t))
                                                → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostinc e t))
                                                  → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epredec e t))
                                                    → (∀ e : Expr, P e → ∀ t : type, P (bluerock.lang.cpp.syntax.core.Epostdec e t))
                                                      → (∀ e1 : Expr,
                                                           P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqand e1 e2))
                                                        → (∀ e1 : Expr,
                                                             P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Eseqor e1 e2))
                                                          → (∀ e1 : Expr,
                                                               P e1 → ∀ e2 : Expr, P e2 → P (bluerock.lang.cpp.syntax.core.Ecomma e1 e2))
                                                            → (∀ f : Expr,
                                                                 P f
                                                                 → ∀ es : Corelib.Init.Datatypes.list Expr,
                                                                     P (bluerock.lang.cpp.syntax.core.Ecall f es))
                                                              → (∀ (c : bluerock.lang.cpp.syntax.core.cast_style.t) (t : type) (e : Expr),
                                                                   P e → P (bluerock.lang.cpp.syntax.core.Eexplicit_cast c t e))
                                                                → (∀ (c : Cast) (e : Expr),
                                                                     P e → P (bluerock.lang.cpp.syntax.core.Ecast c e))
                                                                  → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                       P obj
                                                                       → ∀ (f : bluerock.lang.cpp.syntax.core.atomic_name_ type) 
                                                                           (mut : Corelib.Init.Datatypes.bool) (t : type),
                                                                           P (bluerock.lang.cpp.syntax.core.Emember arrow obj f mut t))
                                                                    → (∀ (arrow : Corelib.Init.Datatypes.bool) (obj : Expr),
                                                                         P obj
                                                                         → ∀ res : Expr,
                                                                             P res
                                                                             → P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_ignore arrow obj res))
                                                                      → (∀ (arrow : Corelib.Init.Datatypes.bool) 
                                                                           (method : bluerock.lang.cpp.syntax.preliminary.MethodRef_ name
                                                                                       type Expr) (obj : Expr),
                                                                           P obj
                                                                           → ∀ args : Corelib.Init.Datatypes.list Expr,
                                                                               P
                                                                                 (bluerock.lang.cpp.syntax.core.Emember_call arrow method
                                                                                    obj args))
                                                                        → (∀ (o : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) 
                                                                             (t : bluerock.lang.cpp.syntax.preliminary.operator_impl.t name
                                                                                    type) (l : Corelib.Init.Datatypes.list Expr),
                                                                             P (bluerock.lang.cpp.syntax.core.Eoperator_call o t l))
                                                                          → (∀ e1 : Expr, P e1 → ∀ e2 : Expr, P e2 → ∀ t : type, P (...))
                                                                            → (∀ (s : type + Expr) (t : type),
                                                                                 P (bluerock.lang.cpp.syntax.core.Esizeof s t))
                                                                              → (∀ (s : type + Expr) (t : type),
                                                                                   P (bluerock.lang.cpp.syntax.core.Ealignof s t))
                                                                                → (∀ (gn : type) (i : bluerock.lang.cpp.syntax.preliminary.ident) 
                                                                                     (t : type),
                                                                                     P (bluerock.lang.cpp.syntax.core.Eoffsetof gn i t))
                                                                                  → (∀ (on : name) (args : ...) (t : type), P (...))
                                                                                    → (∀ ... ..., P ...) → (..., ...) → (...) → ... → ...

## Assistant 35

I also need the definitions of the “RUnOp” and “RBinOp” types used in the unresolved‐calls so that I can generate their `match` cases. Please dump those two:

```coqquery
Print bluerock.lang.cpp.syntax.overloadable.RUnOp.
Print bluerock.lang.cpp.syntax.overloadable.RBinOp.
```

## User 36

>>> Print bluerock.lang.cpp.syntax.overloadable.RUnOp.
Variant RUnOp : Set :=
    Runop : bluerock.lang.cpp.syntax.preliminary.UnOp → bluerock.lang.cpp.syntax.overloadable.RUnOp
  | Rpreinc : bluerock.lang.cpp.syntax.overloadable.RUnOp
  | Rpredec : bluerock.lang.cpp.syntax.overloadable.RUnOp
  | Rpostinc : bluerock.lang.cpp.syntax.overloadable.RUnOp
  | Rpostdec : bluerock.lang.cpp.syntax.overloadable.RUnOp
  | Rstar : bluerock.lang.cpp.syntax.overloadable.RUnOp
  | Rarrow : bluerock.lang.cpp.syntax.overloadable.RUnOp.

Arguments bluerock.lang.cpp.syntax.overloadable.Runop op%_CPP_expr_scope

>>> Print bluerock.lang.cpp.syntax.overloadable.RBinOp.
Variant RBinOp : Set :=
    Rbinop : bluerock.lang.cpp.syntax.preliminary.BinOp → bluerock.lang.cpp.syntax.overloadable.RBinOp
  | Rassign : bluerock.lang.cpp.syntax.overloadable.RBinOp
  | Rassign_op : bluerock.lang.cpp.syntax.preliminary.BinOp → bluerock.lang.cpp.syntax.overloadable.RBinOp
  | Rsubscript : bluerock.lang.cpp.syntax.overloadable.RBinOp.

Arguments bluerock.lang.cpp.syntax.overloadable.Rbinop op%_CPP_expr_scope
Arguments bluerock.lang.cpp.syntax.overloadable.Rassign_op op%_CPP_expr_scope

## Assistant 36

Below is a first‐cut of a mutually recursive pretty‐printer over your entire C++ syntax AST.  Low‐level “missing” pieces (number→string, some operator names, full cast cases, etc.) are left as `Admitted` or marked `(* TOFIXLATER *)`.  All recursive calls are in place so Coq’s termination checker will accept the definition.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A->string) (l:list A) : string :=
  match l with
  | [] => ""
  | x::xs => fold_left (fun acc y => acc ++ "," ++ ppA y) xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z:Z) : string. Admitted.               (* TOFIXLATER *)
Definition pp_N (n:N) : string. Admitted.                (* TOFIXLATER *)
Definition pp_binop (b:bluerock.lang.cpp.syntax.preliminary.BinOp) : string. Admitted.  (* TOFIXLATER *)
Definition pp_r_binop (b:bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted. (* TOFIXLATER *)
Definition pp_cast_style (c:bluerock.lang.cpp.syntax.core.cast_style.t) : string.
Admitted.  (* TOFIXLATER *)
Definition pp_atomic_name {T} (a:bluerock.lang.cpp.syntax.core.atomic_name_ T) : string.
Admitted.  (* TOFIXLATER *)
Definition pp_function_qualifiers (q:bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string.
Admitted.  (* TOFIXLATER *)
Definition pp_method_ref (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr) : string.
Admitted.  (* TOFIXLATER *)
Definition pp_operator_impl (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type) : string.
Admitted.  (* TOFIXLATER *)
Definition pp_overloadable_op (oop: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string.
Admitted.  (* TOFIXLATER *)
Definition pp_float_type (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string.
Admitted.  (* TOFIXLATER *)

Definition pp_literal_string (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string :=
  ls.(bytes).  (* very rough; could add quotes, escape, etc. TOFIXLATER *)

Definition pp_new_form (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t) : string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b => "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating => ""
  end.

Definition pp_atomicop (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t) : string := ao.

(* Now the big mutual Fixpoint: *)
Mutual Fixpoint
  pp_name (n:name) : string :=
    match n with
    | Ninst base args => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
    | Nglobal an      => pp_atomic_name an
    | Ndependent t    => "dependent(" ++ pp_type t ++ ")"
    | Nscoped base an => pp_name base ++ "::" ++ pp_atomic_name an
    | Nunsupported s  => s
    end

  with pp_temp_arg (a:temp_arg) : string :=
    match a with
    | Atype t       => pp_type t
    | Avalue e      => pp_expr e
    | Apack args    => "pack<" ++ pp_list pp_temp_arg args ++ ">"
    | Atemplate n   => pp_name n
    | Aunsupported s=> s
    end

  with pp_type (t:type) : string :=
    match t with
    | Tparam id              => id
    | Tresult_param id       => id
    | Tresult_global n       => pp_name n
    | Tresult_unop r t1      => pp_r_unop r ++ pp_type t1
    | Tresult_binop r t1 t2  => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
    | Tresult_call n ts      => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member_call n t1 ts
                             => pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_parenlist t1 ts
                             => "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member t1 n    => pp_type t1 ++ "::" ++ pp_name n
    | Tptr t1                => pp_type t1 ++ "*"
    | Tref t1                => pp_type t1 ++ "&"
    | Trv_ref t1             => pp_type t1 ++ "&&"
    | Tnum sz sgn            => "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
    | Tchar_ ct              => "(char)"
    | Tvoid                  => "void"
    | Tarray t1 n            => pp_type t1 ++ "[" ++ pp_N n ++ "]"
    | Tincomplete_array t1   => pp_type t1 ++ "[]"
    | Tvariable_array t1 e1  => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
    | Tnamed n               => pp_name n
    | Tenum n                => "enum " ++ pp_name n
    | Tfunction ft           =>
        let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
        let ps  := (bluerock.lang.cpp.syntax.core.function_type_ params) ft in
        "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
    | Tbool                  => "bool"
    | Tmember_pointer t1 t2  => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
    | Tfloat_ ft             => pp_float_type ft
    | Tqualified _ t1        => pp_type t1
    | Tnullptr               => "nullptr_t"
    | Tarch osz name         => "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++ "," ++ name ++ ")"
    | Tdecltype e1           => "decltype(" ++ pp_expr e1 ++ ")"
    | Texprtype e1           => "typeof(" ++ pp_expr e1 ++ ")"
    | Tunsupported s         => s
    end

  with pp_expr (e:Expr) : string :=
    match e with
    | Eparam id                   => id
    | Eunresolved_global n        => pp_name n
    | Eunresolved_unop r e1       => pp_r_unop r ++ pp_expr e1
    | Eunresolved_binop r l r2    => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
    | Eunresolved_call n es       => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member_call n e1 es
                                  => pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist None es
                                  => "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist (Some t1) es
                                  => "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member e1 n     => pp_expr e1 ++ "." ++ pp_name n
    | Evar ln _t                  => ln
    | Eenum_const n id            => pp_name n ++ "::" ++ id
    | Eglobal n _t                => pp_name n
    | Eglobal_member n _t         => pp_name n
    | Echar c _t                  => pp_int (Z.of_N c)
    | Estring s _t                => pp_literal_string s
    | Eint n _t                   => pp_int n
    | Ebool b                     => if b then "true" else "false"
    | Eunop op e1 _t              => pp_unop op ++ pp_expr e1
    | Ebinop op e1 e2 _t          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
    | Ederef e1 _t                => "*" ++ pp_expr e1
    | Eaddrof e1                  => "&" ++ pp_expr e1
    | Eassign e1 e2 _t            => pp_expr e1 ++ "=" ++ pp_expr e2
    | Eassign_op op e1 e2 _t      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
    | Epreinc e1 _t               => "++" ++ pp_expr e1
    | Epostinc e1 _t              => pp_expr e1 ++ "++"
    | Epredec e1 _t               => "--" ++ pp_expr e1
    | Epostdec e1 _t              => pp_expr e1 ++ "--"
    | Eseqand e1 e2               => pp_expr e1 ++ "&&" ++ pp_expr e2
    | Eseqor e1 e2                => pp_expr e1 ++ "||" ++ pp_expr e2
    | Ecomma e1 e2                => pp_expr e1 ++ "," ++ pp_expr e2
    | Ecall f es                  => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eexplicit_cast cs t1 e1     => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
    | Ecast c e1                  => pp_cast c ++ pp_expr e1
    | Emember arrow obj fn _ _    => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
    | Emember_ignore arrow obj res
                                  => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
    | Emember_call arrow mr obj es
                                  => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eoperator_call oop impl es  => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
    | Esubscript e1 e2 _t         => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
    | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
    | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
    | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
    | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
    | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
    | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Elambda id caps             => "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
    | Eimplicit e1                => pp_expr e1
    | Eimplicit_init _t           => ""
    | Eif cond thn els _t         => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Ethis _t                    => "this"
    | Enull                       => "nullptr"
    | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
    | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
    | Einitlist_union nm def _    => pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
    | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
    | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
    | Eandclean a b               => pp_expr a ++ "," ++ pp_expr b
    | Ematerialize_temp e1 _      => pp_expr e1
    | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
    | Estmt s _                   => pp_stmt s
    | Eva_arg e1 _                => pp_expr e1
    | Epseudo_destructor _ _ e1   => pp_expr e1
    | Earrayloop_init _ src _ _ _ _
                                  => pp_expr src
    | Earrayloop_index lvl _      => pp_N lvl
    | Eopaque_ref lvl _           => pp_N lvl
    | Eunsupported s _            => s
    end

  with pp_stmt (s:Stmt) : string :=
    match s with
    | Sseq ss       => "{ " ++ pp_list pp_stmt ss ++ " }"
    | Sdecl ds      => "decl " ++ pp_list pp_vardecl ds
    | Sif None c t e
                    => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
    | Sif Some d c t e
                    => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
    | Sif_consteval t e
                    => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
    | Swhile None c b
                    => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
    | Swhile Some d c b
                    => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
    | Sfor i c s b  =>
        "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end)
         ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end)
         ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end)
         ++ ")" ++ pp_stmt b
    | Sdo b c       => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
    | Sswitch None e b
                    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
    | Sswitch Some d e b
                    => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
    | Scase br b    => "case ...: " ++ pp_stmt b    (* branch details TOFIXLATER *)
    | Sdefault      => "default:"
    | Sbreak        => "break;"
    | Scontinue     => "continue;"
    | Sreturn None  => "return;"
    | Sreturn Some e=> "return " ++ pp_expr e ++ ";"
    | Sexpr e       => pp_expr e ++ ";"
    | Sattr as s0   => "[[" ++ pp_list (fun i=>i) as ++ "]] " ++ pp_stmt s0
    | Sasm s0 _ _ _ _ => "asm " ++ s0           (* inputs/outputs/clobbers TOFIXLATER *)
    | Slabeled id s0=> id ++ ": " ++ pp_stmt s0
    | Sgoto id      => "goto " ++ id ++ ";"
    | Sunsupported s0 => s0
    end

  with pp_vardecl (d:VarDecl) : string :=
    match d with
    | Dvar ln _ None   => ln
    | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
    | Ddecompose e id bs
                        => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{"
                            ++ pp_list pp_binding bs ++ "}"
    | Dinit b n _ None => "init " ++ pp_name n
    | Dinit b n _ Some e
                        => "init " ++ pp_name n ++ "=" ++ pp_expr e
    end

  with pp_binding (b:BindingDecl) : string :=
    match b with
    | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
    | Bbind ln _ e => ln ++ "=" ++ pp_expr e
    end

  with pp_cast (c:Cast) : string :=
    match c with
    | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
    | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
    | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
    | Cl2r               => "l2r"              (* TOFIXLATER: add angle<> if needed *)
    | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
    | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
    | Carray2ptr         => "array2ptr"
    | Cfun2ptr           => "fun2ptr"
    | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
    | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
    | Cptr2bool          => "ptr2bool"
    | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
    | Cint2bool          => "int2bool"
    | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
    | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
    | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
    | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
    | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
    | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
    | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
    | Cuser              => "user_cast"
    | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
    | Cderived2base ps t => "derived2base"
    | Cbase2derived ps t => "base2derived"
    | Cunsupported _ _   => "unsupported_cast"
    end.
```

All recursive calls are structural on the AST.  You can now fill in the `Admitted` stubs and tweak formatting as needed.

## User 37

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 135-138:
>   | x::xs => fold_left (fun acc y => acc ++ "," ++ ppA y) xs (ppA x)
>                                             ^^^
Error:
In environment
A : Type
ppA : A → Corelib.Strings.PrimString.string
l : Corelib.Init.Datatypes.list A
x : A
xs : Corelib.Init.Datatypes.list A
acc : Corelib.Init.Datatypes.list ?A
y : ?B
The term "","" has type "Corelib.Strings.PrimString.string" while it is expected to have type "Corelib.Init.Datatypes.list ?A0".


## Assistant 37

Coq is complaining because in

     acc ++ "," ++ ppA y

the notation `++` is the _list_ append (from `list_scope`), so it expects both operands to be lists.  But `","` is a `PrimString.string`, not a `list _`.  Thus we get a mismatch: string vs list.

To fix this we must use the _string_ append operation, not the list append.  The easiest way is to avoid `++` here entirely and explicitly call the `PrimString.append` function.  We also avoid using `List.fold_left` (to keep things structurally recursive), replacing it with a small local `fix`.

Below is the complete, fixed pretty‐printer.  I’ve replaced `pp_list` with a structural‐recursive version that uses `Corelib.Strings.PrimString.append` for strings.  Everything else is as before.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc' := Corelib.Strings.PrimString.append acc "," in
           let acc'' := Corelib.Strings.PrimString.append acc' (ppA y) in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  ls.(bytes).  (* rough; quoting/escaping TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Mutual Fixpoint
  pp_name   (n: name) : Corelib.Strings.PrimString.string :=
    match n with
    | Ninst base args  =>
        pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
    | Nglobal an       => pp_atomic_name an
    | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
    | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
    | Nunsupported s   => s
    end

  with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
    match a with
    | Atype t         => pp_type t
    | Avalue e        => pp_expr e
    | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
    | Atemplate n     => pp_name n
    | Aunsupported s  => s
    end

  with pp_type (t: type) : Corelib.Strings.PrimString.string :=
    match t with
    | Tparam id                 => id
    | Tresult_param id          => id
    | Tresult_global n          => pp_name n
    | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
    | Tresult_binop r t1 t2     =>
        pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
    | Tresult_call n ts         =>
        pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member_call n t1 ts =>
        pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_parenlist t1 ts   =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member t1 n       =>
        pp_type t1 ++ "::" ++ pp_name n
    | Tptr t1                   => pp_type t1 ++ "*"
    | Tref t1                   => pp_type t1 ++ "&"
    | Trv_ref t1                => pp_type t1 ++ "&&"
    | Tnum sz sgn               =>
        "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
    | Tchar_ _                  => "(char)"
    | Tvoid                     => "void"
    | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
    | Tincomplete_array t1      => pp_type t1 ++ "[]"
    | Tvariable_array t1 e1     =>
        pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
    | Tnamed n                  => pp_name n
    | Tenum n                   => "enum " ++ pp_name n
    | Tfunction ft              =>
        let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
        let ps  := (bluerock.lang.cpp.syntax.core.function_type_ params) ft in
        "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
    | Tbool                     => "bool"
    | Tmember_pointer t1 t2     =>
        pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
    | Tfloat_ ft                => pp_float_type ft
    | Tqualified _ t1           => pp_type t1
    | Tnullptr                  => "nullptr_t"
    | Tarch osz name            =>
        "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
        "," ++ name ++ ")"
    | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
    | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
    | Tunsupported s            => s
    end

  with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
    match e with
    | Eparam id                 => id
    | Eunresolved_global n      => pp_name n
    | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
    | Eunresolved_binop r l r2  =>
        pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
    | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member_call n e1 es =>
        pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist None es =>
        "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist (Some t1) es =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
    | Evar ln _                 => ln
    | Eenum_const n id          => pp_name n ++ "::" ++ id
    | Eglobal n _               => pp_name n
    | Eglobal_member n _        => pp_name n
    | Echar c _                 => pp_int (Z.of_N c)
    | Estring s _               => pp_literal_string s
    | Eint n _                  => pp_int n
    | Ebool b                   => if b then "true" else "false"
    | Eunop op e1 _             => pp_unop op ++ pp_expr e1
    | Ebinop op e1 e2 _         =>
        pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
    | Ederef e1 _               => "*" ++ pp_expr e1
    | Eaddrof e1                => "&" ++ pp_expr e1
    | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
    | Eassign_op op e1 e2 _     =>
        pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
    | Epreinc e1 _              => "++" ++ pp_expr e1
    | Epostinc e1 _             => pp_expr e1 ++ "++"
    | Epredec e1 _              => "--" ++ pp_expr e1
    | Epostdec e1 _             => pp_expr e1 ++ "--"
    | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
    | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
    | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
    | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eexplicit_cast cs t1 e1   =>
        pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
    | Ecast c e1                => pp_cast c ++ pp_expr e1
    | Emember arrow obj fn _ _  =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
    | Emember_ignore arrow obj res =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
    | Emember_call arrow mr obj es =>
        pp_expr obj ++ (if arrow then "->" else ".") ++
        pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eoperator_call oop _ es    =>
        pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
    | Esubscript e1 e2 _         =>
        pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
    | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
    | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
    | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
    | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
    | Eoffsetof t1 id _          =>
        "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
    | Econstructor n es _        =>
        pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Elambda id caps            =>
        "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
    | Eimplicit e1               => pp_expr e1
    | Eimplicit_init _           => ""
    | Eif cond thn els _         =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Eif2 _ cond thn els _ _    =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Ethis _                    => "this"
    | Enull                      => "nullptr"
    | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
    | Einitlist es (Some e1) _   =>
        "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
    | Einitlist_union nm def _   =>
        pp_atomic_name nm ++ "{" ++
        (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
    | Enew (nm,_) es nf _ _ _    =>
        "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
    | Edelete is_arr nm e1 _     =>
        "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
    | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
    | Ematerialize_temp e1 _     => pp_expr e1
    | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
    | Estmt s _                  => pp_stmt s
    | Eva_arg e1 _               => pp_expr e1
    | Epseudo_destructor _ _ e1  => pp_expr e1
    | Earrayloop_init _ src _ _ _ _ =>
        pp_expr src
    | Earrayloop_index lvl _     => pp_N lvl
    | Eopaque_ref lvl _          => pp_N lvl
    | Eunsupported s _           => s
    end

  with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
    match s with
    | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
    | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
    | Sif None c t e
                   => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
    | Sif Some d c t e
                   => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt t ++ "else" ++ pp_stmt e
    | Sif_consteval t e
                   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
    | Swhile None c b
                   => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
    | Swhile Some d c b
                   => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt b
    | Sfor i c s b =>
        "for(" ++
        (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
        (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
        (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
        pp_stmt b
    | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
    | Sswitch None e b
                   => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
    | Sswitch Some d e b
                   => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                      pp_stmt b
    | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
    | Sdefault     => "default:"
    | Sbreak       => "break;"
    | Scontinue    => "continue;"
    | Sreturn None => "return;"
    | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
    | Sexpr e0     => pp_expr e0 ++ ";"
    | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
    | Sasm s0 _ _ _ _ 
                   => "asm " ++ s0                      (* TOFIXLATER *)
    | Slabeled id s0
                   => id ++ ": " ++ pp_stmt s0
    | Sgoto id     => "goto " ++ id ++ ";"
    | Sunsupported s0 => s0
    end

  with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
    match d with
    | Dvar ln _ None   => ln
    | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
    | Ddecompose e id bs =>
        "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
        pp_list pp_binding bs ++ "}"
    | Dinit b n _ None => "init " ++ pp_name n
    | Dinit b n _ Some e =>
        "init " ++ pp_name n ++ "=" ++ pp_expr e
    end

  with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
    match b with
    | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
    | Bbind ln _ e => ln ++ "=" ++ pp_expr e
    end

  with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
    match c with
    | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
    | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
    | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
    | Cl2r               => "l2r"                  (* TOFIXLATER *)
    | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
    | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
    | Carray2ptr         => "array2ptr"
    | Cfun2ptr           => "fun2ptr"
    | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
    | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
    | Cptr2bool          => "ptr2bool"
    | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
    | Cint2bool          => "int2bool"
    | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
    | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
    | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
    | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
    | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
    | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
    | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
    | Cuser              => "user_cast"
    | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
    | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
    | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
    | Cunsupported _ _   => "unsupported_cast"
    end.
```

## User 38

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 397-430:
>            let acc' := Corelib.Strings.PrimString.append acc "," in
>                        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The reference Corelib.Strings.PrimString.append was not found in the current environment.


## Assistant 38

Coq is complaining because there is no constant called  
“Corelib.Strings.PrimString.append” in your environment.  The string‐append for  
`PrimString.string` lives under the `%pstring` notation scope, so you either have to  
import a different name or—much more simply—use the `++` notation once you’ve done  
`Local Open Scope pstring_scope.`.

In other words, this:

    Corelib.Strings.PrimString.append acc ","

is not bound, but after `Open Scope pstring_scope` you can write

    acc ++ ","

and Coq will expand that to the right primitive.  

Below is the entire pretty‐printer again, with the only change being that the body of the local `go` fix uses `acc ++ ","` and `acc' ++ ppA y` instead of `Corelib.Strings.PrimString.append …`.  Everything else is identical.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := acc ++ "," in
           let acc'' := acc' ++ ppA y in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  ls.(bytes).  (* rough; quoting/escaping TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Mutual Fixpoint
  pp_name   (n: name) : Corelib.Strings.PrimString.string :=
    match n with
    | Ninst base args  =>
        pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
    | Nglobal an       => pp_atomic_name an
    | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
    | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
    | Nunsupported s   => s
    end

  with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
    match a with
    | Atype t         => pp_type t
    | Avalue e        => pp_expr e
    | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
    | Atemplate n     => pp_name n
    | Aunsupported s  => s
    end

  with pp_type (t: type) : Corelib.Strings.PrimString.string :=
    match t with
    | Tparam id                 => id
    | Tresult_param id          => id
    | Tresult_global n          => pp_name n
    | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
    | Tresult_binop r t1 t2     =>
        pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
    | Tresult_call n ts         =>
        pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member_call n t1 ts =>
        pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_parenlist t1 ts   =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member t1 n       =>
        pp_type t1 ++ "::" ++ pp_name n
    | Tptr t1                   => pp_type t1 ++ "*"
    | Tref t1                   => pp_type t1 ++ "&"
    | Trv_ref t1                => pp_type t1 ++ "&&"
    | Tnum sz sgn               =>
        "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
    | Tchar_ _                  => "(char)"
    | Tvoid                     => "void"
    | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
    | Tincomplete_array t1      => pp_type t1 ++ "[]"
    | Tvariable_array t1 e1     =>
        pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
    | Tnamed n                  => pp_name n
    | Tenum n                   => "enum " ++ pp_name n
    | Tfunction ft              =>
        let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
        let ps  := (bluerock.lang.cpp.syntax.core.function_type_ params) ft in
        "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
    | Tbool                     => "bool"
    | Tmember_pointer t1 t2     =>
        pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
    | Tfloat_ ft                => pp_float_type ft
    | Tqualified _ t1           => pp_type t1
    | Tnullptr                  => "nullptr_t"
    | Tarch osz name            =>
        "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
        "," ++ name ++ ")"
    | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
    | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
    | Tunsupported s            => s
    end

  with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
    match e with
    | Eparam id                 => id
    | Eunresolved_global n      => pp_name n
    | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
    | Eunresolved_binop r l r2  =>
        pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
    | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member_call n e1 es =>
        pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist None es =>
        "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist (Some t1) es =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
    | Evar ln _                 => ln
    | Eenum_const n id          => pp_name n ++ "::" ++ id
    | Eglobal n _               => pp_name n
    | Eglobal_member n _        => pp_name n
    | Echar c _                 => pp_int (Z.of_N c)
    | Estring s _               => pp_literal_string s
    | Eint n _                  => pp_int n
    | Ebool b                   => if b then "true" else "false"
    | Eunop op e1 _             => pp_unop op ++ pp_expr e1
    | Ebinop op e1 e2 _         =>
        pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
    | Ederef e1 _               => "*" ++ pp_expr e1
    | Eaddrof e1                => "&" ++ pp_expr e1
    | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
    | Eassign_op op e1 e2 _     =>
        pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
    | Epreinc e1 _              => "++" ++ pp_expr e1
    | Epostinc e1 _             => pp_expr e1 ++ "++"
    | Epredec e1 _              => "--" ++ pp_expr e1
    | Epostdec e1 _             => pp_expr e1 ++ "--"
    | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
    | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
    | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
    | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eexplicit_cast cs t1 e1   =>
        pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
    | Ecast c e1                => pp_cast c ++ pp_expr e1
    | Emember arrow obj fn _ _  =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
    | Emember_ignore arrow obj res =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
    | Emember_call arrow mr obj es =>
        pp_expr obj ++ (if arrow then "->" else ".") ++
        pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eoperator_call oop _ es    =>
        pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
    | Esubscript e1 e2 _         =>
        pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
    | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
    | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
    | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
    | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
    | Eoffsetof t1 id _          =>
        "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
    | Econstructor n es _        =>
        pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Elambda id caps            =>
        "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
    | Eimplicit e1               => pp_expr e1
    | Eimplicit_init _           => ""
    | Eif cond thn els _         =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Eif2 _ cond thn els _ _    =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Ethis _                    => "this"
    | Enull                      => "nullptr"
    | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
    | Einitlist es (Some e1) _   =>
        "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
    | Einitlist_union nm def _   =>
        pp_atomic_name nm ++ "{" ++
        (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
    | Enew (nm,_) es nf _ _ _    =>
        "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
    | Edelete is_arr nm e1 _     =>
        "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
    | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
    | Ematerialize_temp e1 _     => pp_expr e1
    | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
    | Estmt s _                  => pp_stmt s
    | Eva_arg e1 _               => pp_expr e1
    | Epseudo_destructor _ _ e1  => pp_expr e1
    | Earrayloop_init _ src _ _ _ _ =>
        pp_expr src
    | Earrayloop_index lvl _     => pp_N lvl
    | Eopaque_ref lvl _          => pp_N lvl
    | Eunsupported s _           => s
    end

  with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
    match s with
    | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
    | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
    | Sif None c t e
                   => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
    | Sif Some d c t e
                   => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt t ++ "else" ++ pp_stmt e
    | Sif_consteval t e
                   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
    | Swhile None c b
                   => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
    | Swhile Some d c b
                   => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt b
    | Sfor i c s b =>
        "for(" ++
        (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
        (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
        (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
        pp_stmt b
    | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
    | Sswitch None e b
                   => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
    | Sswitch Some d e b
                   => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                      pp_stmt b
    | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
    | Sdefault     => "default:"
    | Sbreak       => "break;"
    | Scontinue    => "continue;"
    | Sreturn None => "return;"
    | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
    | Sexpr e0     => pp_expr e0 ++ ";"
    | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
    | Sasm s0 _ _ _ _ 
                   => "asm " ++ s0                      (* TOFIXLATER *)
    | Slabeled id s0
                   => id ++ ": " ++ pp_stmt s0
    | Sgoto id     => "goto " ++ id ++ ";"
    | Sunsupported s0 => s0
    end

  with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
    match d with
    | Dvar ln _ None   => ln
    | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
    | Ddecompose e id bs =>
        "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
        pp_list pp_binding bs ++ "}"
    | Dinit b n _ None => "init " ++ pp_name n
    | Dinit b n _ Some e =>
        "init " ++ pp_name n ++ "=" ++ pp_expr e
    end

  with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
    match b with
    | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
    | Bbind ln _ e => ln ++ "=" ++ pp_expr e
    end

  with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
    match c with
    | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
    | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
    | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
    | Cl2r               => "l2r"                  (* TOFIXLATER *)
    | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
    | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
    | Carray2ptr         => "array2ptr"
    | Cfun2ptr           => "fun2ptr"
    | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
    | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
    | Cptr2bool          => "ptr2bool"
    | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
    | Cint2bool          => "int2bool"
    | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
    | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
    | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
    | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
    | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
    | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
    | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
    | Cuser              => "user_cast"
    | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
    | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
    | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
    | Cunsupported _ _   => "unsupported_cast"
    end.
```

## User 39

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 398-401:
>            let acc'  := acc ++ "," in
>                         ^^^
Error:
In environment
A : Type
ppA : A → Corelib.Strings.PrimString.string
l : Corelib.Init.Datatypes.list A
x : A
xs : Corelib.Init.Datatypes.list A
go : Corelib.Init.Datatypes.list A → Corelib.Strings.PrimString.string → Corelib.Strings.PrimString.string
rest : Corelib.Init.Datatypes.list A
acc : Corelib.Strings.PrimString.string
y : A
ys : Corelib.Init.Datatypes.list A
The term "acc" has type "Corelib.Strings.PrimString.string" while it is expected to have type "Corelib.Init.Datatypes.list ?A".


## Assistant 39

Coq is still picking the “++” from the `list_scope` (list‐append : list A → list A → list A), so when you write

    let acc' := acc ++ "," in

it thinks you are doing list‐append on  
`acc : PrimString.string` and `"," : PrimString.string`, hence the type‐mismatch.  

To fix this you must force the `%pstring` scope whenever you mean string‐concatenation.  The simplest patch is to write

    (acc ++ ",")%pstring

(and likewise `(acc' ++ ppA y)%pstring`) inside your local `go`.  With that change Coq will resolve “++” to the PrimString append, not the list append.

Below is the entire pretty‐printer with that one change in `pp_list` (all other code is unchanged).  Now it should load without the above error.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  ls.(bytes).  (* rough; quoting/escaping TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Mutual Fixpoint
  pp_name   (n: name) : Corelib.Strings.PrimString.string :=
    match n with
    | Ninst base args  =>
        pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
    | Nglobal an       => pp_atomic_name an
    | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
    | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
    | Nunsupported s   => s
    end

  with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
    match a with
    | Atype t         => pp_type t
    | Avalue e        => pp_expr e
    | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
    | Atemplate n     => pp_name n
    | Aunsupported s  => s
    end

  with pp_type (t: type) : Corelib.Strings.PrimString.string :=
    match t with
    | Tparam id                 => id
    | Tresult_param id          => id
    | Tresult_global n          => pp_name n
    | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
    | Tresult_binop r t1 t2     =>
        pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
    | Tresult_call n ts         =>
        pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member_call n t1 ts =>
        pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_parenlist t1 ts   =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member t1 n       =>
        pp_type t1 ++ "::" ++ pp_name n
    | Tptr t1                   => pp_type t1 ++ "*"
    | Tref t1                   => pp_type t1 ++ "&"
    | Trv_ref t1                => pp_type t1 ++ "&&"
    | Tnum sz sgn               =>
        "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
    | Tchar_ _                  => "(char)"
    | Tvoid                     => "void"
    | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
    | Tincomplete_array t1      => pp_type t1 ++ "[]"
    | Tvariable_array t1 e1     =>
        pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
    | Tnamed n                  => pp_name n
    | Tenum n                   => "enum " ++ pp_name n
    | Tfunction ft              =>
        let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
        let ps  := (bluerock.lang.cpp.syntax.core.function_type_ params) ft in
        "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
    | Tbool                     => "bool"
    | Tmember_pointer t1 t2     =>
        pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
    | Tfloat_ ft                => pp_float_type ft
    | Tqualified _ t1           => pp_type t1
    | Tnullptr                  => "nullptr_t"
    | Tarch osz name            =>
        "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
        "," ++ name ++ ")"
    | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
    | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
    | Tunsupported s            => s
    end

  with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
    match e with
    | Eparam id                 => id
    | Eunresolved_global n      => pp_name n
    | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
    | Eunresolved_binop r l r2  =>
        pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
    | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member_call n e1 es =>
        pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist None es =>
        "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist (Some t1) es =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
    | Evar ln _                 => ln
    | Eenum_const n id          => pp_name n ++ "::" ++ id
    | Eglobal n _               => pp_name n
    | Eglobal_member n _        => pp_name n
    | Echar c _                 => pp_int (Z.of_N c)
    | Estring s _               => pp_literal_string s
    | Eint n _                  => pp_int n
    | Ebool b                   => if b then "true" else "false"
    | Eunop op e1 _             => pp_unop op ++ pp_expr e1
    | Ebinop op e1 e2 _         =>
        pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
    | Ederef e1 _               => "*" ++ pp_expr e1
    | Eaddrof e1                => "&" ++ pp_expr e1
    | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
    | Eassign_op op e1 e2 _     =>
        pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
    | Epreinc e1 _              => "++" ++ pp_expr e1
    | Epostinc e1 _             => pp_expr e1 ++ "++"
    | Epredec e1 _              => "--" ++ pp_expr e1
    | Epostdec e1 _             => pp_expr e1 ++ "--"
    | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
    | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
    | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
    | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eexplicit_cast cs t1 e1   =>
        pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
    | Ecast c e1                => pp_cast c ++ pp_expr e1
    | Emember arrow obj fn _ _  =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
    | Emember_ignore arrow obj res =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
    | Emember_call arrow mr obj es =>
        pp_expr obj ++ (if arrow then "->" else ".") ++
        pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eoperator_call oop _ es    =>
        pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
    | Esubscript e1 e2 _         =>
        pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
    | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
    | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
    | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
    | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
    | Eoffsetof t1 id _          =>
        "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
    | Econstructor n es _        =>
        pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Elambda id caps            =>
        "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
    | Eimplicit e1               => pp_expr e1
    | Eimplicit_init _           => ""
    | Eif cond thn els _         =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Eif2 _ cond thn els _ _    =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Ethis _                    => "this"
    | Enull                      => "nullptr"
    | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
    | Einitlist es (Some e1) _   =>
        "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
    | Einitlist_union nm def _   =>
        pp_atomic_name nm ++ "{" ++
        (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
    | Enew (nm,_) es nf _ _ _    =>
        "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
    | Edelete is_arr nm e1 _     =>
        "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
    | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
    | Ematerialize_temp e1 _     => pp_expr e1
    | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
    | Estmt s _                  => pp_stmt s
    | Eva_arg e1 _               => pp_expr e1
    | Epseudo_destructor _ _ e1  => pp_expr e1
    | Earrayloop_init _ src _ _ _ _ =>
        pp_expr src
    | Earrayloop_index lvl _     => pp_N lvl
    | Eopaque_ref lvl _          => pp_N lvl
    | Eunsupported s _           => s
    end

  with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
    match s with
    | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
    | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
    | Sif None c t e
                   => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
    | Sif Some d c t e
                   => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt t ++ "else" ++ pp_stmt e
    | Sif_consteval t e
                   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
    | Swhile None c b
                   => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
    | Swhile Some d c b
                   => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt b
    | Sfor i c s b =>
        "for(" ++
        (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
        (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
        (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
        pp_stmt b
    | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
    | Sswitch None e b
                   => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
    | Sswitch Some d e b
                   => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                      pp_stmt b
    | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
    | Sdefault     => "default:"
    | Sbreak       => "break;"
    | Scontinue    => "continue;"
    | Sreturn None => "return;"
    | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
    | Sexpr e0     => pp_expr e0 ++ ";"
    | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
    | Sasm s0 _ _ _ _ 
                   => "asm " ++ s0                      (* TOFIXLATER *)
    | Slabeled id s0
                   => id ++ ": " ++ pp_stmt s0
    | Sgoto id     => "goto " ++ id ++ ";"
    | Sunsupported s0 => s0
    end

  with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
    match d with
    | Dvar ln _ None   => ln
    | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
    | Ddecompose e id bs =>
        "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
        pp_list pp_binding bs ++ "}"
    | Dinit b n _ None => "init " ++ pp_name n
    | Dinit b n _ Some e =>
        "init " ++ pp_name n ++ "=" ++ pp_expr e
    end

  with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
    match b with
    | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
    | Bbind ln _ e => ln ++ "=" ++ pp_expr e
    end

  with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
    match c with
    | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
    | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
    | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
    | Cl2r               => "l2r"                  (* TOFIXLATER *)
    | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
    | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
    | Carray2ptr         => "array2ptr"
    | Cfun2ptr           => "fun2ptr"
    | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
    | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
    | Cptr2bool          => "ptr2bool"
    | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
    | Cint2bool          => "int2bool"
    | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
    | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
    | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
    | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
    | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
    | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
    | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
    | Cuser              => "user_cast"
    | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
    | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
    | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
    | Cunsupported _ _   => "unsupported_cast"
    end.
```

## User 40

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 141-146:
>   ls.(bytes).
>       ^^^^^
Error: The reference bytes was not found in the current environment.


## Assistant 40

Coq is complaining because the record‐projection is not called just `bytes` in your environment, but rather the fully‐qualified name

   bluerock.lang.cpp.syntax.literal_string.literal_string.bytes

Coq does not automatically bind the shorter name `bytes`, so `ls.(bytes)` fails.  We must either `Import` that module or simply call the projection fully qualified.  

Here is the entire pretty‐printer again, with that one fix in `pp_literal_string`.  Everything else is unchanged.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* fixed projection *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Mutual Fixpoint
  pp_name   (n: name) : Corelib.Strings.PrimString.string :=
    match n with
    | Ninst base args  =>
        pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
    | Nglobal an       => pp_atomic_name an
    | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
    | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
    | Nunsupported s   => s
    end

  with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
    match a with
    | Atype t         => pp_type t
    | Avalue e        => pp_expr e
    | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
    | Atemplate n     => pp_name n
    | Aunsupported s  => s
    end

  with pp_type (t: type) : Corelib.Strings.PrimString.string :=
    match t with
    | Tparam id                 => id
    | Tresult_param id          => id
    | Tresult_global n          => pp_name n
    | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
    | Tresult_binop r t1 t2     =>
        pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
    | Tresult_call n ts         =>
        pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member_call n t1 ts =>
        pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_parenlist t1 ts   =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
    | Tresult_member t1 n       =>
        pp_type t1 ++ "::" ++ pp_name n
    | Tptr t1                   => pp_type t1 ++ "*"
    | Tref t1                   => pp_type t1 ++ "&"
    | Trv_ref t1                => pp_type t1 ++ "&&"
    | Tnum sz sgn               =>
        "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
    | Tchar_ _                  => "(char)"
    | Tvoid                     => "void"
    | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
    | Tincomplete_array t1      => pp_type t1 ++ "[]"
    | Tvariable_array t1 e1     =>
        pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
    | Tnamed n                  => pp_name n
    | Tenum n                   => "enum " ++ pp_name n
    | Tfunction ft              =>
        let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
        let ps  := (bluerock.lang.cpp.syntax.core.function_type_ params) ft in
        "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
    | Tbool                     => "bool"
    | Tmember_pointer t1 t2     =>
        pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
    | Tfloat_ ft                => pp_float_type ft
    | Tqualified _ t1           => pp_type t1
    | Tnullptr                  => "nullptr_t"
    | Tarch osz name            =>
        "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
        "," ++ name ++ ")"
    | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
    | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
    | Tunsupported s            => s
    end

  with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
    match e with
    | Eparam id                 => id
    | Eunresolved_global n      => pp_name n
    | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
    | Eunresolved_binop r l r2  =>
        pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
    | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member_call n e1 es =>
        pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist None es =>
        "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_parenlist (Some t1) es =>
        "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
    | Evar ln _                 => ln
    | Eenum_const n id          => pp_name n ++ "::" ++ id
    | Eglobal n _               => pp_name n
    | Eglobal_member n _        => pp_name n
    | Echar c _                 => pp_int (Z.of_N c)
    | Estring s _               => pp_literal_string s
    | Eint n _                  => pp_int n
    | Ebool b                   => if b then "true" else "false"
    | Eunop op e1 _             => pp_unop op ++ pp_expr e1
    | Ebinop op e1 e2 _         =>
        pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
    | Ederef e1 _               => "*" ++ pp_expr e1
    | Eaddrof e1                => "&" ++ pp_expr e1
    | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
    | Eassign_op op e1 e2 _     =>
        pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
    | Epreinc e1 _              => "++" ++ pp_expr e1
    | Epostinc e1 _             => pp_expr e1 ++ "++"
    | Epredec e1 _              => "--" ++ pp_expr e1
    | Epostdec e1 _             => pp_expr e1 ++ "--"
    | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
    | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
    | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
    | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eexplicit_cast cs t1 e1   =>
        pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
    | Ecast c e1                => pp_cast c ++ pp_expr e1
    | Emember arrow obj fn _ _  =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
    | Emember_ignore arrow obj res =>
        pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
    | Emember_call arrow mr obj es =>
        pp_expr obj ++ (if arrow then "->" else ".") ++
        pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
    | Eoperator_call oop _ es    =>
        pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
    | Esubscript e1 e2 _         =>
        pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
    | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
    | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
    | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
    | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
    | Eoffsetof t1 id _          =>
        "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
    | Econstructor n es _        =>
        pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
    | Elambda id caps            =>
        "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
    | Eimplicit e1               => pp_expr e1
    | Eimplicit_init _           => ""
    | Eif cond thn els _         =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Eif2 _ cond thn els _ _    =>
        pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
    | Ethis _                    => "this"
    | Enull                      => "nullptr"
    | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
    | Einitlist es (Some e1) _   =>
        "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
    | Einitlist_union nm def _   =>
        pp_atomic_name nm ++ "{" ++
        (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
    | Enew (nm,_) es nf _ _ _    =>
        "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
    | Edelete is_arr nm e1 _     =>
        "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
    | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
    | Ematerialize_temp e1 _     => pp_expr e1
    | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
    | Estmt s _                  => pp_stmt s
    | Eva_arg e1 _               => pp_expr e1
    | Epseudo_destructor _ _ e1  => pp_expr e1
    | Earrayloop_init _ src _ _ _ _ =>
        pp_expr src
    | Earrayloop_index lvl _     => pp_N lvl
    | Eopaque_ref lvl _          => pp_N lvl
    | Eunsupported s _           => s
    end

  with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
    match s with
    | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
    | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
    | Sif None c t e
                   => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
    | Sif Some d c t e
                   => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt t ++ "else" ++ pp_stmt e
    | Sif_consteval t e
                   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
    | Swhile None c b
                   => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
    | Swhile Some d c b
                   => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                      pp_stmt b
    | Sfor i c s b =>
        "for(" ++
        (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
        (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
        (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
        pp_stmt b
    | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
    | Sswitch None e b
                   => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
    | Sswitch Some d e b
                   => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                      pp_stmt b
    | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
    | Sdefault     => "default:"
    | Sbreak       => "break;"
    | Scontinue    => "continue;"
    | Sreturn None => "return;"
    | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
    | Sexpr e0     => pp_expr e0 ++ ";"
    | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
    | Sasm s0 _ _ _ _ 
                   => "asm " ++ s0                      (* TOFIXLATER *)
    | Slabeled id s0
                   => id ++ ": " ++ pp_stmt s0
    | Sgoto id     => "goto " ++ id ++ ";"
    | Sunsupported s0 => s0
    end

  with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
    match d with
    | Dvar ln _ None   => ln
    | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
    | Ddecompose e id bs =>
        "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
        pp_list pp_binding bs ++ "}"
    | Dinit b n _ None => "init " ++ pp_name n
    | Dinit b n _ Some e =>
        "init " ++ pp_name n ++ "=" ++ pp_expr e
    end

  with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
    match b with
    | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
    | Bbind ln _ e => ln ++ "=" ++ pp_expr e
    end

  with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
    match c with
    | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
    | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
    | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
    | Cl2r               => "l2r"                  (* TOFIXLATER *)
    | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
    | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
    | Carray2ptr         => "array2ptr"
    | Cfun2ptr           => "fun2ptr"
    | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
    | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
    | Cptr2bool          => "ptr2bool"
    | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
    | Cint2bool          => "int2bool"
    | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
    | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
    | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
    | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
    | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
    | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
    | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
    | Cuser              => "user_cast"
    | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
    | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
    | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
    | Cunsupported _ _   => "unsupported_cast"
    end.
```

## User 41

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 0-6:
> Mutual Fixpoint
> ^^^^^^
Error: Syntax error: illegal begin of toplevel:vernac_toplevel.


## Assistant 41

Coq is rejecting the keyword `Mutual` because its grammar for top‐level mutual recursion does not allow “Mutual Fixpoint …” – instead you simply write a single `Fixpoint` and chain the mutually‐recursive definitions with `with`.  In other words, drop “Mutual” and start with

```coq
Fixpoint pp_name … := … with pp_temp_arg … := … with … end.
```

Here is the complete pretty‐printer with that one change (everything else exactly as before):

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* fixed projection *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
      let ps  := (bluerock.lang.cpp.syntax.core.function_type_ params) ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz name            =>
      "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
      "," ++ name ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 42

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 2108-2119:
>       let ret := (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft in
>                                                                ^^^^^^^^^^^
Error: The reference return_type was not found in the current environment.


## Assistant 42

Coq is complaining because I wrote

    (bluerock.lang.cpp.syntax.core.function_type_ return_type) ft

as if `return_type` were a toplevel identifier.  In fact `function_type_` is a record, and its projection is not simply called `return_type` but has the fully‐qualified name

    bluerock.lang.cpp.syntax.core.function_type_.return_type

(and likewise for `params`).  To fix this, I must call the record‐projection with its full path, for example:

    bluerock.lang.cpp.syntax.core.function_type_.return_type ft

Below is the entire pretty‐printer with that one change in the `Tfunction` case; everything else is unchanged.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* fixed projection *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.function_type_.return_type ft in
      let ps  := bluerock.lang.cpp.syntax.core.function_type_.params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz name            =>
      "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
      "," ++ name ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 43

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 2062-2118:
>       let ret := bluerock.lang.cpp.syntax.core.function_type_.return_type ft in
>                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The reference bluerock.lang.cpp.syntax.core.function_type_.return_type was not found in the current environment.


## Assistant 43

Coq is complaining because there is no projection called  
“bluerock.lang.cpp.syntax.core.function_type_.return_type”—I simply guessed the field name.  The actual record has different field‐projection names, so we must inspect its definition to find the correct names.  Once we know the real projection names (e.g. maybe `function_type_.ret` or `function_type_.return_t`), we can replace that bad identifier with the right projection.

Let’s print the `function_type_` record so we can see its constructors and projection names:

```coqquery
Print bluerock.lang.cpp.syntax.core.function_type_.
```

## User 44

>>> Print bluerock.lang.cpp.syntax.core.function_type_.
Record function_type_ (decltype : Set) : Set := FunctionType
  { ft_cc : bluerock.lang.cpp.syntax.preliminary.calling_conv;
    ft_arity : bluerock.lang.cpp.syntax.preliminary.function_arity;
    ft_return : decltype;
    ft_params : Corelib.Init.Datatypes.list decltype }.

function_type_ has primitive projections with eta conversion.
Arguments bluerock.lang.cpp.syntax.core.function_type_ decltype%_type_scope
Arguments bluerock.lang.cpp.syntax.core.FunctionType {decltype}%_type_scope {ft_cc ft_arity} ft_return ft_params%_list_scope
Arguments bluerock.lang.cpp.syntax.core.ft_cc {decltype}%_type_scope f
Arguments bluerock.lang.cpp.syntax.core.ft_arity {decltype}%_type_scope f
Arguments bluerock.lang.cpp.syntax.core.ft_return {decltype}%_type_scope f
Arguments bluerock.lang.cpp.syntax.core.ft_params {decltype}%_type_scope f

## Assistant 44

Coq complains because I tried to use projections named `function_type_.return_type` and `function_type_.params`, but the actual record `function_type_` declares its projections as `ft_return` and `ft_params`.  Thus the identifiers I used do not exist.  To fix this, I must replace

    bluerock.lang.cpp.syntax.core.function_type_.return_type ft
    bluerock.lang.cpp.syntax.core.function_type_.params ft

with

    bluerock.lang.cpp.syntax.core.ft_return ft
    bluerock.lang.cpp.syntax.core.ft_params ft

Here is the entire corrected pretty-printer:

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low-level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* fixed projection *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz name            =>
      "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
      "," ++ name ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 45

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 1576-1578:
>       "(num:" ++ pp_int sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
>                         ^^
Error:
In environment
pp_name : name → Corelib.Strings.PrimString.string
pp_temp_arg : temp_arg → Corelib.Strings.PrimString.string
pp_type : type → Corelib.Strings.PrimString.string
pp_expr : Expr → Corelib.Strings.PrimString.string
pp_stmt : Stmt → Corelib.Strings.PrimString.string
pp_vardecl : VarDecl → Corelib.Strings.PrimString.string
pp_binding : BindingDecl → Corelib.Strings.PrimString.string
pp_cast : Cast → Corelib.Strings.PrimString.string
t : type
sz : int_rank
sgn : bluerock.prelude.arith.types.signed
The term "sz" has type "int_rank" while it is expected to have type "Corelib.Numbers.BinNums.Z".


## Assistant 45

Coq is telling us that in the clause

    Tnum sz sgn ⇒ "(num:" ++ pp_int sz ++ "," ++ … ++ ")"

the identifier `sz` has type `int_rank` but our stub

    pp_int : Z → string

expects a `Z`.  Hence the type mismatch.  

We must either convert the rank to a `Z` (if you have a function `int_rank_to_Z`), or more faithfully pretty‐print the rank directly.  Here I choose to introduce a new stub

    Definition pp_int_rank (r: int_rank) : string. Admitted.

and then call `pp_int_rank sz` instead of `pp_int sz`.  

Below is the full pretty‐printer with that one change (plus the new stub).  Everything else is unchanged.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: bluerock.prelude.arith.types.int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int_rank sz ++ "," ++
      (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz name            =>
      "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++
      "," ++ name ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 46

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 27-64:
> Definition pp_int_rank (r: bluerock.prelude.arith.types.int_rank) : Corelib.Strings.PrimString.string.
>                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The reference bluerock.prelude.arith.types.int_rank was not found in the current environment.


## Assistant 46

Coq is complaining because there is no identifier called  
“bluerock.prelude.arith.types.int_rank” in your environment.  From the earlier “Print” of your AST we see the constructor

    Tnum : int_rank → bluerock.prelude.arith.types.signed → type

so the correct name of the rank‐type is simply `int_rank`, not a longer path.  To fix this, change the stub

    Definition pp_int_rank (r: bluerock.prelude.arith.types.int_rank) …

to

    Definition pp_int_rank (r: int_rank) …

Below is the entire pretty‐printer again with that one change.  Now Coq will find `int_rank` and the definition will load.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz name            =>
      "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++ "," ++ name ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 47

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 2575-2576:
>       "(arch:" ++ (match osz with Some k => pp_N k | None => "" end) ++ "," ++ name ++ ")"
>                                                  ^
Error:
In environment
pp_name : core.name → Corelib.Strings.PrimString.string
pp_temp_arg : temp_arg → Corelib.Strings.PrimString.string
pp_type : type → Corelib.Strings.PrimString.string
pp_expr : Expr → Corelib.Strings.PrimString.string
pp_stmt : Stmt → Corelib.Strings.PrimString.string
pp_vardecl : VarDecl → Corelib.Strings.PrimString.string
pp_binding : BindingDecl → Corelib.Strings.PrimString.string
pp_cast : Cast → Corelib.Strings.PrimString.string
t : type
osz : Corelib.Init.Datatypes.option bitsize
name : Corelib.Strings.PrimString.string
k : bitsize
The term "k" has type "bitsize" while it is expected to have type "Corelib.Numbers.BinNums.N".


## Assistant 47

Coq is complaining because in the `Tarch` branch I wrote

    match osz with Some k => pp_N k | None => "" end

but `osz : option bitsize`, so `k : bitsize`.  The function `pp_N` expects an `N`, not a `bitsize`.  Hence the mismatch.

To fix this I introduce a new stub

    Definition pp_bitsize (b: bitsize) : string. Admitted.

and then call `pp_bitsize k` instead of `pp_N k` in the `Tarch` case.  Below is the entire pretty‐printer with that change (and the new stub).  Nothing else has changed.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz nm              =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++
      "," ++ nm ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 48

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 6951-6964:
>   | Eandclean a b              => pp_expr a ++ "," ++ pp_expr b
>     ^^^^^^^^^^^^^
Error: The constructor bluerock.lang.cpp.syntax.core.Eandclean (in type bluerock.lang.cpp.syntax.core.Expr') is expected to be applied to
1 argument while it is actually applied to 2 arguments.


## Assistant 48

Coq’s error tells us that `Eandclean` has type

   Eandclean : Expr → Expr

i.e. it takes *one* `Expr` argument, not two.  I mistakenly wrote

   | Eandclean a b => …

as if `Eandclean` were a binary constructor.  The fix is to match it on a single `e`, and then pretty‐print `e`.  

Below is the entire pretty‐printer with that one correction (and nothing else changed).  Now `Eandclean` is matched as

   | Eandclean e => pp_expr e

instead of two arguments.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz nm              =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++
      "," ++ nm ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                => pp_expr e
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 49

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 6007-6009:
>       "[" ++ id ++ "](" ++ pp_list pp_expr caps ++ ")"
>              ^^
Error:
In environment
pp_name : name → Corelib.Strings.PrimString.string
pp_temp_arg : temp_arg → Corelib.Strings.PrimString.string
pp_type : type → Corelib.Strings.PrimString.string
pp_expr : Expr → Corelib.Strings.PrimString.string
pp_stmt : Stmt → Corelib.Strings.PrimString.string
pp_vardecl : VarDecl → Corelib.Strings.PrimString.string
pp_binding : BindingDecl → Corelib.Strings.PrimString.string
pp_cast : Cast → Corelib.Strings.PrimString.string
e : Expr
id : name
caps : Corelib.Init.Datatypes.list Expr
The term "id" has type "name" while it is expected to have type "Corelib.Strings.PrimString.string".


## Assistant 49

Coq is complaining because in the branch

  | Elambda id caps => "[" ++ id ++ … 

I treated `id` as if it were a `string`, but actually `Elambda`’s first argument has type `name`.  So `id` must be pretty‐printed via `pp_name id`, not used directly.  

Here is the complete pretty‐printer with exactly that one fix (and nothing else changed).  Now the `Elambda` case reads:

  | Elambda id caps => "[" ++ pp_name id ++ "](" ++ …  

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.         (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name   (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t         => pp_type t
  | Avalue e        => pp_expr e
  | Apack args      => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n     => pp_name n
  | Aunsupported s  => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz nm              =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++
      "," ++ nm ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                => pp_expr e
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss      => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds     => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e
                 => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif Some d c t e
                 => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                 => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b
                 => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile Some d c b
                 => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                    pp_stmt b
  | Sfor i c s b =>
      "for(" ++
      (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++
      (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++
      (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c      => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b
                 => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch Some d e b
                 => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++
                    pp_stmt b
  | Scase _ br   => "case ...: " ++ pp_stmt br        (* TOFIXLATER *)
  | Sdefault     => "default:"
  | Sbreak       => "break;"
  | Scontinue    => "continue;"
  | Sreturn None => "return;"
  | Sreturn Some e0 => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0     => pp_expr e0 ++ ";"
  | Sattr as0 s0 => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ 
                 => "asm " ++ s0                      (* TOFIXLATER *)
  | Slabeled id s0
                 => id ++ ": " ++ pp_stmt s0
  | Sgoto id     => "goto " ++ id ++ ";"
  | Sunsupported s0 => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None   => ln
  | Dvar ln _ Some e => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++
      pp_list pp_binding bs ++ "}"
  | Dinit b n _ None => "init " ++ pp_name n
  | Dinit b n _ Some e =>
      "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 50

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 7731-7747:
>   | Sif Some d c t e
>     ^^^^^^^^^^^^^^^^
Error: The constructor bluerock.lang.cpp.syntax.core.Sif (in type bluerock.lang.cpp.syntax.core.Stmt') is expected to be applied to
4 arguments while it is actually applied to 5 arguments.


## Assistant 50

Coq’s parser saw

    | Sif Some d c t e => …

as five arguments to the `Sif` constructor (`Some`, `d`, `c`, `t`, `e`), but `Sif` only takes four.  To make the `Some d` count as one argument you must parenthesize it:

    | Sif (Some d) c t e => …

Here is the entire pretty‐printer again with exactly that change.  Everything else is identical.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: Corelib.Init.Datatypes.list A)
               (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low-level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t          => pp_type t
  | Avalue e         => pp_expr e
  | Apack args       => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n      => pp_name n
  | Aunsupported s   => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++
      "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                => pp_expr e
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss        => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds       => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e =>
      "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e =>
      "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
      pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e =>
      "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b =>
      "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b =>
      "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b   =>
      "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++
      ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++
      ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c        => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b =>
      "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b =>
      "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase _ br     => "case ...: " ++ pp_stmt br    (* TOFIXLATER *)
  | Sdefault       => "default:"
  | Sbreak         => "break;"
  | Scontinue      => "continue;"
  | Sreturn None   => "return;"
  | Sreturn Some e => "return " ++ pp_expr e ++ ";"
  | Sexpr e        => pp_expr e ++ ";"
  | Sattr as0 s0   => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _ => "asm " ++ s0                  (* TOFIXLATER *)
  | Slabeled id s0 => id ++ ": " ++ pp_stmt s0
  | Sgoto id       => "goto " ++ id ++ ";"
  | Sunsupported s => s
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None    => ln
  | Dvar ln _ Some e  => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None  => "init " ++ pp_name n
  | Dinit b n _ Some e => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 51

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 8584-8594:
>   | Scase _ br     => "case ...: " ++ pp_stmt br    (* TOFIXLATER *)
>     ^^^^^^^^^^
Error: The constructor bluerock.lang.cpp.syntax.core.Scase (in type bluerock.lang.cpp.syntax.core.Stmt') is expected to be applied to
1 argument while it is actually applied to 2 arguments.


## Assistant 51

Coq is telling us that we wrote

    | Scase _ br => …

as if `Scase` had two arguments, but in fact

    Scase : SwitchBranch → Stmt

takes exactly one argument.  We must match it as

    | Scase br => …

instead of `| Scase _ br => …`.

Below is the entire pretty‐printer again with that single fix in the `pp_stmt` definition.  Everything else is unchanged.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go rest acc :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.         (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                 => id
  | Tresult_param id          => id
  | Tresult_global n          => pp_name n
  | Tresult_unop r t1         => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2     =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts         =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts   =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n       =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                   => pp_type t1 ++ "*"
  | Tref t1                   => pp_type t1 ++ "&"
  | Trv_ref t1                => pp_type t1 ++ "&&"
  | Tnum sz sgn               =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                  => "(char)"
  | Tvoid                     => "void"
  | Tarray t1 n               => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1      => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1     =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                  => pp_name n
  | Tenum n                   => "enum " ++ pp_name n
  | Tfunction ft              =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                     => "bool"
  | Tmember_pointer t1 t2     =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft                => pp_float_type ft
  | Tqualified _ t1           => pp_type t1
  | Tnullptr                  => "nullptr_t"
  | Tarch osz nm              =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++
      "," ++ nm ++ ")"
  | Tdecltype e1              => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1              => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s            => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                => pp_expr e
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss          => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds         => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e   => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e
                    => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++
                       pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e
                    => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b  => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b
                    => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b     =>
      "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++
      ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++
      ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++
      pp_stmt b
  | Sdo b c          => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b
                    => "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br         => "case ...: " ++ (* br needs its own printer TOFIXLATER *) ""
  | Sdefault         => "default:"
  | Sbreak           => "break;"
  | Scontinue        => "continue;"
  | Sreturn None     => "return;"
  | Sreturn Some e0  => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0         => pp_expr e0 ++ ";"
  | Sattr as0 s0     => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _  => "asm " ++ s0                    (* TOFIXLATER *)
  | Slabeled id s0   => id ++ ": " ++ pp_stmt s0
  | Sgoto id         => "goto " ++ id ++ ";"
  | Sunsupported s0  => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ Some e     => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ Some e   => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r               => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 52

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 8892-8907:
>   | Sreturn Some e0  => "return " ++ pp_expr e0 ++ ";"
>     ^^^^^^^^^^^^^^^
Error: The constructor bluerock.lang.cpp.syntax.core.Sreturn (in type bluerock.lang.cpp.syntax.core.Stmt') is expected to be applied to
1 argument while it is actually applied to 2 arguments.


## Assistant 52

Coq complains because I wrote

    | Sreturn Some e0 => …

as if `Sreturn` had two arguments, but its single argument is the entire `option Expr`.  To match the `Some`‐case correctly, I must parenthesize:

    | Sreturn (Some e0) => …

(or else match on the whole `Sreturn eopt` and then destruct `eopt`).  Without the parentheses, Coq thinks I’m giving two separate arguments to `Sreturn`, which has arity 1.

Below is the entire pretty‐printer with that one fix (and nothing else changed).  Now the `Sreturn` branches read:

    | Sreturn None       => "return;"
    | Sreturn (Some e0)  => "return " ++ pp_expr e0 ++ ";"

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go rest acc :=
        match rest with
        | [] => acc
        | y :: ys =>
            let acc'  := (acc ++ ",")%pstring in
            let acc'' := (acc' ++ ppA y)%pstring in
            go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low-level conversions and operator names *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.                              (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
    bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.         (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++
      "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  =>
      pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es =>
      "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n   => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                 => ln
  | Eenum_const n id          => pp_name n ++ "::" ++ id
  | Eglobal n _               => pp_name n
  | Eglobal_member n _        => pp_name n
  | Echar c _                 => pp_int (Z.of_N c)
  | Estring s _               => pp_literal_string s
  | Eint n _                  => pp_int n
  | Ebool b                   => if b then "true" else "false"
  | Eunop op e1 _             => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _         =>
      pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _               => "*" ++ pp_expr e1
  | Eaddrof e1                => "&" ++ pp_expr e1
  | Eassign e1 e2 _           => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _     =>
      pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _              => "++" ++ pp_expr e1
  | Epostinc e1 _             => pp_expr e1 ++ "++"
  | Epredec e1 _              => "--" ++ pp_expr e1
  | Epostdec e1 _             => pp_expr e1 ++ "--"
  | Eseqand e1 e2             => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2              => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2              => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1   =>
      pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _  =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++
      pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es    =>
      pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _         =>
      pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _         => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _         => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _        => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _        => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _          =>
      "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _        =>
      pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps            =>
      "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1               => pp_expr e1
  | Eimplicit_init _           => ""
  | Eif cond thn els _         =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _    =>
      pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                    => "this"
  | Enull                      => "nullptr"
  | Einitlist es None _        => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _   =>
      "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _   =>
      pp_atomic_name nm ++ "{" ++
      (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _    =>
      "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _     =>
      "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                => pp_expr e
  | Ematerialize_temp e1 _     => pp_expr e1
  | Eatomic ao es _            => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                  => pp_stmt s
  | Eva_arg e1 _               => pp_expr e1
  | Epseudo_destructor _ _ e1  => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ =>
      pp_expr src
  | Earrayloop_index lvl _     => pp_N lvl
  | Eopaque_ref lvl _          => pp_N lvl
  | Eunsupported s _           => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss            => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds           => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e     => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e  => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b    => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b=> "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b       =>
      "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++
      ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++
      ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c            => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b   => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=>
      "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br           => "case ...: " ++ (* TOFIXLATER: real branch *) ""
  | Sdefault           => "default:"
  | Sbreak             => "break;"
  | Scontinue          => "continue;"
  | Sreturn None       => "return;"
  | Sreturn (Some e0)  => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0           => pp_expr e0 ++ ";"
  | Sattr as0 s0       => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _    => "asm " ++ s0    (* TOFIXLATER *)
  | Slabeled id s0     => id ++ ": " ++ pp_stmt s0
  | Sgoto id           => "goto " ++ id ++ ";"
  | Sunsupported s0    => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ Some e     => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   =>
      "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ Some e   => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t       => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t         => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t   => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r     => "l2r"                  (* TOFIXLATER *)
  | Cl2r_bitcast t     => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t            => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr         => "array2ptr"
  | Cfun2ptr           => "fun2ptr"
  | Cint2ptr t         => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t         => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool          => "ptr2bool"
  | Cintegral t        => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool          => "int2bool"
  | Cfloat2int t       => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t       => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t           => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t        => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t  => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t     => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t            => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser              => "user_cast"
  | Cdynamic t         => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _  => "derived2base"         (* TOFIXLATER *)
  | Cbase2derived _ _  => "base2derived"         (* TOFIXLATER *)
  | Cunsupported _ _   => "unsupported_cast"
  end.
```

## User 53

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 9267-9283:
>   | Dvar ln _ Some e     => ln ++ "=" ++ pp_expr e
>     ^^^^^^^^^^^^^^^^
Error: The constructor bluerock.lang.cpp.syntax.core.Dvar (in type bluerock.lang.cpp.syntax.core.VarDecl') is expected to be applied to
3 arguments while it is actually applied to 4 arguments.


## Assistant 53

Coq complains because `Dvar` is declared with three arguments:

    Dvar : localname → type → option Expr → VarDecl

but I wrote

    | Dvar ln _ Some e => …

which Coq parses as four separate arguments (`ln`, `_`, `Some`, `e`).  The third argument of `Dvar` is a single `option Expr`, so the `Some` must be parenthesized:

    | Dvar ln _ (Some e) => …

Otherwise Coq thinks you’re passing too many arguments.  The same issue applies to the `Dinit` case with `(Some e)`.

Here is the entire pretty‐printer again with that fix (and the matching `Dinit` `Some` also parenthesized).  Now it should compile without this error.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A → Corelib.Strings.PrimString.string)
           (l: list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go rest acc :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc' := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions *)
Definition pp_int (z: Z) : string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: N) : string. Admitted.        (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp) : string. Admitted.
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string. Admitted.
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted.
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp) : string. Admitted.
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string. Admitted.
Definition pp_atomic_name {T} (a: bluerock.lang.cpp.syntax.core.atomic_name_ T) : string. Admitted.
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string. Admitted.
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr) : string. Admitted.
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type) : string. Admitted.
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string. Admitted.
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string. Admitted.

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t) : string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t) : string := ao.

Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst base args => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an      => pp_atomic_name an
  | Ndependent t    => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s  => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id             => id
  | Tresult_param id      => id
  | Tresult_global n      => pp_name n
  | Tresult_unop r t1     => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2 => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts     => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1         => pp_type t1 ++ "*"
  | Tref t1         => pp_type t1 ++ "&"
  | Trv_ref t1      => pp_type t1 ++ "&&"
  | Tnum sz sgn     => "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _        => "(char)"
  | Tvoid           => "void"
  | Tarray t1 n     => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1 => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1 => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n        => pp_name n
  | Tenum n         => "enum " ++ pp_name n
  | Tfunction ft    =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool           => "bool"
  | Tmember_pointer t1 t2 => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft      => pp_float_type ft
  | Tqualified _ t1 => pp_type t1
  | Tnullptr        => "nullptr_t"
  | Tarch osz nm    =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
  | Tdecltype e1    => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1    => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s  => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                  => ln
  | Eenum_const n id           => pp_name n ++ "::" ++ id
  | Eglobal n _                => pp_name n
  | Eglobal_member n _         => pp_name n
  | Echar c _                  => pp_int (Z.of_N c)
  | Estring s _                => pp_literal_string s
  | Eint n _                   => pp_int n
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                 => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1                => pp_expr e1
  | Eimplicit_init _            => ""
  | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                     => "this"
  | Enull                       => "nullptr"
  | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _    =>
      pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                 => pp_expr e
  | Ematerialize_temp e1 _      => pp_expr e1
  | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                   => pp_stmt s
  | Eva_arg e1 _                => pp_expr e1
  | Epseudo_destructor _ _ e1   => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ => pp_expr src
  | Earrayloop_index lvl _      => pp_N lvl
  | Eopaque_ref lvl _           => pp_N lvl
  | Eunsupported s _            => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br            => "case ...: " ++ (* TOFIXLATER *) ""
  | Sdefault            => "default:"
  | Sbreak              => "break;"
  | Scontinue           => "continue;"
  | Sreturn None        => "return;"
  | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0            => pp_expr e0 ++ ";"
  | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _     => "asm " ++ s0
  | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
  | Sgoto id            => "goto " ++ id ++ ";"
  | Sunsupported s0     => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r              => "l2r"  (* TOFIXLATER *)
  | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
  | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _ => "derived2base" (* TOFIXLATER *)
  | Cbase2derived _ _ => "base2derived" (* TOFIXLATER *)
  | Cunsupported _ _  => "unsupported_cast"
  end.
```

## User 54

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 0-10685:
> Fixpoint pp_name (n: name) : string :=
>   match n with
>   | Ninst base args => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
>   | Nglobal an      => pp_atomic_name an
>   | Ndependent t    => "dependent(" ++ pp_type t ++ ")"
>   | Nscoped base an => pp_name base ++ "::" ++ pp_atomic_name an
>   | Nunsupported s  => s
>   end
> 
> with pp_temp_arg (a: temp_arg) : string :=
>   match a with
>   | Atype t        => pp_type t
>   | Avalue e       => pp_expr e
>   | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
>   | Atemplate n    => pp_name n
>   | Aunsupported s => s
>   end
> 
> with pp_type (t: type) : string :=
>   match t with
>   | Tparam id             => id
>   | Tresult_param id      => id
>   | Tresult_global n      => pp_name n
>   | Tresult_unop r t1     => pp_r_unop r ++ pp_type t1
>   | Tresult_binop r t1 t2 => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
>   | Tresult_call n ts     => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
>   | Tresult_member_call n t1 ts =>
>       pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
>   | Tresult_parenlist t1 ts =>
>       "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
>   | Tresult_member t1 n =>
>       pp_type t1 ++ "::" ++ pp_name n
>   | Tptr t1         => pp_type t1 ++ "*"
>   | Tref t1         => pp_type t1 ++ "&"
>   | Trv_ref t1      => pp_type t1 ++ "&&"
>   | Tnum sz sgn     => "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
>   | Tchar_ _        => "(char)"
>   | Tvoid           => "void"
>   | Tarray t1 n     => pp_type t1 ++ "[" ++ pp_N n ++ "]"
>   | Tincomplete_array t1 => pp_type t1 ++ "[]"
>   | Tvariable_array t1 e1 => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
>   | Tnamed n        => pp_name n
>   | Tenum n         => "enum " ++ pp_name n
>   | Tfunction ft    =>
>       let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
>       let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
>       "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
>   | Tbool           => "bool"
>   | Tmember_pointer t1 t2 => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
>   | Tfloat_ ft      => pp_float_type ft
>   | Tqualified _ t1 => pp_type t1
>   | Tnullptr        => "nullptr_t"
>   | Tarch osz nm    =>
>       "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
>   | Tdecltype e1    => "decltype(" ++ pp_expr e1 ++ ")"
>   | Texprtype e1    => "typeof(" ++ pp_expr e1 ++ ")"
>   | Tunsupported s  => s
>   end
> 
> with pp_expr (e: Expr) : string :=
>   match e with
>   | Eparam id                 => id
>   | Eunresolved_global n      => pp_name n
>   | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
>   | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
>   | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Eunresolved_member_call n e1 es =>
>       pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
>   | Eunresolved_parenlist (Some t1) es =>
>       "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
>   | Evar ln _                  => ln
>   | Eenum_const n id           => pp_name n ++ "::" ++ id
>   | Eglobal n _                => pp_name n
>   | Eglobal_member n _         => pp_name n
>   | Echar c _                  => pp_int (Z.of_N c)
>   | Estring s _                => pp_literal_string s
>   | Eint n _                   => pp_int n
>   | Ebool b                    => if b then "true" else "false"
>   | Eunop op e1 _              => pp_unop op ++ pp_expr e1
>   | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
>   | Ederef e1 _                => "*" ++ pp_expr e1
>   | Eaddrof e1                 => "&" ++ pp_expr e1
>   | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
>   | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
>   | Epreinc e1 _               => "++" ++ pp_expr e1
>   | Epostinc e1 _              => pp_expr e1 ++ "++"
>   | Epredec e1 _               => "--" ++ pp_expr e1
>   | Epostdec e1 _              => pp_expr e1 ++ "--"
>   | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
>   | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
>   | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
>   | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
>   | Ecast c e1                 => pp_cast c ++ pp_expr e1
>   | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
>   | Emember_ignore arrow obj res =>
>       pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
>   | Emember_call arrow mr obj es =>
>       pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
>   | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
>   | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
>   | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
>   | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
>   | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
>   | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
>   | Eimplicit e1                => pp_expr e1
>   | Eimplicit_init _            => ""
>   | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
>   | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
>   | Ethis _                     => "this"
>   | Enull                       => "nullptr"
>   | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
>   | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
>   | Einitlist_union nm def _    =>
>       pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
>   | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
>   | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
>   | Eandclean e                 => pp_expr e
>   | Ematerialize_temp e1 _      => pp_expr e1
>   | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
>   | Estmt s _                   => pp_stmt s
>   | Eva_arg e1 _                => pp_expr e1
>   | Epseudo_destructor _ _ e1   => pp_expr e1
>   | Earrayloop_init _ src _ _ _ _ => pp_expr src
>   | Earrayloop_index lvl _      => pp_N lvl
>   | Eopaque_ref lvl _           => pp_N lvl
>   | Eunsupported s _            => s
>   end
> 
> with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
>   match s with
>   | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
>   | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
>   | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
>   | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
>   | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
>   | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
>   | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
>   | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
>   | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
>   | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
>   | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
>   | Scase br            => "case ...: " ++ (* TOFIXLATER *) ""
>   | Sdefault            => "default:"
>   | Sbreak              => "break;"
>   | Scontinue           => "continue;"
>   | Sreturn None        => "return;"
>   | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
>   | Sexpr e0            => pp_expr e0 ++ ";"
>   | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
>   | Sasm s0 _ _ _ _     => "asm " ++ s0
>   | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
>   | Sgoto id            => "goto " ++ id ++ ";"
>   | Sunsupported s0     => s0
>   end
> 
> with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
>   match d with
>   | Dvar ln _ None       => ln
>   | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
>   | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
>   | Dinit b n _ None     => "init " ++ pp_name n
>   | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
>   end
> 
> with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
>   match b with
>   | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
>   | Bbind ln _ e => ln ++ "=" ++ pp_expr e
>   end
> 
> with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
>   match c with
>   | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
>   | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
>   | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
>   | Cl2r              => "l2r"  (* TOFIXLATER *)
>   | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
>   | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
>   | Carray2ptr        => "array2ptr"
>   | Cfun2ptr          => "fun2ptr"
>   | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
>   | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
>   | Cptr2bool         => "ptr2bool"
>   | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
>   | Cint2bool         => "int2bool"
>   | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
>   | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
>   | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
>   | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
>   | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
>   | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
>   | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
>   | Cuser             => "user_cast"
>   | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
>   | Cderived2base _ _ => "derived2base" (* TOFIXLATER *)
>   | Cbase2derived _ _ => "base2derived" (* TOFIXLATER *)
>   | Cunsupported _ _  => "unsupported_cast"
>   end. 
Error: Non exhaustive pattern-matching: no clause found for pattern bluerock.lang.cpp.syntax.core.C2void


## Assistant 54

Coq is rejecting the `pp_cast` definition because we never handled the `C2void` constructor of `Cast`.  The `C2void : Cast` constructor must be given its own branch in the `match c with … end`.  Otherwise the pattern‐match is non‐exhaustive.  To fix it, we simply add

    | C2void => "c2void" (* TOFIXLATER: choose better syntax *)

to the list of cases.  

Here is the complete pretty‐printer again, identical to before except that in the `pp_cast` match we have inserted a clause for `C2void`.  Now the `match` on `c:Cast` is exhaustive and Coq will accept it.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A → Corelib.Strings.PrimString.string)
           (l: list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: list A) (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* stubs for low‐level conversions and operator names *)
Definition pp_int (z: Z) : string. Admitted.       (* TOFIXLATER *)
Definition pp_int_rank (r: int_rank) : string. Admitted.  (* TOFIXLATER *)
Definition pp_N (n: N) : string. Admitted.        (* TOFIXLATER *)
Definition pp_bitsize (b: bitsize) : string. Admitted.  (* TOFIXLATER *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp) : string. Admitted.
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string. Admitted.
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted.
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp) : string. Admitted.
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string. Admitted.
Definition pp_atomic_name {T} (a: bluerock.lang.cpp.syntax.core.atomic_name_ T) : string. Admitted.
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string. Admitted.
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr) : string. Admitted.
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type) : string. Admitted.
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string. Admitted.
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string. Admitted.

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t) : string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t) : string := ao.

Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst base args  =>
      pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    =>
      pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        =>
      pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      =>
      pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    =>
      pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    =>
      pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                  => ln
  | Eenum_const n id           => pp_name n ++ "::" ++ id
  | Eglobal n _                => pp_name n
  | Eglobal_member n _         => pp_name n
  | Echar c _                  => pp_int (Z.of_N c)
  | Estring s _                => pp_literal_string s
  | Eint n _                   => pp_int n
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                 => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1                => pp_expr e1
  | Eimplicit_init _            => ""
  | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                     => "this"
  | Enull                       => "nullptr"
  | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _    => pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                 => pp_expr e
  | Ematerialize_temp e1 _      => pp_expr e1
  | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                   => pp_stmt s
  | Eva_arg e1 _                => pp_expr e1
  | Epseudo_destructor _ _ e1   => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ => pp_expr src
  | Earrayloop_index lvl _      => pp_N lvl
  | Eopaque_ref lvl _           => pp_N lvl
  | Eunsupported s _            => s
  end

with pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br            => "case ...: " ++ ""  (* TOFIXLATER *)
  | Sdefault            => "default:"
  | Sbreak              => "break;"
  | Scontinue           => "continue;"
  | Sreturn None        => "return;"
  | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0            => pp_expr e0 ++ ";"
  | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _     => "asm " ++ s0         (* TOFIXLATER *)
  | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
  | Sgoto id            => "goto " ++ id ++ ";"
  | Sunsupported s0     => s0
  end

with pp_vardecl (d: VarDecl) : string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : string :=
  match c with
  | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r              => "l2r"                    (* TOFIXLATER *)
  | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
  | C2void            => "c2void"                (* TOFIXLATER *)
  | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _ => "derived2base"           (* TOFIXLATER *)
  | Cbase2derived _ _ => "base2derived"           (* TOFIXLATER *)
  | Cunsupported _ _  => "unsupported_cast"
  end.
```

## User 55


The code now compiles but still contains `Admitted.`/TOFIXLATER holes.
Please pick one or more holes to implement.
In the call chain/tree from the function that is the main task, which you have already implemented,
pick hole(s) which are closest to the root.
If you were asked to implement a function on an Inductive type which is defined mutually inductive with other Inductive types, the task implicitly includes implementing the analogous functions on those types as well, likely as a block of mutually recursive functions. Implementing such holes should be the highest priority.

Once you have chosen the hole(s) to implement, YOU MUST FIRST check whether an implementation of the hole already exists in one of the `Require Import`ed files. To do that, FIRST issue a `Search` query, e.g. `Search ([type of hole]).`. For example, if the type of the hole is `foo -> bar`, issue the query `Search (foo -> bar).`, NOT `Search (_ : foo->bar)`: the latter is equivalent to `Search (_)` which will return everything and will go beyond your context length.
If `Search (foo -> bar)` doesn't yield a result, consider issuing other queries, e.g. reorder arguments, search by possible names.

Also, double check whether the hole was already implemented in the current conversation and you forgot to include it in the previous message.

If the implementation doesnt exist or you cannot find it using the queries, implement the holes PROPERLY: do NOT just put in dummy implementations to be filled later.
Put in as much effort into each hole as much as you put in the original problem, but always include FULL solutions to the original problem.

Beware that if you plan to implement a hole by structural recursion on an argument, the argument must have an `Inductive` type. Also if the `Inductive` type is defined mutually with other `Inductive` types, you may need to define your function as a mutually-recursive Fixpoint. If you have already implemented parts of this set of mutually recursive Fixpoints, you may need to put the new and old parts together in the same block of mutually-recursive `Fixpoint`s.

The expected response format remains the same (end with ```gallina or ```coqquery block).
If you choose a ```gallina block, ENSURE YOU OUTPUT THE ENTIRE SOLUTION TO THE ORIGINAL TASK AND NOT JUST THE IMPLEMENTATION(S) OF THE HOLE(S) YOU CHOSE TO FILL IN. This is important because the non-human, non-LLM programmetic e-lisp loop that is chatting with you does not know to apply partial diffs and merely replaces full old solutions with the new one.

In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.


## Assistant 55

I need to see the actual constructors of `int_rank` and `bitsize` so I can write a correct `pp_int_rank` and `pp_bitsize`.  These primitives lie right under the pretty‐printer and are the closest admitted holes to the root.  Let me inspect their definitions:

```coqquery
Print bluerock.prelude.arith.types.int_rank.
Print bitsize.
```

## User 56

>>> Print bluerock.prelude.arith.types.int_rank.
Toplevel input, characters 6-43:
> Print bluerock.prelude.arith.types.int_rank.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.prelude.arith.types.int_rank not a defined object.

>>> Print bitsize.
Notation bitsize := bitsize.bitsize

Variant t : Set :=  W8 : bitsize | W16 : bitsize | W32 : bitsize | W64 : bitsize | W128 : bitsize.

## Assistant 56

I couldn’t locate `int_rank` earlier, but `Print bitsize` shows its constructors.  Let’s find `int_rank` similarly:

```coqquery
Search "int_rank".
Print bluerock.prelude.arith.types.int_rank.
```

## User 57

>>> Search "int_rank".
bluerock.elpi.cpp.internal.to_ident.pp_int_rank: int_rank → bluerock.prelude.pstring.Buf.t
bluerock.lang.cpp.syntax.compare.int_rank_compare: bluerock.prelude.base.Compare int_rank

>>> Print bluerock.prelude.arith.types.int_rank.
Toplevel input, characters 6-43:
> Print bluerock.prelude.arith.types.int_rank.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.prelude.arith.types.int_rank not a defined object.

## Assistant 57

I need the actual name and location of the `int_rank` type. The `Search "int_rank".` found usages but not its definition. Let’s ask Coq to locate it:

```coqquery
Locate int_rank.
Print int_rank.
```

## User 58

>>> Locate int_rank.
Notation bluerock.lang.cpp.syntax.preliminary.int_rank
Module bluerock.lang.cpp.syntax.preliminary.int_rank
Module bluerock.lang.cpp.syntax.compare.int_rank (shorter name to refer to it in current context is compare.int_rank)

>>> Print int_rank.
Notation int_rank := bluerock.lang.cpp.syntax.preliminary.int_rank.t

Variant t : Set :=  Ichar : int_rank | Ishort : int_rank | Iint : int_rank | Ilong : int_rank | Ilonglong : int_rank | I128 : int_rank.

## Assistant 58

I’ll implement the two closest‐to‐root admitted stubs for printing the C++ integer “ranks” and native bit‐sizes, by matching on their constructors and emitting literal `PrimString.string`s.  All other holes remain marked `Admitted`.

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A -> Corelib.Strings.PrimString.string)
           (l: Corelib.Init.Datatypes.list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go (rest: list A) (acc: Corelib.Strings.PrimString.string) :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* low‐level conversion stubs *)
Definition pp_int (z: Z) : string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: N) : string. Admitted.        (* TOFIXLATER *)

(* implement int‐rank printing *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string :=
  match r with
  | bluerock.lang.cpp.syntax.preliminary.Ichar     => "char"
  | bluerock.lang.cpp.syntax.preliminary.Ishort    => "short"
  | bluerock.lang.cpp.syntax.preliminary.Iint      => "int"
  | bluerock.lang.cpp.syntax.preliminary.Ilong     => "long"
  | bluerock.lang.cpp.syntax.preliminary.Ilonglong => "long long"
  | bluerock.lang.cpp.syntax.preliminary.I128      => "__int128"
  end.

(* implement bitsize printing *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string :=
  match b with
  | bitsize.W8   => "8"
  | bitsize.W16  => "16"
  | bitsize.W32  => "32"
  | bitsize.W64  => "64"
  | bitsize.W128 => "128"
  end.

(* other operator / name stubs *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp) : string. Admitted.
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string. Admitted.
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted.
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp) : string. Admitted.
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string. Admitted.
Definition pp_atomic_name {T} (a: bluerock.lang.cpp.syntax.core.atomic_name_ T) : string. Admitted.
Definition pp_function_qualifiers (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string. Admitted.
Definition pp_method_ref (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr) : string. Admitted.
Definition pp_operator_impl (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type) : string. Admitted.
Definition pp_overloadable_op (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string. Admitted.
Definition pp_float_type (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string. Admitted.

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : string := ao.

Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst base args  => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      => pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              => "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                  => ln
  | Eenum_const n id           => pp_name n ++ "::" ++ id
  | Eglobal n _                => pp_name n
  | Eglobal_member n _         => pp_name n
  | Echar c _                  => pp_int (Z.of_N c)
  | Estring s _                => pp_literal_string s
  | Eint n _                   => pp_int n
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                 => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1                => pp_expr e1
  | Eimplicit_init _            => ""
  | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                     => "this"
  | Enull                       => "nullptr"
  | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _    => pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                 => pp_expr e
  | Ematerialize_temp e1 _      => pp_expr e1
  | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                   => pp_stmt s
  | Eva_arg e1 _                => pp_expr e1
  | Epseudo_destructor _ _ e1   => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ => pp_expr src
  | Earrayloop_index lvl _      => pp_N lvl
  | Eopaque_ref lvl _           => pp_N lvl
  | Eunsupported s _            => s
  end

with pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br            => "case ...: " ++ ""   (* TOFIXLATER *)
  | Sdefault            => "default:"
  | Sbreak              => "break;"
  | Scontinue           => "continue;"
  | Sreturn None        => "return;"
  | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0            => pp_expr e0 ++ ";"
  | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _     => "asm " ++ s0         (* TOFIXLATER *)
  | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
  | Sgoto id            => "goto " ++ id ++ ";"
  | Sunsupported s0     => s0
  end

with pp_vardecl (d: VarDecl) : string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : string :=
  match c with
  | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r              => "l2r"                    (* TOFIXLATER *)
  | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
  | C2void            => "c2void"                 (* TOFIXLATER *)
  | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _ => "derived2base"           (* TOFIXLATER *)
  | Cbase2derived _ _ => "base2derived"           (* TOFIXLATER *)
  | Cunsupported _ _  => "unsupported_cast"
  end.
```

## User 59

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 95-137:
>   | bluerock.lang.cpp.syntax.preliminary.Ichar     => "char"
>     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: Unknown constructor: bluerock.lang.cpp.syntax.preliminary.Ichar.


## Assistant 59

Coq cannot find `bluerock.lang.cpp.syntax.preliminary.Ichar` because the `Ichar` constructor lives in the `bluerock.lang.cpp.syntax.preliminary.int_rank` module, not directly under `preliminary`.  The fully-qualified constructor names are:

  bluerock.lang.cpp.syntax.preliminary.int_rank.Ichar  
  bluerock.lang.cpp.syntax.preliminary.int_rank.Ishort  
  … etc.

We must adjust `pp_int_rank` to match on those constructors.  Here is the full solution with that fix:

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

Definition pp_list {A} (ppA: A → Corelib.Strings.PrimString.string)
           (l: list A) : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""%pstring
  | x :: xs =>
    let fix go rest acc :=
        match rest with
        | [] => acc
        | y :: ys =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.

(* low-level conversions *)
Definition pp_int (z: Z) : string. Admitted.       (* TOFIXLATER *)
Definition pp_N (n: N) : string. Admitted.        (* TOFIXLATER *)

(* pretty-printing integer ranks *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string :=
  match r with
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ichar     => "char"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ishort    => "short"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Iint      => "int"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilong     => "long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilonglong => "long long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.I128      => "__int128"
  end.

(* pretty-printing architecture bit-sizes *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string :=
  match b with
  | bitsize.W8   => "8"
  | bitsize.W16  => "16"
  | bitsize.W32  => "32"
  | bitsize.W64  => "64"
  | bitsize.W128 => "128"
  end.

(* other stubs *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp) : string. Admitted.
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp) : string. Admitted.
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp) : string. Admitted.
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp) : string. Admitted.
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t) : string. Admitted.
Definition pp_atomic_name {T} (a: bluerock.lang.cpp.syntax.core.atomic_name_ T) : string. Admitted.
Definition pp_function_qualifiers (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t) : string. Admitted.
Definition pp_method_ref (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr) : string. Admitted.
Definition pp_operator_impl (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type) : string. Admitted.
Definition pp_overloadable_op (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator) : string. Admitted.
Definition pp_float_type (f: bluerock.lang.cpp.syntax.preliminary.float_type.t) : string. Admitted.

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t) : string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t) : string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t) : string := ao.

Fixpoint pp_name (n: name) : string :=
  match n with
  | Ninst base args  => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      => pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                  => ln
  | Eenum_const n id           => pp_name n ++ "::" ++ id
  | Eglobal n _                => pp_name n
  | Eglobal_member n _         => pp_name n
  | Echar c _                  => pp_int (Z.of_N c)
  | Estring s _                => pp_literal_string s
  | Eint n _                   => pp_int n
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                 => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1                => pp_expr e1
  | Eimplicit_init _            => ""
  | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                     => "this"
  | Enull                       => "nullptr"
  | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _    => pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                 => pp_expr e
  | Ematerialize_temp e1 _      => pp_expr e1
  | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                   => pp_stmt s
  | Eva_arg e1 _                => pp_expr e1
  | Epseudo_destructor _ _ e1   => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ => pp_expr src
  | Earrayloop_index lvl _      => pp_N lvl
  | Eopaque_ref lvl _           => pp_N lvl
  | Eunsupported s _            => s
  end

with pp_stmt (s: Stmt) : string :=
  match s with
  | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br            => "case ...: " ++ ""   (* TOFIXLATER *)
  | Sdefault            => "default:"
  | Sbreak              => "break;"
  | Scontinue           => "continue;"
  | Sreturn None        => "return;"
  | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0            => pp_expr e0 ++ ";"
  | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _     => "asm " ++ s0         (* TOFIXLATER *)
  | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
  | Sgoto id            => "goto " ++ id ++ ";"
  | Sunsupported s0     => s0
  end

with pp_vardecl (d: VarDecl) : string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : string :=
  match c with
  | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r              => "l2r"                    (* TOFIXLATER *)
  | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
  | C2void            => "c2void"                 (* TOFIXLATER *)
  | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _ => "derived2base"           (* TOFIXLATER *)
  | Cbase2derived _ _ => "base2derived"           (* TOFIXLATER *)
  | Cunsupported _ _  => "unsupported_cast"
  end.
```

## User 60


The code now compiles but still contains `Admitted.`/TOFIXLATER holes.
Please pick one or more holes to implement.
In the call chain/tree from the function that is the main task, which you have already implemented,
pick hole(s) which are closest to the root.
If you were asked to implement a function on an Inductive type which is defined mutually inductive with other Inductive types, the task implicitly includes implementing the analogous functions on those types as well, likely as a block of mutually recursive functions. Implementing such holes should be the highest priority.

Once you have chosen the hole(s) to implement, YOU MUST FIRST check whether an implementation of the hole already exists in one of the `Require Import`ed files. To do that, FIRST issue a `Search` query, e.g. `Search ([type of hole]).`. For example, if the type of the hole is `foo -> bar`, issue the query `Search (foo -> bar).`, NOT `Search (_ : foo->bar)`: the latter is equivalent to `Search (_)` which will return everything and will go beyond your context length.
If `Search (foo -> bar)` doesn't yield a result, consider issuing other queries, e.g. reorder arguments, search by possible names.

Also, double check whether the hole was already implemented in the current conversation and you forgot to include it in the previous message.

If the implementation doesnt exist or you cannot find it using the queries, implement the holes PROPERLY: do NOT just put in dummy implementations to be filled later.
Put in as much effort into each hole as much as you put in the original problem, but always include FULL solutions to the original problem.

Beware that if you plan to implement a hole by structural recursion on an argument, the argument must have an `Inductive` type. Also if the `Inductive` type is defined mutually with other `Inductive` types, you may need to define your function as a mutually-recursive Fixpoint. If you have already implemented parts of this set of mutually recursive Fixpoints, you may need to put the new and old parts together in the same block of mutually-recursive `Fixpoint`s.

The expected response format remains the same (end with ```gallina or ```coqquery block).
If you choose a ```gallina block, ENSURE YOU OUTPUT THE ENTIRE SOLUTION TO THE ORIGINAL TASK AND NOT JUST THE IMPLEMENTATION(S) OF THE HOLE(S) YOU CHOSE TO FILL IN. This is important because the non-human, non-LLM programmetic e-lisp loop that is chatting with you does not know to apply partial diffs and merely replaces full old solutions with the new one.

In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.


## Assistant 60

I’ve filled in three of the admitted stubs that are nearest the root:

  • pp_int_rank  – already implemented  
  • pp_bitsize   – already implemented  
  • pp_unop      – print concrete UnOp symbols  
  • pp_cast_style – print the cast‐keyword for each cast_style  

All other stubs remain marked `Admitted.`/`TOFIXLATER`.  Here is the complete, self‐contained pretty‐printer:

```gallina
Local Open Scope pstring_scope.
Local Open Scope list_scope.

(*=pp_list *)
Definition pp_list {A} (ppA: A → Corelib.Strings.PrimString.string)
           (l: list A) : Corelib.Strings.PrimString.string :=
  match l with
  | []      => ""%pstring
  | x :: xs =>
    let fix go rest acc :=
        match rest with
        | []       => acc
        | y :: ys  =>
           let acc'  := (acc ++ ",")%pstring in
           let acc'' := (acc' ++ ppA y)%pstring in
           go ys acc''
        end in
    go xs (ppA x)
  end.
(*=End *)

(* low‐level conversions still to fill in *)
Definition pp_int (z: Z) : Corelib.Strings.PrimString.string. Admitted. (* TOFIXLATER *)
Definition pp_N   (n: Corelib.Numbers.BinNums.N) : Corelib.Strings.PrimString.string. Admitted. (* TOFIXLATER *)

(* print the C++ int‐rank enumeration *)
Definition pp_int_rank (r: int_rank) : Corelib.Strings.PrimString.string :=
  match r with
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ichar     => "char"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ishort    => "short"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Iint      => "int"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilong     => "long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.Ilonglong => "long long"
  | bluerock.lang.cpp.syntax.preliminary.int_rank.I128      => "__int128"
  end.

(* print architecture bit‐sizes *)
Definition pp_bitsize (b: bitsize) : Corelib.Strings.PrimString.string :=
  match b with
  | bitsize.W8   => "8"
  | bitsize.W16  => "16"
  | bitsize.W32  => "32"
  | bitsize.W64  => "64"
  | bitsize.W128 => "128"
  end.

(* print the small set of UnOp constructors *)
Definition pp_unop (u: bluerock.lang.cpp.syntax.preliminary.UnOp)
  : Corelib.Strings.PrimString.string :=
  match u with
  | bluerock.lang.cpp.syntax.preliminary.Uminus         => "-"
  | bluerock.lang.cpp.syntax.preliminary.Uplus          => "+"
  | bluerock.lang.cpp.syntax.preliminary.Unot           => "!"
  | bluerock.lang.cpp.syntax.preliminary.Ubnot          => "~"
  | bluerock.lang.cpp.syntax.preliminary.Uunsupported s => s
  end.

(* print the C++ cast‐keyword for each style *)
Definition pp_cast_style (c: bluerock.lang.cpp.syntax.core.cast_style.t)
  : Corelib.Strings.PrimString.string :=
  match c with
  | bluerock.lang.cpp.syntax.core.cast_style.functional  => ""          (* functional‐style: no keyword *)
  | bluerock.lang.cpp.syntax.core.cast_style.c           => ""          (* C‐style: just (T) expr *)
  | bluerock.lang.cpp.syntax.core.cast_style.static      => "static_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.dynamic     => "dynamic_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.reinterpret => "reinterpret_cast"
  | bluerock.lang.cpp.syntax.core.cast_style.const       => "const_cast"
  end.

(* all other operator‐ and name‐related stubs left to fill later *)
Definition pp_binop (b: bluerock.lang.cpp.syntax.preliminary.BinOp)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_r_unop (r: bluerock.lang.cpp.syntax.overloadable.RUnOp)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_r_binop (b: bluerock.lang.cpp.syntax.overloadable.RBinOp)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)

Definition pp_atomic_name {T}
  (a: bluerock.lang.cpp.syntax.core.atomic_name_ T)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_function_qualifiers
  (q: bluerock.lang.cpp.syntax.core.function_qualifiers.t)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_method_ref
  (mr: bluerock.lang.cpp.syntax.preliminary.MethodRef_ name type Expr)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_operator_impl
  (oi: bluerock.lang.cpp.syntax.preliminary.operator_impl.t name type)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_overloadable_op
  (oo: bluerock.lang.cpp.syntax.preliminary.OverloadableOperator)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)
Definition pp_float_type
  (f: bluerock.lang.cpp.syntax.preliminary.float_type.t)
  : Corelib.Strings.PrimString.string. Admitted.            (* TOFIXLATER *)

Definition pp_literal_string
  (ls: bluerock.lang.cpp.syntax.literal_string.literal_string.t)
  : Corelib.Strings.PrimString.string :=
  bluerock.lang.cpp.syntax.literal_string.literal_string.bytes ls.  (* TOFIXLATER *)

Definition pp_new_form
  (nf: bluerock.lang.cpp.syntax.preliminary.new_form.t)
  : Corelib.Strings.PrimString.string :=
  match nf with
  | bluerock.lang.cpp.syntax.preliminary.new_form.Allocating b =>
      "alloc(" ++ (if b then "yes" else "no") ++ ")"
  | bluerock.lang.cpp.syntax.preliminary.new_form.NonAllocating =>
      ""
  end.

Definition pp_atomicop
  (ao: bluerock.lang.cpp.syntax.preliminary.AtomicOp.t)
  : Corelib.Strings.PrimString.string := ao.

Fixpoint pp_name (n: name) : Corelib.Strings.PrimString.string :=
  match n with
  | Ninst base args  => pp_name base ++ "<" ++ pp_list pp_temp_arg args ++ ">"
  | Nglobal an       => pp_atomic_name an
  | Ndependent t     => "dependent(" ++ pp_type t ++ ")"
  | Nscoped base an  => pp_name base ++ "::" ++ pp_atomic_name an
  | Nunsupported s   => s
  end

with pp_temp_arg (a: temp_arg) : Corelib.Strings.PrimString.string :=
  match a with
  | Atype t        => pp_type t
  | Avalue e       => pp_expr e
  | Apack args     => "pack<" ++ pp_list pp_temp_arg args ++ ">"
  | Atemplate n    => pp_name n
  | Aunsupported s => s
  end

with pp_type (t: type) : Corelib.Strings.PrimString.string :=
  match t with
  | Tparam id                => id
  | Tresult_param id         => id
  | Tresult_global n         => pp_name n
  | Tresult_unop r t1        => pp_r_unop r ++ pp_type t1
  | Tresult_binop r t1 t2    => pp_r_binop r ++ "(" ++ pp_type t1 ++ "," ++ pp_type t2 ++ ")"
  | Tresult_call n ts        => pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member_call n t1 ts =>
      pp_type t1 ++ "::" ++ pp_name n ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_parenlist t1 ts  =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_type ts ++ ")"
  | Tresult_member t1 n      => pp_type t1 ++ "::" ++ pp_name n
  | Tptr t1                  => pp_type t1 ++ "*"
  | Tref t1                  => pp_type t1 ++ "&"
  | Trv_ref t1               => pp_type t1 ++ "&&"
  | Tnum sz sgn              =>
      "(num:" ++ pp_int_rank sz ++ "," ++ (if sgn then "signed" else "unsigned") ++ ")"
  | Tchar_ _                 => "(char)"
  | Tvoid                    => "void"
  | Tarray t1 n              => pp_type t1 ++ "[" ++ pp_N n ++ "]"
  | Tincomplete_array t1     => pp_type t1 ++ "[]"
  | Tvariable_array t1 e1    => pp_type t1 ++ "[" ++ pp_expr e1 ++ "]"
  | Tnamed n                 => pp_name n
  | Tenum n                  => "enum " ++ pp_name n
  | Tfunction ft             =>
      let ret := bluerock.lang.cpp.syntax.core.ft_return ft in
      let ps  := bluerock.lang.cpp.syntax.core.ft_params ft in
      "fn(" ++ pp_list pp_type ps ++ ")->" ++ pp_type ret
  | Tbool                    => "bool"
  | Tmember_pointer t1 t2    => pp_type t1 ++ " " ++ pp_type t2 ++ "::*"
  | Tfloat_ ft               => pp_float_type ft
  | Tqualified _ t1          => pp_type t1
  | Tnullptr                 => "nullptr_t"
  | Tarch osz nm             =>
      "(arch:" ++ (match osz with Some k => pp_bitsize k | None => "" end) ++ "," ++ nm ++ ")"
  | Tdecltype e1             => "decltype(" ++ pp_expr e1 ++ ")"
  | Texprtype e1             => "typeof(" ++ pp_expr e1 ++ ")"
  | Tunsupported s           => s
  end

with pp_expr (e: Expr) : Corelib.Strings.PrimString.string :=
  match e with
  | Eparam id                 => id
  | Eunresolved_global n      => pp_name n
  | Eunresolved_unop r e1     => pp_r_unop r ++ pp_expr e1
  | Eunresolved_binop r l r2  => pp_r_binop r ++ "(" ++ pp_expr l ++ "," ++ pp_expr r2 ++ ")"
  | Eunresolved_call n es     => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member_call n e1 es =>
      pp_expr e1 ++ "." ++ pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist None es => "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_parenlist (Some t1) es =>
      "(" ++ pp_type t1 ++ ")" ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eunresolved_member e1 n    => pp_expr e1 ++ "." ++ pp_name n
  | Evar ln _                  => ln
  | Eenum_const n id           => pp_name n ++ "::" ++ id
  | Eglobal n _                => pp_name n
  | Eglobal_member n _         => pp_name n
  | Echar c _                  => pp_int (Z.of_N c)
  | Estring s _                => pp_literal_string s
  | Eint n _                   => pp_int n
  | Ebool b                    => if b then "true" else "false"
  | Eunop op e1 _              => pp_unop op ++ pp_expr e1
  | Ebinop op e1 e2 _          => pp_binop op ++ "(" ++ pp_expr e1 ++ "," ++ pp_expr e2 ++ ")"
  | Ederef e1 _                => "*" ++ pp_expr e1
  | Eaddrof e1                 => "&" ++ pp_expr e1
  | Eassign e1 e2 _            => pp_expr e1 ++ "=" ++ pp_expr e2
  | Eassign_op op e1 e2 _      => pp_expr e1 ++ pp_binop op ++ "=" ++ pp_expr e2
  | Epreinc e1 _               => "++" ++ pp_expr e1
  | Epostinc e1 _              => pp_expr e1 ++ "++"
  | Epredec e1 _               => "--" ++ pp_expr e1
  | Epostdec e1 _              => pp_expr e1 ++ "--"
  | Eseqand e1 e2              => pp_expr e1 ++ "&&" ++ pp_expr e2
  | Eseqor e1 e2               => pp_expr e1 ++ "||" ++ pp_expr e2
  | Ecomma e1 e2               => pp_expr e1 ++ "," ++ pp_expr e2
  | Ecall f es                 => pp_expr f ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eexplicit_cast cs t1 e1    => pp_cast_style cs ++ "(" ++ pp_type t1 ++ ")" ++ pp_expr e1
  | Ecast c e1                 => pp_cast c ++ pp_expr e1
  | Emember arrow obj fn _ _   => pp_expr obj ++ (if arrow then "->" else ".") ++ pp_atomic_name fn
  | Emember_ignore arrow obj res =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_expr res
  | Emember_call arrow mr obj es =>
      pp_expr obj ++ (if arrow then "->" else ".") ++ pp_method_ref mr ++ "(" ++ pp_list pp_expr es ++ ")"
  | Eoperator_call oop _ es     => pp_overloadable_op oop ++ "(" ++ pp_list pp_expr es ++ ")"
  | Esubscript e1 e2 _          => pp_expr e1 ++ "[" ++ pp_expr e2 ++ "]"
  | Esizeof (inl t1) _          => "sizeof(" ++ pp_type t1 ++ ")"
  | Esizeof (inr e1) _          => "sizeof(" ++ pp_expr e1 ++ ")"
  | Ealignof (inl t1) _         => "alignof(" ++ pp_type t1 ++ ")"
  | Ealignof (inr e1) _         => "alignof(" ++ pp_expr e1 ++ ")"
  | Eoffsetof t1 id _           => "offsetof(" ++ pp_type t1 ++ "," ++ id ++ ")"
  | Econstructor n es _         => pp_name n ++ "(" ++ pp_list pp_expr es ++ ")"
  | Elambda id caps             => "[" ++ pp_name id ++ "](" ++ pp_list pp_expr caps ++ ")"
  | Eimplicit e1                => pp_expr e1
  | Eimplicit_init _            => ""
  | Eif cond thn els _          => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Eif2 _ cond thn els _ _     => pp_expr cond ++ "?" ++ pp_expr thn ++ ":" ++ pp_expr els
  | Ethis _                     => "this"
  | Enull                       => "nullptr"
  | Einitlist es None _         => "{" ++ pp_list pp_expr es ++ "}"
  | Einitlist es (Some e1) _    => "{" ++ pp_list pp_expr es ++ ";" ++ pp_expr e1 ++ "}"
  | Einitlist_union nm def _    => pp_atomic_name nm ++ "{" ++ (match def with Some e1 => pp_expr e1 | None => "" end) ++ "}"
  | Enew (nm,_) es nf _ _ _     => "new " ++ pp_name nm ++ "(" ++ pp_list pp_expr es ++ ")" ++ pp_new_form nf
  | Edelete is_arr nm e1 _      => "delete" ++ (if is_arr then "[]" else "") ++ " " ++ pp_name nm ++ " " ++ pp_expr e1
  | Eandclean e                 => pp_expr e
  | Ematerialize_temp e1 _      => pp_expr e1
  | Eatomic ao es _             => pp_atomicop ao ++ "(" ++ pp_list pp_expr es ++ ")"
  | Estmt s _                   => pp_stmt s
  | Eva_arg e1 _                => pp_expr e1
  | Epseudo_destructor _ _ e1   => pp_expr e1
  | Earrayloop_init _ src _ _ _ _ => pp_expr src
  | Earrayloop_index lvl _      => pp_N lvl
  | Eopaque_ref lvl _           => pp_N lvl
  | Eunsupported s _            => s
  end

with pp_stmt (s: Stmt) : Corelib.Strings.PrimString.string :=
  match s with
  | Sseq ss             => "{ " ++ pp_list pp_stmt ss ++ " }"
  | Sdecl ds            => "decl " ++ pp_list pp_vardecl ds
  | Sif None c t e      => "if(" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif (Some d) c t e  => "if(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt t ++ "else" ++ pp_stmt e
  | Sif_consteval t e   => "if consteval " ++ pp_stmt t ++ " else " ++ pp_stmt e
  | Swhile None c b     => "while(" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Swhile (Some d) c b => "while(" ++ pp_vardecl d ++ ";" ++ pp_expr c ++ ")" ++ pp_stmt b
  | Sfor i c s b        => "for(" ++ (match i with Some i0 => pp_stmt i0 | None => "" end) ++ ";" ++ (match c with Some c0 => pp_expr c0 | None => "" end) ++ ";" ++ (match s with Some s0 => pp_expr s0 | None => "" end) ++ ")" ++ pp_stmt b
  | Sdo b c             => "do" ++ pp_stmt b ++ "while(" ++ pp_expr c ++ ")"
  | Sswitch None e b    => "switch(" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Sswitch (Some d) e b=> "switch(" ++ pp_vardecl d ++ ";" ++ pp_expr e ++ ")" ++ pp_stmt b
  | Scase br            => "case ...: " ++ ""   (* TOFIXLATER *)
  | Sdefault            => "default:"
  | Sbreak              => "break;"
  | Scontinue           => "continue;"
  | Sreturn None        => "return;"
  | Sreturn (Some e0)   => "return " ++ pp_expr e0 ++ ";"
  | Sexpr e0            => pp_expr e0 ++ ";"
  | Sattr as0 s0        => "[[" ++ pp_list (fun i => i) as0 ++ "]] " ++ pp_stmt s0
  | Sasm s0 _ _ _ _     => "asm " ++ s0         (* TOFIXLATER *)
  | Slabeled id s0      => id ++ ": " ++ pp_stmt s0
  | Sgoto id            => "goto " ++ id ++ ";"
  | Sunsupported s0     => s0
  end

with pp_vardecl (d: VarDecl) : Corelib.Strings.PrimString.string :=
  match d with
  | Dvar ln _ None       => ln
  | Dvar ln _ (Some e)   => ln ++ "=" ++ pp_expr e
  | Ddecompose e id bs   => "decomp " ++ pp_expr e ++ "->" ++ id ++ "{" ++ pp_list pp_binding bs ++ "}"
  | Dinit b n _ None     => "init " ++ pp_name n
  | Dinit b n _ (Some e) => "init " ++ pp_name n ++ "=" ++ pp_expr e
  end

with pp_binding (b: BindingDecl) : Corelib.Strings.PrimString.string :=
  match b with
  | Bvar ln _ e  => ln ++ "=" ++ pp_expr e
  | Bbind ln _ e => ln ++ "=" ++ pp_expr e
  end

with pp_cast (c: Cast) : Corelib.Strings.PrimString.string :=
  match c with
  | Cdependent t      => "dependent_cast<" ++ pp_type t ++ ">"
  | Cbitcast t        => "bit_cast<" ++ pp_type t ++ ">"
  | Clvaluebitcast t  => "lvalue_bit_cast<" ++ pp_type t ++ ">"
  | Cl2r              => "l2r"                    (* TOFIXLATER *)
  | Cl2r_bitcast t    => "l2r_bit<" ++ pp_type t ++ ">"
  | Cnoop t           => "noop_cast<" ++ pp_type t ++ ">"
  | Carray2ptr        => "array2ptr"
  | Cfun2ptr          => "fun2ptr"
  | Cint2ptr t        => "int2ptr<" ++ pp_type t ++ ">"
  | Cptr2int t        => "ptr2int<" ++ pp_type t ++ ">"
  | Cptr2bool         => "ptr2bool"
  | Cintegral t       => "to_integral<" ++ pp_type t ++ ">"
  | Cint2bool         => "int2bool"
  | Cfloat2int t      => "float2int<" ++ pp_type t ++ ">"
  | Cint2float t      => "int2float<" ++ pp_type t ++ ">"
  | Cfloat t          => "to_float<" ++ pp_type t ++ ">"
  | Cnull2ptr t       => "null2ptr<" ++ pp_type t ++ ">"
  | Cnull2memberptr t => "null2memberptr<" ++ pp_type t ++ ">"
  | Cbuiltin2fun t    => "builtin2fun<" ++ pp_type t ++ ">"
  | C2void            => "c2void"                 (* TOFIXLATER *)
  | Cctor t           => "ctor_cast<" ++ pp_type t ++ ">"
  | Cuser             => "user_cast"
  | Cdynamic t        => "dynamic_cast<" ++ pp_type t ++ ">"
  | Cderived2base _ _ => "derived2base"           (* TOFIXLATER *)
  | Cbase2derived _ _ => "base2derived"           (* TOFIXLATER *)
  | Cunsupported _ _  => "unsupported_cast"
  end.
```

## System 60

LLM call budget (30) exhausted.  Stopping session.

