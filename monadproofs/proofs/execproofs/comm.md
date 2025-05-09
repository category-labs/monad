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


## Assistant 31

I need to see the exact constructors of your C++ AST types (Stmt, Expr, etc.) in order to write the corresponding `PrimString.string`-returning printers.  Let’s first locate and print their definitions so we know all the mutually‐recursive cases we must handle.  

```coqquery
Locate Stmt.
Print bluerock.lang.cpp.syntax.stmt.Stmt.
Locate Expr.
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

>>> Locate Expr.
Notation bluerock.lang.cpp.syntax.core.Expr
Module Type bluerock.lang.cpp.logic.expr.Expr
Module bluerock.lang.cpp.syntax.compare.Expr (shorter name to refer to it in current context is compare.Expr)

>>> Print bluerock.lang.cpp.syntax.expr.Expr.
Toplevel input, characters 6-40:
> Print bluerock.lang.cpp.syntax.expr.Expr.
>       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: bluerock.lang.cpp.syntax.expr.Expr not a defined object.

## Assistant 32

I already have the AST constructors. Before writing the big mutually‐recursive printers, let me just confirm exactly which append/empty literals and helper functions are available in the PrimString scope so I can use them correctly.  

```coqquery
Locate "++"%pstring.
Search (_ ++ _)%pstring.
Search ([@_] _) in Corelib.Strings.PrimString.
```

## User 33

>>> Locate "++"%pstring.
Notation "x ++ y" := (bluerock.prelude.bytestring_core.BS.append x y) (* x in scope _bs_scope, y in scope _bs_scope *) : bs_scope
  (from bluerock.prelude.bytestring_core.BS.Bytestring_notations)
Notation "x ++ y" := (Corelib.Init.Datatypes.app x y) (* x in scope _list_scope, y in scope _list_scope *) : list_scope
  (from Corelib.Init.Datatypes)
Notation "x ++ y" := (bluerock.auto.core.internal.stdlib.D.app x y) (* x in scope _plist_scope, y in scope _plist_scope *) : plist_scope
  (from bluerock.auto.core.internal.plib.plist.PLIST.PListNotation)
Notation "x ++ y" := (stdpp.numbers.Pos.app x y) (* x in scope _positive_scope, y in scope _positive_scope *) : positive_scope
  (from stdpp.numbers.Pos.app_notations)
Notation "x ++ y" := (Corelib.Strings.PrimString.cat x y) (* x in scope _pstring_scope, y in scope _pstring_scope *) : pstring_scope
  (default interpretation) (from bluerock.prelude.pstring)
Notation "s1 ++ s2" := (Stdlib.Strings.String.append s1 s2) (* s1 in scope _string_scope, s2 in scope _string_scope *) : string_scope
  (from Stdlib.Strings.String)
Notation "x ++ y" := (bluerock.upoly.list.app x y) (* x in scope _ulist_scope, y in scope _ulist_scope *) : ulist_scope
  (from bluerock.upoly.list.Notations)

>>> Search (_ ++ _)%pstring.
bluerock.lang.cpp.syntax.literal_string.Encoded.pstring_app_empty_l: ∀ s : Corelib.Strings.PrimString.string, "" ++ s = s
Stdlib.Strings.PString.cat_empty_r: ∀ s : Corelib.Strings.PrimString.string, s ++ "" = s
Stdlib.Strings.PString.cat_empty_l: ∀ s : Corelib.Strings.PrimString.string, "" ++ s = s
Stdlib.Strings.PString.cat_assoc: ∀ s1 s2 s3 : Corelib.Strings.PrimString.string, (s1 ++ s2) ++ s3 = s1 ++ s2 ++ s3
Stdlib.Strings.PString.split_cat_sub:
  ∀ (s : Corelib.Strings.PrimString.string) (len : Corelib.Numbers.Cyclic.Int63.PrimInt63.int),
    s =
    Corelib.Strings.PrimString.sub s 0x0 len ++
    Corelib.Strings.PrimString.sub s len (Corelib.Numbers.Cyclic.Int63.PrimInt63.sub (Corelib.Strings.PrimString.length s) len)
Stdlib.Strings.PString.of_list_app:
  ∀ l1 l2 : Corelib.Init.Datatypes.list Corelib.Strings.PrimString.char63,
    Corelib.Strings.PrimStringAxioms.of_list (l1 ++ l2) =
    Corelib.Strings.PrimStringAxioms.of_list l1 ++ Corelib.Strings.PrimStringAxioms.of_list l2
Stdlib.Strings.PString.cat_length_spec:
  ∀ s1 s2 : Corelib.Strings.PrimString.string,
    Corelib.Strings.PrimString.length (s1 ++ s2) =
    Stdlib.Numbers.Cyclic.Int63.Uint63.min Corelib.Strings.PrimString.max_length
      (Corelib.Numbers.Cyclic.Int63.PrimInt63.add (Corelib.Strings.PrimString.length s1) (Corelib.Strings.PrimString.length s2))
Stdlib.Strings.PString.cat_get_spec_l:
  ∀ (s1 s2 : Corelib.Strings.PrimString.string) (i : Corelib.Numbers.Cyclic.Int63.PrimInt63.int),
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z i <
     Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1))%Z
    → Corelib.Strings.PrimString.get (s1 ++ s2) i = Corelib.Strings.PrimString.get s1 i
Corelib.Strings.PrimStringAxioms.cat_spec:
  ∀ s1 s2 : Corelib.Strings.PrimString.string,
    Corelib.Strings.PrimStringAxioms.to_list (s1 ++ s2) =
    take (Corelib.BinNums.IntDef.Z.to_nat (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length))
      (Corelib.Strings.PrimStringAxioms.to_list s1 ++ Corelib.Strings.PrimStringAxioms.to_list s2)
Stdlib.Strings.PString.cat_length_spec_no_overflow:
  ∀ s1 s2 : Corelib.Strings.PrimString.string,
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1) +
     Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s2)
     ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length)%Z
    → Corelib.Strings.PrimString.length (s1 ++ s2) =
      Corelib.Numbers.Cyclic.Int63.PrimInt63.add (Corelib.Strings.PrimString.length s1) (Corelib.Strings.PrimString.length s2)
Stdlib.Strings.PString.to_list_cat:
  ∀ s1 s2 : Corelib.Strings.PrimString.string,
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1) +
     Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s2)
     ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length)%Z
    → Corelib.Strings.PrimStringAxioms.to_list (s1 ++ s2) =
      (Corelib.Strings.PrimStringAxioms.to_list s1 ++ Corelib.Strings.PrimStringAxioms.to_list s2)%list
Stdlib.Strings.PString.cat_spec_valid_length:
  ∀ s1 s2 : Corelib.Strings.PrimString.string,
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1) +
     Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s2)
     ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length)%Z
    → Corelib.Strings.PrimStringAxioms.to_list (s1 ++ s2) =
      (Corelib.Strings.PrimStringAxioms.to_list s1 ++ Corelib.Strings.PrimStringAxioms.to_list s2)%list
Stdlib.Strings.PString.cat_get_spec_r:
  ∀ (s1 s2 : Corelib.Strings.PrimString.string) (i : Corelib.Numbers.Cyclic.Int63.PrimInt63.int),
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1)
     ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z i)%Z
    → (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z i <
       Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length)%Z
      → Corelib.Strings.PrimString.get (s1 ++ s2) i =
        Corelib.Strings.PrimString.get s2 (Corelib.Numbers.Cyclic.Int63.PrimInt63.sub i (Corelib.Strings.PrimString.length s1))
bluerock.lang.cpp.syntax.literal_string.Encoded.to_N_app_l:
  ∀ (bpc : Corelib.Init.Datatypes.nat) (acc : Corelib.Numbers.BinNums.N) (offset : Corelib.Numbers.Cyclic.Int63.PrimInt63.int) 
    (s1 s2 : bluerock.lang.cpp.syntax.literal_string.Encoded.t),
    (0 ≤ bpc + Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z offset
     ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1))%Z
    → bluerock.lang.cpp.syntax.literal_string.Encoded.to_N bpc acc offset (s1 ++ s2) =
      bluerock.lang.cpp.syntax.literal_string.Encoded.to_N bpc acc offset s1
bluerock.lang.cpp.syntax.literal_string.Encoded.to_N_app_r:
  ∀ (bpc : Corelib.Init.Datatypes.nat) (acc : Corelib.Numbers.BinNums.N) (offset : Corelib.Numbers.Cyclic.Int63.PrimInt63.int) 
    (s1 s2 : bluerock.lang.cpp.syntax.literal_string.Encoded.t),
    (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1)
     ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z offset)%Z
    → (bpc + Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z offset <
       Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length)%Z
      → bluerock.lang.cpp.syntax.literal_string.Encoded.to_N bpc acc offset (s1 ++ s2) =
        bluerock.lang.cpp.syntax.literal_string.Encoded.to_N bpc acc
          (Corelib.Numbers.Cyclic.Int63.PrimInt63.sub offset (Corelib.Strings.PrimString.length s1)) s2
bluerock.lang.cpp.syntax.literal_string.Encoded.to_N_app:
  ∀ (bpc : Corelib.Init.Datatypes.nat) (acc : Corelib.Numbers.BinNums.N) (offset : Corelib.Numbers.Cyclic.Int63.PrimInt63.int) 
    (s1 s2 : bluerock.lang.cpp.syntax.literal_string.Encoded.t),
    (bpc + Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z offset <
     Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1))%Z
    → (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1) +
       Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s2)
       ≤ Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z Corelib.Strings.PrimString.max_length)%Z
      → bluerock.lang.cpp.syntax.literal_string.Encoded.to_N bpc acc offset (s1 ++ s2) =
        bluerock.lang.cpp.syntax.literal_string.Encoded.to_N
          (bpc - Stdlib.ZArith.BinInt.Z.to_nat (Corelib.Numbers.Cyclic.Int63.Uint63Axioms.to_Z (Corelib.Strings.PrimString.length s1)))
          (bluerock.lang.cpp.syntax.literal_string.Encoded.to_N bpc acc offset (s1 ++ s2))
          (Corelib.Numbers.Cyclic.Int63.PrimInt63.sub offset (Corelib.Strings.PrimString.length s1)) s2

>>> Search ([@_] _) in Corelib.Strings.PrimString.
Toplevel input, characters 10-11:
> Search ([@_] _) in Corelib.Strings.PrimString.
>           ^
Error: Syntax error: [global] or [pattern_ident] expected after '@' (in [term]).

## Assistant 33

I need to know the definitions of the helper types (ident, literal strings, operator enums, new_forms, etc.) before I can generate the full mutually‐recursive printers. Please dump those here:

```coqquery
Print bluerock.lang.cpp.syntax.preliminary.ident.
Print bluerock.lang.cpp.syntax.literal_string.literal_string.t.
Print bluerock.lang.cpp.syntax.core.new_form.
Print bluerock.lang.cpp.syntax.preliminary.MethodRef_.
Print bluerock.lang.cpp.syntax.preliminary.OverloadableOperator.
Print bluerock.lang.cpp.syntax.preliminary.operator_impl.t.
Print bluerock.lang.cpp.syntax.overloadable.RUnOp.
Print bluerock.lang.cpp.syntax.overloadable.RBinOp.
Print bluerock.lang.cpp.syntax.preliminary.UnOp.
Print bluerock.lang.cpp.syntax.preliminary.BinOp.
Print bluerock.prelude.arith.types.signed.
Print bluerock.lang.cpp.syntax.core.Cast.
```

## User 34

>>> Print bluerock.lang.cpp.syntax.preliminary.ident.
bluerock.lang.cpp.syntax.preliminary.ident = Corelib.Strings.PrimString.string
     : Set

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

>>> Print bluerock.lang.cpp.syntax.preliminary.operator_impl.t.
Variant t (obj_name type : Set) : Set :=
    Func : obj_name → type → bluerock.lang.cpp.syntax.preliminary.operator_impl.t obj_name type
  | MFunc : obj_name
            → bluerock.lang.cpp.syntax.preliminary.dispatch_type → type → bluerock.lang.cpp.syntax.preliminary.operator_impl.t obj_name type.

Arguments bluerock.lang.cpp.syntax.preliminary.operator_impl.t (obj_name type)%_type_scope
Arguments bluerock.lang.cpp.syntax.preliminary.operator_impl.Func {obj_name type}%_type_scope fn_name fn_type
Arguments bluerock.lang.cpp.syntax.preliminary.operator_impl.MFunc {obj_name type}%_type_scope fn_name _ fn_type

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

>>> Print bluerock.prelude.arith.types.signed.
Variant signed : Set :=  Signed : bluerock.prelude.arith.types.signed | Unsigned : bluerock.prelude.arith.types.signed.

>>> Print bluerock.lang.cpp.syntax.core.Cast.
Notation Cast := bluerock.lang.cpp.syntax.core.Cast'

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

## Assistant 34

Below is a minimal “scaffold” showing one big mutually‐recursive definition that covers all of

   name, temp_arg, type, Expr, Stmt, VarDecl, BindingDecl and Cast

and which you can now refine case‐by‐case.  Right now each branch just returns a placeholder string (`"<...>"`), but the recursion is properly wired up so it type‐checks and you can incrementally replace the `"<...>"` by proper `++`-ed `PrimString.string` fragments.  

Note that you may want to open the `pstring_scope` so that `""` is a `PrimString.string` and `++` is its `cat`.

```gallina
Local Open Scope pstring_scope.

Fixpoint pprint_name (n: bluerock.lang.cpp.syntax.core.name') : Corelib.Strings.PrimString.string :=
  "<name>"

with pprint_temp_arg (ta: bluerock.lang.cpp.syntax.core.temp_arg') : Corelib.Strings.PrimString.string :=
  "<temp_arg>"

with pprint_type (ty: bluerock.lang.cpp.syntax.core.type') : Corelib.Strings.PrimString.string :=
  "<type>"

with pprint_expr (e: bluerock.lang.cpp.syntax.core.Expr') : Corelib.Strings.PrimString.string :=
  "<expr>"

with pprint_stmt (s: bluerock.lang.cpp.syntax.core.Stmt') : Corelib.Strings.PrimString.string :=
  "<stmt>"

with pprint_vardecl (d: bluerock.lang.cpp.syntax.core.VarDecl') : Corelib.Strings.PrimString.string :=
  "<vardecl>"

with pprint_bindingdecl (b: bluerock.lang.cpp.syntax.core.BindingDecl') : Corelib.Strings.PrimString.string :=
  "<bindingdecl>"

with pprint_cast (c: bluerock.lang.cpp.syntax.core.Cast') : Corelib.Strings.PrimString.string :=
  "<cast>".

(* You can now refine each placeholder, e.g.: *)

(*
Fixpoint pprint_name (n: name') : string :=
  match n with
  | Ninst base args =>
      pprint_name base ++ "<" ++ pprint_list pprint_temp_arg "," args ++ ">"
  | Nglobal a      => pprint_atomic_name a
  | Ndependent ty  => "decltype(" ++ pprint_type ty ++ ")"
  | Nscoped n' a   => pprint_name n' ++ "::" ++ pprint_atomic_name a
  | Nunsupported s => s
  end
with ...
*)

(* Helper for printing lists, options, etc. *)
Fixpoint pprint_list {A}
  (f : A -> Corelib.Strings.PrimString.string)
  (sep : Corelib.Strings.PrimString.string)
  (l : Corelib.Init.Datatypes.list A)
  : Corelib.Strings.PrimString.string :=
  match l with
  | [] => ""
  | x :: xs =>
     f x ++
     match xs with
     | [] => ""
     | _  => sep ++ pprint_list f sep xs
     end
  end.

Definition pprint_option {A}
  (f : A -> Corelib.Strings.PrimString.string)
  (o : Corelib.Init.Datatypes.option A)
  : Corelib.Strings.PrimString.string :=
  match o with
  | Corelib.Init.Datatypes.None   => ""
  | Corelib.Init.Datatypes.Some x => f x
  end.
```

