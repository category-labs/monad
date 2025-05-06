## User 1

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
bluerock.lang.cpp.syntax.stmt.Stmt is defined mutually Inductively with many other types like Expr.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be bluerock.lang.cpp.syntax.stmt.Stmt -> PrimString.string.
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


## User 2

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
bluerock.lang.cpp.syntax.stmt.Stmt is defined mutually Inductively with many other types like Expr.
As a part of this job, you need to write pretty printers for them as well, likely together using mutual recursion.
The type of the printer should be bluerock.lang.cpp.syntax.stmt.Stmt -> PrimString.string.
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


## Assistant 1

I need to see the exact constructors of `bluerock.lang.cpp.syntax.stmt.Stmt` (and its mutually‐defined companions) so that I can write a matching `PrimString.string` printer. None of your prior queries have dumped its definition, so let’s inspect it directly:

```coqquery
Print bluerock.lang.cpp.syntax.stmt.Stmt.
```

## User 3

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

## Assistant 2

To build a pretty‐printer returning `PrimString.string`, I first need to know what constructors and operations (e.g. literal‐to‐`PrimString`, append, etc.) the `PrimString` module exposes.  Once I see those, I can write mutually recursive `pp_…` functions (for `name`, `type`, `Expr`, `Stmt` etc.) that assemble `PrimString.string` via those primitives.

```coqquery
Search PrimString.
```

## User 4

Toplevel input, characters 7-17:
> Search PrimString.
>        ^^^^^^^^^^
Error: The reference PrimString was not found in the current environment.

## Assistant 3

I need to know what constructors and combinators (e.g. empty string, append, of-Z, of-bool, etc.) are provided for `PrimString.string` so I can assemble my pretty‐printer output. Since nothing is in scope yet, let’s import the core primitive‐string library and list all definitions returning `PrimString.string`:

```coqquery
Require Import Coq.Strings.PrimString.
Search (_ : PrimString.string).
```

## User 5

That query has no errors but returned an empty result. For `Search` queries, this means nothing in the current context matches the search criteria. Before assuming non-existence of what you are looking for, try relaxing some constraints. Consider the possiblity of the arugment order being different, or the names being different: toString vs to_string vs print vs showString: make most minimal assumptions about how stuff is named

## Assistant 4

I need the basic conversion and concatenation functions into `PrimString.string` (e.g. of‐Z, of‐bool, append, empty) so I can build up larger printed pieces. To discover all such API functions, let’s search for anything returning `PrimString.string`:

```coqquery
Search (_ -> PrimString.string).
```

## User 6

own_frac_auth_both_includedI_total:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : cmra} {HasOwn0 : HasOwn PROP (frac_auth.frac_authR A)},
            HasOwnValid PROP (frac_auth.frac_authR A)
            → CmraTotal A
              → ∀ (g : gname) (q1 q2 : Qp) (a b : A),
                  Observe2 (includedI.includedI b a) (own g (frac_auth.frac_auth_auth_frac q1 a)) (own g (frac_auth.frac_auth_frag q2 b))
wp_block_shift:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (tu : translation_unit) (ρ : region) 
    (ds : list Stmt) (Q : Kpred), (|={⊤}=> wp_block tu ρ ds (|={⊤}=> Q)) ⊢ wp_block tu ρ ds Q
has_type.svalid_members_aligned_ofR_this_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (p : ptr) (cls : globname) 
    (members : list (field_name * type)),
    CancelX MatchNormal [p |-> svalid_members cls members] [tele] CoverAny [p |-> aligned_ofR (Tnamed cls)]
TM.Raw.Proofs.remove_min_mapsto:
  ∀ [elt : Type] (l : TM.Raw.t elt) (x : TM.Raw.key) (e : elt) (r : TM.Raw.t elt) (h : Int.Z_as_Int.t) (y : TM.Raw.key) (e' : elt),
    TM.Raw.MapsTo y e' (TM.Raw.Node l x e r h)
    ↔ (λ x0 y0 : TM.Compare.t, namemap.TM.Compare.compare x0 y0 = Eq) y (TM.Raw.remove_min l x e r).2.1
      ∧ e' = (TM.Raw.remove_min l x e r).2.2 ∨ TM.Raw.MapsTo y e' (TM.Raw.remove_min l x e r).1
map_empty_equiv_eq:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} {H7 : Equiv A} (m : M A), m ≡ ∅ ↔ m = ∅
insert_idN:
  ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : ofe} (n : nat) (m : gmap K A) (i : K) (x : A),
    m !! i ≡{n}≡ Some x → <[i:=x]> m ≡{n}≡ m
big_sepL_sepM:
  ∀ {PROP : bi} {A K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {B : Type} (Φ : nat → A → K → B → PROP) 
    (l1 : list A) (m2 : gmap K B),
    ([∗ list] k1↦x1 ∈ l1, [∗ map] k2↦x2 ∈ m2, Φ k1 x1 k2 x2) ⊣⊢ ([∗ map] k2↦x2 ∈ m2, [∗ list] k1↦x1 ∈ l1, Φ k1 x1 k2 x2)
big_sepMS_delete:
  ∀ {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → PROP) (X : gmultiset A) (x : A),
    x ∈ X → ([∗ mset] y ∈ X, Φ y) ⊣⊢ Φ x ∗ ([∗ mset] y ∈ (X ∖ {[+ x +]}), Φ y)
internal.NameMap.Raw.Proofs.remove_min_mapsto:
  ∀ [elt : Type] (l : TM.Raw.t elt) (x : internal.NameMap.Raw.key) (e : elt) (r : TM.Raw.t elt) (h : Int.Z_as_Int.t) 
    (y : internal.NameMap.Raw.key) (e' : elt),
    internal.NameMap.Raw.MapsTo y e' (internal.NameMap.Raw.Node l x e r h)
    ↔ (λ x0 y0 : internal.NameMap.Compare.t, namemap.internal.NameMap.Compare.compare x0 y0 = Eq) y
        (internal.NameMap.Raw.remove_min l x e r).2.1
      ∧ e' = (internal.NameMap.Raw.remove_min l x e r).2.2 ∨ internal.NameMap.Raw.MapsTo y e' (internal.NameMap.Raw.remove_min l x e r).1
big_sepM_sepL:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type} (Φ : K → A → nat → B → PROP) 
    (m1 : gmap K A) (l2 : list B),
    ([∗ map] k1↦x1 ∈ m1, [∗ list] k2↦x2 ∈ l2, Φ k1 x1 k2 x2) ⊣⊢ ([∗ list] k2↦x2 ∈ l2, [∗ map] k1↦x1 ∈ m1, Φ k1 x1 k2 x2)
map_compose_empty_r:
  ∀ {A : Type} {MA : Type → Type} {H : FMap MA} {H0 : ∀ A0 : Type, Lookup A A0 (MA A0)} {H1 : ∀ A0 : Type, Empty (MA A0)} 
    {H2 : ∀ A0 : Type, PartialAlter A A0 (MA A0)} {H3 : OMap MA} {H4 : Merge MA} {H5 : ∀ A0 : Type, MapFold A A0 (MA A0)} 
    {EqDecision0 : EqDecision A},
    FinMap A MA → ∀ {B : Type} {MB : Type → Type} {H8 : ∀ A0 : Type, Lookup B A0 (MB A0)} {C : Type} (m : MB C), m ∘ₘ ∅ = ∅
set_map_alt:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ {B D : Type} {H7 : ElemOf B D} {H8 : Empty D} {H9 : Singleton B D} {H10 : Union D},
        SemiSet B D → ∀ (f : A → B) (X : C), set_map f X = set_omap (λ x : A, Some (f x)) X
big_sepM_mono:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} (Φ Ψ : K → A → PROP) (m : gmap K A),
    (∀ (k : K) (x : A), m !! k = Some x → Φ k x ⊢ Ψ k x) → ([∗ map] k↦x ∈ m, Φ k x) ⊢ [∗ map] k↦x ∈ m, Ψ k x
Kloop_frame:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} (I1 I2 : mpred) (k1 k2 : Kpred) (rt : ReturnType),
    <affine> (I1 -∗ I2) ⊢ <affine> (∀ rt0 : ReturnType, k1 rt0 -∗ k2 rt0) -∗ wp.Kloop I1 k1 rt -∗ wp.Kloop I2 k2 rt
commit_acc_intro:
  ∀ {PROP : bi} {H : BiFUpd PROP} {TA TB : tele} (b : bool) (Eo Ei : coPset) (α : TA → PROP) (β Φ : TA → TB → PROP),
    Ei ⊆ Eo → ⊢ ∀.. x : TA, α x -∗ ▷?b (∀.. y : TB, β x y ={Eo}=∗ Φ x y) -∗ commit_acc b Eo Ei α β Φ
SDestructor_flip_mono':
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {cc : calling_conv} (class : globname),
    Proper (pointwise_relation ptr (wpspec_relation bi_entails) --> flip fs_entails) (SDestructor class)
mapset_set:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → Set_ K (mapset M)
operators.wp_eval_binop_pure_signed:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (bo : BinOp) (ty1 ty2 ty3 : type) (av bv : val) (result : Z) (Q : val → mpredI) {v : Z},
    Simplify result v
    → (valid<ty1> av → valid<ty2> bv → valid<ty3> result → eval_binop_pure tu bo ty1 ty2 ty3 av bv result)
      → [| valid<ty3> v |] ∗ Q v ⊢ operators.wp_eval_binop.body tu bo ty1 ty2 ty3 av bv Q
foldr_op_index_shift:
  ∀ (shift : Z → Z) (la : list N) (n m : nat) (f : nat * N → Z → Z),
    0%Z = shift 0%Z
    → (∀ (idx : nat) (elm : N) (acc : Z), shift (f (idx, elm) acc) = f (idx + n, elm) (shift acc))
      → foldr f 0%Z (zip (seq (m + n) (base.length la)) la) = shift (foldr f 0%Z (zip (seq m (base.length la)) la))
_at_big_sepL:
  ∀ {thread_info : biIndex} {Σ : gFunctors} {cpp_logic0 : cpp_logic thread_info Σ} (A : Type) (p : ptr) (xs : list A) (Φ : nat → A → Rep),
    p |-> ([∗ list] i↦x ∈ xs, Φ i x) ⊣⊢ ([∗ list] i↦x ∈ xs, p |-> Φ i x)
Decimal.uint_rec:
  ∀ P : Decimal.uint → Set,
    P Decimal.Nil
    → (∀ u : Decimal.uint, P u → P (Decimal.D0 u))
      → (∀ u : Decimal.uint, P u → P (Decimal.D1 u))
        → (∀ u : Decimal.uint, P u → P (Decimal.D2 u))
          → (∀ u : Decimal.uint, P u → P (Decimal.D3 u))
            → (∀ u : Decimal.uint, P u → P (Decimal.D4 u))
              → (∀ u : Decimal.uint, P u → P (Decimal.D5 u))
                → (∀ u : Decimal.uint, P u → P (Decimal.D6 u))
                  → (∀ u : Decimal.uint, P u → P (Decimal.D7 u))
                    → (∀ u : Decimal.uint, P u → P (Decimal.D8 u)) → (∀ u : Decimal.uint, P u → P (Decimal.D9 u)) → ∀ u : Decimal.uint, P u
Decimal.uint_ind:
  ∀ P : Decimal.uint → Prop,
    P Decimal.Nil
    → (∀ u : Decimal.uint, P u → P (Decimal.D0 u))
      → (∀ u : Decimal.uint, P u → P (Decimal.D1 u))
        → (∀ u : Decimal.uint, P u → P (Decimal.D2 u))
          → (∀ u : Decimal.uint, P u → P (Decimal.D3 u))
            → (∀ u : Decimal.uint, P u → P (Decimal.D4 u))
              → (∀ u : Decimal.uint, P u → P (Decimal.D5 u))
                → (∀ u : Decimal.uint, P u → P (Decimal.D6 u))
                  → (∀ u : Decimal.uint, P u → P (Decimal.D7 u))
                    → (∀ u : Decimal.uint, P u → P (Decimal.D8 u)) → (∀ u : Decimal.uint, P u → P (Decimal.D9 u)) → ∀ u : Decimal.uint, P u
na_inv_objective_with:
  ∀ {K J : biIndex} {Σ : gFunctors} {invGS0 : invGS Σ} {na_invG0 : na_invG Σ} (L : mlens.MLens K J) (p : na_inv_pool_name) 
    (N : namespace) (P : K -mon> iPropI Σ), tls_modalities.ObjectiveWith L P → tls_modalities.ObjectiveWith L (na_inv p N P)
Decimal.uint_sind:
  ∀ P : Decimal.uint → SProp,
    P Decimal.Nil
    → (∀ u : Decimal.uint, P u → P (Decimal.D0 u))
      → (∀ u : Decimal.uint, P u → P (Decimal.D1 u))
        → (∀ u : Decimal.uint, P u → P (Decimal.D2 u))
          → (∀ u : Decimal.uint, P u → P (Decimal.D3 u))
            → (∀ u : Decimal.uint, P u → P (Decimal.D4 u))
              → (∀ u : Decimal.uint, P u → P (Decimal.D5 u))
                → (∀ u : Decimal.uint, P u → P (Decimal.D6 u))
                  → (∀ u : Decimal.uint, P u → P (Decimal.D7 u))
                    → (∀ u : Decimal.uint, P u → P (Decimal.D8 u)) → (∀ u : Decimal.uint, P u → P (Decimal.D9 u)) → ∀ u : Decimal.uint, P u
own_excl_auth_frac_agree:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {HasOwn0 : HasOwn PROP (excl_authR A)},
            HasOwnValid PROP (excl_authR A)
            → ∀ (g : gname) (q1 q2 : Qp) (a1 a2 : A),
                Discrete a1 → Observe2 [| a1 ≡ a2 |] (own g (excl_auth.excl_auth_frac q1 a1)) (own g (excl_auth.excl_auth_frac q2 a2))
has_type.svalid_members_has_type_ptr_this_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (p : ptr) (cls : globname) 
    (members : list (field_name * type)),
    CancelX MatchNormal [p |-> svalid_members cls members] [tele] CoverAny [(validP<Tptr (Tnamed cls)> (Vptr p))%I]
map_disjoint_difference_r:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 m3 : M A), m3 ⊆ m2 → m3 ##ₘ m1 ∖ m2
big_sepS_insert_2':
  ∀ {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} {Φ : A → PROP} {X : gset A} (x : A),
    TCOr (Affine (Φ x)) (Absorbing (Φ x)) → Φ x -∗ ([∗ set] y ∈ X, Φ y) -∗ [∗ set] y ∈ (X ∪ {[x]}), Φ y
Decimal.uint_rect:
  ∀ P : Decimal.uint → Type,
    P Decimal.Nil
    → (∀ u : Decimal.uint, P u → P (Decimal.D0 u))
      → (∀ u : Decimal.uint, P u → P (Decimal.D1 u))
        → (∀ u : Decimal.uint, P u → P (Decimal.D2 u))
          → (∀ u : Decimal.uint, P u → P (Decimal.D3 u))
            → (∀ u : Decimal.uint, P u → P (Decimal.D4 u))
              → (∀ u : Decimal.uint, P u → P (Decimal.D5 u))
                → (∀ u : Decimal.uint, P u → P (Decimal.D6 u))
                  → (∀ u : Decimal.uint, P u → P (Decimal.D7 u))
                    → (∀ u : Decimal.uint, P u → P (Decimal.D8 u)) → (∀ u : Decimal.uint, P u → P (Decimal.D9 u)) → ∀ u : Decimal.uint, P u
own_excl_auth_agree:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {HasOwn0 : HasOwn PROP (excl_authR A)},
            HasOwnValid PROP (excl_authR A)
            → ∀ (g : gname) (q : Qp) (a b : A), Discrete a → Observe2 [| a ≡ b |] (own g (excl_auth.excl_auth_frac q a)) (own g (◯E b))
big_sepL2_intro:
  ∀ {PROP : bi} {A B : Type} (Φ : nat → A → B → PROP) (l1 : list A) (l2 : list B),
    base.length l1 = base.length l2
    → □ (∀ (k : nat) (x1 : A) (x2 : B), ⌜l1 !! k = Some x1⌝ → ⌜l2 !! k = Some x2⌝ → Φ k x1 x2) ⊢ [∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2
map_union_difference:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 : M A), (m1 ∪ m2) ∖ m1 = m2 ∖ m1
cast.wp_lval_lval_cast_noop:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (ρ : region) (ty : type) (e : Expr) (Q : ptr → FreeTemps → epred),
    cast.is_noop_cast_vc (valcat_of e) Lvalue (type_of e) ty =[Vm?]=> Some true → ::wpL ρ e ⊢ ::wpL ρ (Ecast (Cnoop (Tref ty)) e)
cast.wp_xval_xval_cast_noop:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (ρ : region) (ty : type) (e : Expr) (Q : ptr → FreeTemps → epred),
    cast.is_noop_cast_vc (valcat_of e) Xvalue (type_of e) ty =[Vm?]=> Some true → ::wpX ρ e ⊢ ::wpX ρ (Ecast (Cnoop (Trv_ref ty)) e)
map_disjoint_difference_l:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 m3 : M A), m3 ⊆ m2 → m1 ∖ m2 ##ₘ m3
big_sepS_delete:
  ∀ {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → PROP) (X : gset A) (x : A),
    x ∈ X → ([∗ set] y ∈ X, Φ y) ⊣⊢ Φ x ∗ ([∗ set] y ∈ (X ∖ {[x]}), Φ y)
big_andM_mono:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} (Φ Ψ : K → A → PROP) (m : gmap K A),
    (∀ (k : K) (x : A), m !! k = Some x → Φ k x ⊢ Ψ k x) → ([∧ map] k↦x ∈ m, Φ k x) ⊢ [∧ map] k↦x ∈ m, Ψ k x
alignment.svalid_members_aligned_of_this_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (p : ptr) (cls : globname) 
    (members : list (field_name * type)),
    CancelX MatchNormal [p |-> svalid_members cls members] [tele] CoverAny [p |-> aligned_ofR (Tnamed cls)]
NM.Raw.Proofs.remove_min_mapsto:
  ∀ [elt : Type] (l : TM.Raw.t elt) (x : NM.Raw.key) (e : elt) (r : TM.Raw.t elt) (h : Int.Z_as_Int.t) (y : NM.Raw.key) (e' : elt),
    NM.Raw.MapsTo y e' (NM.Raw.Node l x e r h)
    ↔ (λ x0 y0 : NM.Compare.t, namemap.NM.Compare.compare x0 y0 = Eq) y (NM.Raw.remove_min l x e r).2.1
      ∧ e' = (NM.Raw.remove_min l x e r).2.2 ∨ NM.Raw.MapsTo y e' (NM.Raw.remove_min l x e r).1
coq_tactics.tac_intuitionistic:
  ∀ {PROP : bi} (Δ : environments.envs PROP) (i j : base.ident.ident) (p : bool) (P P' Q : PROP),
    environments.envs_lookup i Δ = Some (p, P)
    → IntoPersistent p P P'
      → (if p then TCTrue else TCOr (Affine P) (Absorbing Q))
        → match environments.envs_replace i p true (environments.Esnoc  j P') Δ with
          | Some Δ' => environments.envs_entails Δ' Q
          | None => False
          end → environments.envs_entails Δ Q
view_both_core_frac: ∀ {A : ofe} {B : ucmra} (rel : view_rel A B) (q : Qp) (a : A) (b : B), core (●V{#q} a ⋅ ◯V b) ≡ ◯V core b
branch.stmt.unlock:
  @branch.stmt =
  λ (thread_info : biIndex) (_Σ : gFunctors) (Σ : cpp_logic thread_info _Σ) (σ : genv) (tu : translation_unit) (ρ : region) 
    (b : bool) (thn els : Stmt) (Q : Kpred), (([| b |] -∗ ::wpS ρ thn) ∧ ([| ~~ b |] -∗ ::wpS ρ els))%I
elaborate_add_pre:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (ret : type) (ts : list type) 
    (ar : function_arity) (args : list val) (R : mpredI) (P : WpSpec mpredI val val) (Q : list ptr) (args' : ptr → mpredI),
    elaborate ret ts ar args (add_pre R P) Q args' ⊣⊢ R ∗ elaborate ret ts ar args P Q args'
operators.wp_eval_div_int:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (av bv : Z) (Q : val → mpredI),
    [| bv ≠ 0%Z |] ∗ [| bitsize.bound (int_rank.bitsize int_rank.Iint) Signed (av `quot` bv) |] ∗ Q (av `quot` bv)%Z
    ⊢ operators.wp_eval_binop.body tu Bdiv "int" "int" "int" av bv Q
ssrbool.on1lS:
  ∀ {T1 T2 T3 : ssrbool.predArgType} (D2 : ssrbool.pred_sort (ssrbool.predPredType T2)) {f : T1 → T2} {h : T3} {Q1l : 
                                                                                                               (T1 → T2) → 
                                                                                                               T3 → T1 → Prop},
    (∀ x : T1, Datatypes.is_true (ssrbool.in_mem (f x) (ssrbool.mem D2)))
    → ssrbool.prop_on1 (ssrbool.mem D2) (f:=f) (Pf:=λ (f'' : T1 → T2) (h' : T3), ∀ x : T1, Q1l f'' h' x : Prop) (P:=
        Q1l f h) (Phantom (T3 → Prop) ((λ (f'' : T1 → T2) (h' : T3), ∀ x : T1, Q1l f'' h' x : Prop) f))
        (ssrbool.onPhantom ((λ (f'' : T1 → T2) (h' : T3), ∀ x : T1, Q1l f'' h' x : Prop) f) h)
      → (λ (f'' : T1 → T2) (h' : T3), ∀ x : T1, Q1l f'' h' x : Prop) f h
operators.wp_eval_div_long:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (av bv : Z) (Q : val → mpredI),
    [| bv ≠ 0%Z |] ∗ [| bitsize.bound (int_rank.bitsize int_rank.Ilong) Signed (av `quot` bv) |] ∗ Q (av `quot` bv)%Z
    ⊢ operators.wp_eval_binop.body tu Bdiv "long" "long" "long" av bv Q
big_sepM2_fmap:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B A' B' : Type} (f : A → A') (g : B → B') 
    (Φ : K → A' → B' → PROP) (m1 : gmap K A) (m2 : gmap K B),
    ([∗ map] k↦y1;y2 ∈ (f <$> m1);(g <$> m2), Φ k y1 y2) ⊣⊢ ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k (f y1) (g y2))
elem_of_map_2_alt:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ {B D : Type} {H7 : ElemOf B D} {H8 : Empty D} {H9 : Singleton B D} {H10 : Union D},
        SemiSet B D → ∀ (f : A → B) (X : C) (x : A) (y : B), x ∈ X → y = f x → y ∈ set_map f X
map_subseteq_inv:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 : M A), m1 ⊆ m2 → m1 ⊂ m2 ∨ m1 = m2
auth_both_validN: ∀ {A : ucmra} (n : nat) (a b : A), ✓{n} (● a ⋅ ◯ b) ↔ b ≼{n} a ∧ ✓{n} a
big_sepM2_pure_1:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type} (φ : K → A → B → Prop) (m1 : gmap K A) 
    (m2 : gmap K B),
    ([∗ map] k↦y1;y2 ∈ m1;m2, ⌜φ k y1 y2⌝) ⊢ ⌜∀ (k : K) (y1 : A) (y2 : B), m1 !! k = Some y1 → m2 !! k = Some y2 → φ k y1 y2⌝
wp_const_enum_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (nm : name) (tu0 : translation_unit) 
    (from to : cQp.t) (p : ptr) (v : val) (Q : mpredI),
    CancelX MatchNormal [p |-> primR (Tenum nm) from v] [tele] CoverAny [wp_const tu0 from to p (Tenum nm) Q]
destroy_val_intro_val:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (tu : translation_unit) (ty : type) 
    (this : ptr) (Q : epred),
    is_value_type ty
    → let cv := qual_norm (λ (cv : type_qualifiers) (_ : type), cv) ty in
      (∃ v : val, this |-> tptstoR (erase_qualifiers ty) (cQp.mk (q_const cv) 1) v) ∗ Q ⊢ destroy_val tu ty this Q
big_sepL2_closed:
  ∀ {PROP : bi} {A B : Type} (P : PROP → Prop) (Φ : nat → A → B → PROP) (l1 : list A) (l2 : list B),
    P emp%I
    → P False%I
      → (∀ Q1 Q2 : PROP, P Q1 → P Q2 → P (Q1 ∗ Q2)%I)
        → (∀ (k : nat) (x1 : A) (x2 : B), l1 !! k = Some x1 → l2 !! k = Some x2 → P (Φ k x1 x2)) → P ([∗ list] k↦x1;x2 ∈ l1;l2, Φ k x1 x2)%I
arrayR_proper_ho.arrayR_proper_ho:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {T : Type} {H : Equiv T} (t : type),
    Proper ((equiv ==> equiv) ==> equiv ==> equiv) (arrayR t)
elem_of_fmap:
  ∀ {M : Type → Type} {H : ∀ A : Type, ElemOf A (M A)} {H0 : ∀ A : Type, Empty (M A)} {H1 : ∀ A : Type, Singleton A (M A)} 
    {H2 : ∀ A : Type, Union (M A)} {MBind0 : MBind M} {MRet0 : MRet M} {FMap0 : FMap M} {MJoin0 : MJoin M},
    MonadSet M → ∀ {A B : Type} (f : A → B) (X : M A) (x : B), x ∈ f <$> X ↔ ∃ y : A, x = f y ∧ y ∈ X
wp_const_float_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (sz : float_type.t) (tu0 : translation_unit) 
    (from to : cQp.t) (p : ptr) (v : val) (Q : mpredI),
    CancelX MatchNormal [p |-> primR (Tfloat_ sz) from v] [tele] CoverAny [wp_const tu0 from to p (Tfloat_ sz) Q]
wp_spec_bind_ne: ∀ {PROP : bi} {ARG ARG' RESULT RESULT' : Type} (n : nat), Proper (dist n ==> eq ==> eq ==> dist n) wp_spec_bind
arrayR_flip_mono:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {X : Type} (ty : type),
    Proper (pointwise_relation X (flip bi_entails) ==> eq ==> flip bi_entails) (arrayR ty)
operators.wp_eval_div_longlong:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (av bv : Z) (Q : val → mpredI),
    [| bv ≠ 0%Z |] ∗ [| bitsize.bound (int_rank.bitsize int_rank.Ilonglong) Signed (av `quot` bv) |] ∗ Q (av `quot` bv)%Z
    ⊢ operators.wp_eval_binop.body tu Bdiv "long long" "long long" "long long" av bv Q
class_instances_updates.from_forall_step_fupd:
  ∀ {PROP : bi} {BiFUpd0 : BiFUpd PROP} {BiPlainly0 : BiPlainly PROP},
    BiFUpdPlainly PROP
    → ∀ (E1 E2 : coPset) {A : Type} (P : PROP) (Φ : A → PROP) (name : ident_name),
        TCOr (TCEq E1 E2) (TCOr (TCEq E1 ⊤) (TCEq E2 ∅))
        → FromForall P Φ name → (∀ x : A, Plain (Φ x)) → FromForall (|={E1}[E2]▷=> P) (λ a : A, (|={E1}[E2]▷=> Φ a)%I) name
auth_auth_includedN: ∀ {A : ucmra} (n : nat) (a1 a2 b : A), ● a1 ≼{n} ● a2 ⋅ ◯ b ↔ a1 ≡{n}≡ a2
App.part_def:
  ∀ {A : Type},
    list A * list A → restrict.wrapper App (prodR (optionR (exclR (leibnizO (list A)))) (optionR (exclR (leibnizO (list A * list A)))))
ssrbool.in3_sig:
  ∀ {T1 T2 T3 : Type} {D1 : ssrbool.pred_sort (ssrbool.predPredType T1)} {D2 : ssrbool.pred_sort (ssrbool.predPredType T2)} 
    {D3 : ssrbool.pred_sort (ssrbool.predPredType T3)} {P3 : T1 → T2 → T3 → Prop},
    ssrbool.prop_in111 (ssrbool.mem D1) (ssrbool.mem D2) (ssrbool.mem D3) (P:=P3)
      (ssrbool.inPhantom (∀ (x : T1) (y : T2) (z : T3), P3 x y z : Prop))
    → ∀ (x : {x : T1 | Datatypes.is_true (D1 x)}) (y : {x0 : T2 | Datatypes.is_true (D2 x0)}) (z : {x0 : T3 | Datatypes.is_true (D3 x0)}),
        P3 (`x) (`y) (`z)
parray.PArray.get_of_list_aux:
  ∀ {A : Type} {j : PrimInt63.int} (l : list A) (a : PrimArray.array A) (i : PrimInt63.int),
    (base.length l ≤ Uint63Axioms.to_Z (PrimArray.length a))%Z
    → (Uint63Axioms.to_Z i + base.length l ≤ Uint63Axioms.to_Z (PrimArray.length a))%Z
      → PrimArray.get (parray.PArray.of_list_aux l i a) j =
        (if PrimInt63.leb i j && PrimInt63.ltb j (PrimInt63.add i (Uint63Axioms.of_Z (base.length l)))
         then nth (Z.to_nat (Uint63Axioms.to_Z j) - Z.to_nat (Uint63Axioms.to_Z i)) l (PrimArray.get a j)
         else PrimArray.get a j)
PEadd_ext:
  ∀ [R : Type] [rO rI : R] [radd rmul rsub : R → R → R] [ropp : R → R] [req : R → R → Prop],
    Equivalence req
    → ring_eq_ext radd rmul ropp req
      → ∀ [C : Type] [phi : C → R] [Cpow : Type] [Cp_phi : N → Cpow] [rpow : R → Cpow → R],
          Proper
            (NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow ==>
             NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow ==> NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow)
            (Ring_polynom.PEadd (C:=C))
partial_alter_self_alt:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K},
    FinMap K M → ∀ {A : Type} (m : M A) (i : K) (x : option A), x = m !! i → partial_alter (λ _ : option A, x) i m = m
prepost_loops.wp_do_inv:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (tu : translation_unit) (inv : region → mpredI) 
    (P : mpredI) (Q : Kpred) (t : Expr) (b : Stmt) (ρ : region), (P ⊢ inv ρ ∗ gather_all.Spatial.gather) → P ⊢ ::wpS ρ (Sdo b t)
App.part:
  ∀ {A : Type},
    list A * list A → restrict.wrapper App (prodR (optionR (exclR (leibnizO (list A)))) (optionR (exclR (leibnizO (list A * list A)))))
PEmul_ext:
  ∀ [R : Type] [rO rI : R] [radd rmul rsub : R → R → R] [ropp : R → R] [req : R → R → Prop],
    Equivalence req
    → ring_eq_ext radd rmul ropp req
      → ∀ [C : Type] [phi : C → R] [Cpow : Type] [Cp_phi : N → Cpow] [rpow : R → Cpow → R],
          Proper
            (NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow ==>
             NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow ==> NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow)
            (Ring_polynom.PEmul (C:=C))
ssrbool.in_onW_can:
  ∀ {aT rT : ssrbool.predArgType} (aD : ssrbool.pred_sort (ssrbool.predPredType aT)) (rD : ssrbool.pred_sort (ssrbool.predPredType rT)) 
    {f : aT → rT} {g : rT → aT},
    ssrfun.cancel g f
    → ssrbool.prop_in1 (ssrbool.mem rD)
        (P:=λ x : rT, Datatypes.is_true (ssrbool.in_mem (g x) (ssrbool.mem aD)) → (λ x0 : rT, f (g x0) = x0) x)
        (ssrbool.inPhantom
           (ssrbool.prop_on1 (ssrbool.mem aD) (f:=g) (Pf:=ssrfun.cancel (aT:=rT)) (P:=λ x : rT, f (g x) = x)
              (Phantom ((aT → rT) → Prop) (ssrfun.cancel g)) (ssrbool.onPhantom (ssrfun.cancel g) f)))
own_agree_L:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {HasOwn0 : HasOwn PROP (agreeR A)},
            HasOwnValid PROP (agreeR A)
            → LeibnizEquiv A → ∀ (g : gname) (a b : A), Discrete a → Observe2 [| a = b |] (own g (to_agree a)) (own g (to_agree b))
algebra.discrete_fun_includedI_spec:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : Type} {B : A → ucmra} {EqDecision0 : EqDecision A},
            Finite A → ∀ f g : discrete_fun (λ x : A, B x), includedI.includedI f g ⊣⊢ ∀ x : A, includedI.includedI (f x) (g x)
map_subseteq_difference_l:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 m : M A), m1 ⊆ m → m1 ∖ m2 ⊆ m
own_alloc_cofinite_dep:
  ∀ {PROP : bi} {BiBUpd0 : BiBUpd PROP} {A : cmra} {HasOwn0 : HasOwn PROP A},
    HasOwnUpd PROP A → ∀ (f : gname → A) (G : gset gname), (∀ γ : gname, γ ∉ G → ✓ f γ) → ⊢ |==> ∃ γ : gname, <affine> ⌜γ ∉ G⌝ ∗ own γ (f γ)
merge_empty:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A B C : Type} (f : option A → option B → option C), merge f ∅ ∅ = ∅
filter_empty_not_elem_of_L:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C → ∀ (P : A → Prop) {H7 : ∀ x : A, Decision (P x)}, LeibnizEquiv C → ∀ (X : C) (x : A), filter P X = ∅ → P x → x ∉ X
auth_update_alloc: ∀ {A : ucmra} (a a' b' : A), (a, ε) ~l~> (a', b') → ● a ~~> ● a' ⋅ ◯ b'
wp_operand_cast_builtin2fun_cpp:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (ρ : region) (cc : calling_conv) (ar : function_arity) (ret : type) (args : list type) (g : name) (Q : val → FreeTemps → epred),
    let ty := Tfunction (FunctionType ret args) in let e := Eglobal g ty in ::wpL ρ e ⊢ ::wpOperand ρ (Ecast (Cbuiltin2fun (Tptr ty)) e)
ZifyUint63.to_Z_bounded: ∀ x : PrimInt63.int, (0 ≤ Uint63Axioms.to_Z x < 9223372036854775808)%Z
big_sepM2_Member_base:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type} (m : gmap K A) (m' : gmap K B) 
    (k : K) (x0 x1 : A) (y0 y1 : B) (P : K → A → B → PROP),
    prelude.LookupSearch (m !! k = Some x0)
    → prelude.LookupSearch (m' !! k = Some y0) → Member ([∗ map] k↦x1;x2 ∈ m;m', P k x1 x2) (P k x1 y1) k
_offsetR_big_sepL:
  ∀ {thread_info : biIndex} {Σ : gFunctors} {cpp_logic0 : cpp_logic thread_info Σ} (o : offset) {T : Type} (Rs : list T) 
    (F : nat → T → RepI), o |-> ([∗ list] i↦x ∈ Rs, F i x) ⊣⊢ ([∗ list] i↦x ∈ Rs, o |-> F i x)
map_union_subseteq_l':
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 m3 : M A), m1 ⊆ m2 → m1 ⊆ m2 ∪ m3
map_disjoint_omap:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A B : Type} (f1 f2 : A → option B) (m1 m2 : M A), m1 ##ₘ m2 → omap f1 m1 ##ₘ omap f2 m2
set_map_singleton:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ {B D : Type} {H7 : ElemOf B D} {H8 : Empty D} {H9 : Singleton B D} {H10 : Union D},
        SemiSet B D → ∀ (f : A → B) (x : A), set_map f {[x]} ≡ {[f x]}
Build_EnumConstant:
  ∀ (thread_info : biIndex) (_Σ : gFunctors) (Σ : cpp_logic thread_info _Σ) (tu : translation_unit) (gn : globname) (c : ident) (v : val),
    (∃ e : Expr,
       find_enum_constant gn c tu = Some e ∧ ∀ (σ : genv) (ρ : region) (Q : val → FreeTemps → mpredI), tu ⊧ σ → Q v 1%free ⊢ ::wpOperand ρ e)
    → EnumConstant tu gn c v
own_auth_frac_valid:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ucmra} {HasOwn0 : HasOwn PROP (authR A)},
            HasOwnValid PROP (authR A) → ∀ (g : gname) (q : Qp) (a : A), Observe [| (q ≤ 1)%Qp |] (own g (●{#q} a))
auth_both_valid_discrete: ∀ {A : ucmra}, CmraDiscrete A → ∀ a b : A, ✓ (● a ⋅ ◯ b) ↔ b ≼ a ∧ ✓ a
enum_constant_ok:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {tu : translation_unit} {gn : globname} {c : ident} {v : val},
    EnumConstant tu gn c v
    → ∃ e : Expr,
        find_enum_constant gn c tu = Some e
        ∧ ∀ (σ : genv) (ρ : region) (Q : val → FreeTemps → mpredI), tu ⊧ σ → Q v 1%free ⊢ ::wpOperand ρ e
SFunction_flip_mono_fupd':
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {cc : calling_conv} {ar : function_arity} 
    (ret : type) (targs : list type), Proper (wpspec_relation_fupd bi_entails --> flip fs_entails_fupd) (SFunction ret targs)
auth_update_dealloc: ∀ {A : ucmra} (a b a' : A), (a, b) ~l~> (a', ε) → ● a ⋅ ◯ b ~~> ● a'
own_excl_auth_frac_valid_2:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {HasOwn0 : HasOwn PROP (excl_authR A)},
            HasOwnValid PROP (excl_authR A)
            → ∀ (g : gname) (q1 q2 : Qp) (a1 a2 : A),
                Observe2 [| (q1 + q2 ≤ 1)%Qp |] (own g (excl_auth.excl_auth_frac q1 a1)) (own g (excl_auth.excl_auth_frac q2 a2))
tls_modalities.monPred_exactly_at_big_sepS:
  ∀ {I J : biIndex} {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → I -mon> PROP) 
    (X : gset A) (L : mlens.MLens I J) (j : J),
    tls_modalities.monPred_exactly_at L j ([∗ set] y ∈ X, Φ y) ⊣⊢ ([∗ set] y ∈ X, tls_modalities.monPred_exactly_at L j (Φ y))
map_Forall_delete:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (P : K → A → Prop) (m : M A) (i : K), map_Forall P m → map_Forall P (delete i m)
big_opS_gen_power:
  ∀ {M : ofe} {o : M → M → M} {H : Monoid o} (R : relation M) {A : Type} {EqDecision0 : EqDecision A} {H0 : Countable A} 
    (X : gset A) (x : M), Reflexive R → Proper (R ==> R ==> R) o → R ([^o set] _ ∈ X, x) (x ^^{o} N.of_nat (size X))
wp_init_shift:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (tu : translation_unit) (ρ : region) 
    (ty : exprtype) (p : ptr) (e : Expr) (Q : FreeTemps → epred), (|={⊤}=> ::wpPRᵢ ρ (Pointer ↦ p) e) ⊢ ::wpPRᵢ ρ (Pointer ↦ p) e
big_sepM2_persistent:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type} (Φ : K → A → B → PROP) (m1 : gmap K A) 
    (m2 : gmap K B),
    (∀ (k : K) (x1 : A) (x2 : B), m1 !! k = Some x1 → m2 !! k = Some x2 → Persistent (Φ k x1 x2))
    → Persistent ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
offset_inv_pinned_ptr_Z:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {H : cpp_logic thread_info _Σ} {σ : genv} (o : offset) (z : Z) (va : vaddr) (p : ptr),
    eval_offset σ o = Some z → valid_ptr p ⊢ pinned_ptr va (p ,, o) -∗ pinned_ptr_Z (va - z) p
CaseSplit_bool_decide_if_bp:
  ∀ (x : bool) (bp : bool_pair) (c : bool_val), CaseSplit x → CaseSplit (bool_decide ((if x then bp_b bp else bp_a bp) = bool_value c))
plogic.primR_canon_F:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} (σ : genv) (p : ptr) (q : cQp.t) (v : val) 
    (sz : int_rank) (sgn : signed), bool_decide (Tnum sz sgn ≠ "unsigned char"%cpp_type) → Fwd (p |-> primR (Tnum sz sgn) q v)
gen_phiN_complete:
  ∀ [R : Type] [rO rI : R] [radd rmul rsub : R → R → R] [ropp : R → R] [rdiv : R → R → R] [rinv : R → R] [req : R → R → Prop],
    Setoid_Theory R req
    → ring_eq_ext radd rmul ropp req
      → almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req
        → (∀ x y : R, req (radd rI x) (radd rI y) → req x y)
          → (∀ p : positive, ¬ req (gen_phiPOS1 rI radd rmul p) rO)
            → ∀ x y : N, req (gen_phiN rO rI radd rmul x) (gen_phiN rO rI radd rmul y) → (x =? y)%N = true
lib.cancelable_invariants.cinv_cancel:
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} {cinvG0 : cinvG Σ} (E : coPset) (N : namespace) (γ : gname) (P : iProp Σ),
    ↑N ⊆ E → lib.cancelable_invariants.cinv N γ P -∗ lib.cancelable_invariants.cinv_own γ 1 ={E}=∗ ▷ P
borrowR.borrowR.unlock:
  @borrowR.borrowR.body =
  λ (thread_info : biIndex) (_Σ : gFunctors) (Σ : cpp_logic thread_info _Σ) (σ : genv) (Field : Type) (EqDecision0 : EqDecision Field) 
    (H : Countable Field) (ToField0 : borrowR.ToField Field) (C : globname) (q : cQp.t) (m : gmap Field Rep),
    (borrowR._borrowR m ∗ structR C q)%I
gmultiset_set_fold_comm_acc_strong:
  ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} {B : Type} (R : relation B),
    PreOrder R
    → ∀ (f : A → B → B) (g : B → B) (b : B) (X : gmultiset A),
        (∀ x : A, Proper (R ==> R) (f x))
        → (∀ (x : A) (y : B), x ∈ X → R (f x (g y)) (g (f x y))) → R (set_fold f (g b) X) (g (set_fold f b X))
_at_arrayR_sub_type_ptrR_obs:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {X : Type} (R : X → Rep) 
    (ty : type) (i : Z) (p : ptr) (xs : list X),
    (0 ≤ i < base.length xs)%Z → Observe (p .[ ty ! i ] |-> type_ptrR ty) (p |-> arrayR ty R xs)
set_join_proper:
  ∀ {M : Type → Type} {H : ∀ A : Type, ElemOf A (M A)} {H0 : ∀ A : Type, Empty (M A)} {H1 : ∀ A : Type, Singleton A (M A)} 
    {H2 : ∀ A : Type, Union (M A)} {MBind0 : MBind M} {MRet0 : MRet M} {FMap0 : FMap M} {MJoin0 : MJoin M},
    MonadSet M → ∀ {A : Type}, Proper (equiv ==> equiv) mjoin
big_sepS_union_2:
  ∀ {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} {Φ : A → PROP} (X Y : gset A),
    (∀ x : A, TCOr (Affine (Φ x)) (Absorbing (Φ x))) → ([∗ set] y ∈ X, Φ y) -∗ ([∗ set] y ∈ Y, Φ y) -∗ [∗ set] y ∈ (X ∪ Y), Φ y
big_opM_ext:
  ∀ {M : ofe} {o : M → M → M} {Monoid0 : Monoid o} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type} 
    (f g : K → A → M) (m : gmap K A),
    (∀ (k : K) (x : A), m !! k = Some x → f k x = g k x) → ([^ o map] k↦x ∈ m, f k x) = ([^ o map] k↦x ∈ m, g k x)
map_Exists_delete:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (P : K → A → Prop) (m : M A) (i : K), map_Exists P (delete i m) → map_Exists P m
SConstructor_ne:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {cc : calling_conv} 
    {ar : function_arity} (class : globname) (targs : list type) (n : nat),
    Proper (pointwise_relation ptr (dist n) ==> dist n) (SConstructor class targs)
big_sepM2_singleton:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type} (Φ : K → A → B → PROP) (i : K) (x1 : A) (x2 : B),
    ([∗ map] k↦y1;y2 ∈ {[i := x1]};{[i := x2]}, Φ k y1 y2) ⊣⊢ Φ i x1 x2
map_solver.idlist_delete_snoc:
  ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (B : Type) (l l' : list map_solver.ID) (m : gmap A B) (k : A),
    map_solver.idlist_to_gmap (map_solver.deletes_of (l ++ [map_solver.Delete k]) m) l' =
    map_solver.idlist_to_gmap (map_solver.deletes_of l (delete k m)) l'
option_includedN_total:
  ∀ {A : cmra}, CmraTotal A → ∀ (n : nat) (ma mb : option A), ma ≼{n} mb ↔ ma = None ∨ ∃ a b : A, ma = Some a ∧ mb = Some b ∧ a ≼{n} b
tls_modalities.monPred_exactly_at_big_sepMS:
  ∀ {I J : biIndex} {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → I -mon> PROP) 
    (X : gmultiset A) (L : mlens.MLens I J) (j : J),
    tls_modalities.monPred_exactly_at L j ([∗ mset] y ∈ X, Φ y) ⊣⊢ ([∗ mset] y ∈ X, tls_modalities.monPred_exactly_at L j (Φ y))
PEpow_mul_l:
  ∀ [R : Type] [rO rI : R] [radd rmul rsub : R → R → R] [ropp : R → R] [rdiv : R → R → R] [rinv : R → R] [req : R → R → Prop],
    Equivalence req
    → ring_eq_ext radd rmul ropp req
      → almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req
        → ∀ [C : Type] (phi : C → R) [Cpow : Type] [Cp_phi : N → Cpow] [rpow : R → Cpow → R],
            power_theory rI rmul req Cp_phi rpow
            → ∀ (e e' : Ring_polynom.PExpr C) (n : N),
                NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow (Ring_polynom.PEpow (Ring_polynom.PEmul e e') n)
                  (Ring_polynom.PEmul (Ring_polynom.PEpow e n) (Ring_polynom.PEpow e' n))
PEpow_add_r:
  ∀ [R : Type] [rO rI : R] [radd rmul rsub : R → R → R] [ropp : R → R] [rdiv : R → R → R] [rinv : R → R] [req : R → R → Prop],
    Equivalence req
    → ring_eq_ext radd rmul ropp req
      → almost_field_theory rO rI radd rmul rsub ropp rdiv rinv req
        → ∀ [C : Type] (phi : C → R) [Cpow : Type] [Cp_phi : N → Cpow] [rpow : R → Cpow → R],
            power_theory rI rmul req Cp_phi rpow
            → ∀ (e : Ring_polynom.PExpr C) (n n' : N),
                NPEequiv rO rI radd rmul rsub ropp req phi Cp_phi rpow (Ring_polynom.PEpow e (n + n'))
                  (Ring_polynom.PEmul (Ring_polynom.PEpow e n) (Ring_polynom.PEpow e n'))
cast.wp_lval_xval_cast_noop:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (ρ : region) (ty : type) (e : Expr) (Q : ptr → FreeTemps → epred),
    cast.is_noop_cast_vc (valcat_of e) Xvalue (type_of e) ty =[Vm?]=> Some true → ::wpX ρ e ⊢ ::wpL ρ (Ecast (Cnoop (Tref ty)) e)
big_opS_insert:
  ∀ {M : ofe} {o : M → M → M} {Monoid0 : Monoid o} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (f : A → M) 
    (X : gset A) (x : A), x ∉ X → ([^o set] y ∈ ({[x]} ∪ X), f y) ≡ o (f x) ([^o set] y ∈ X, f y)
algebra.view_auth_dfrac_op_invI:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {B : ucmra} (rel : view_rel A B) (dp1 : dfrac) (a1 : A) (dp2 : dfrac) (a2 : A), ✓ (●V{dp1} a1 ⋅ ●V{dp2} a2) ⊢ a1 ≡ a2
map_to_list_empty_iff:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m : M A), map_to_list m = [] ↔ m = ∅
coq_tactics.transform_spatial_env:
  ∀ {PROP1 PROP2 : bi} {M : modality PROP1 PROP2} {C : PROP2 → PROP1 → Prop} {Γin : environments.env PROP2} {Γout : environments.env PROP1} 
    {filtered : bool},
    coq_tactics.TransformSpatialEnv M C Γin Γout filtered
    → (∀ (P : PROP2) (Q : PROP1), C P Q → P ⊢ M Q)
      → [∗] environments.env_to_list Γin ⊢ M ([∗] environments.env_to_list Γout) ∗ (if filtered then True else emp)
lookup_insert:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m : M A) (i : K) (x : A), <[i:=x]> m !! i = Some x
set_join_mono:
  ∀ {M : Type → Type} {H : ∀ A : Type, ElemOf A (M A)} {H0 : ∀ A : Type, Empty (M A)} {H1 : ∀ A : Type, Singleton A (M A)} 
    {H2 : ∀ A : Type, Union (M A)} {MBind0 : MBind M} {MRet0 : MRet M} {FMap0 : FMap M} {MJoin0 : MJoin M},
    MonadSet M → ∀ {A : Type}, Proper (subseteq ==> subseteq) mjoin
algebra.gmap_view_frag_validI:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {V : ofe} (k : K) (dq : dfrac) (v : V),
            ✓ gmap_view.gmap_view_frag k dq (to_agree v) ⊣⊢ ⌜✓ dq⌝
auth_both_dfrac_valid: ∀ {A : ucmra} (dq : dfrac) (a b : A), ✓ (●{dq} a ⋅ ◯ b) ↔ ✓ dq ∧ (∀ n : nat, b ≼{n} a) ∧ ✓ a
big_sepM2_affine:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A B : Type} (Φ : K → A → B → PROP) (m1 : gmap K A) 
    (m2 : gmap K B),
    (∀ (k : K) (x1 : A) (x2 : B), m1 !! k = Some x1 → m2 !! k = Some x2 → Affine (Φ k x1 x2)) → Affine ([∗ map] k↦y1;y2 ∈ m1;m2, Φ k y1 y2)
Compose.dual_sets_proper: ∀ (sf : Compose.config) {n1 n2 : Compose.name sf}, Proper (equiv ==> equiv ==> iff) (Compose.dual_sets sf)
coq_tactics.tac_specialize_intuitionistic_helper:
  ∀ {PROP : bi} (Δ : environments.envs PROP) (j : base.ident.ident) (q : bool) (P R R' Q : PROP),
    environments.envs_lookup j Δ = Some (q, P)
    → (if q then TCTrue else BiAffine PROP)
      → environments.envs_entails Δ (<absorb> R)
        → IntoPersistent false R R'
          → match environments.envs_replace j q true (environments.Esnoc  j R') Δ with
            | Some Δ'' => environments.envs_entails Δ'' Q
            | None => False
            end → environments.envs_entails Δ Q
set_fold_union:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ (f : A → A → A) (b : A) (X Y : C), IdemP eq f → Comm eq f → Assoc eq f → set_fold f b (X ∪ Y) = set_fold f (set_fold f b X) Y
class_instances_frame.frame_big_sepMS_disj_union:
  ∀ {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (p : bool) (Φ : A → PROP) (R Q : PROP) (X X1 X2 : gmultiset A),
    IsDisjUnion X X1 X2 → Frame p R (([∗ mset] y ∈ X1, Φ y) ∗ ([∗ mset] y ∈ X2, Φ y)) Q → Frame p R ([∗ mset] y ∈ X, Φ y) Q
own_view_auth_frac_valid:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {B : ucmra} (rel : view_rel A B) {HasOwn0 : HasOwn PROP (viewR rel)},
            HasOwnValid PROP (viewR rel) → ∀ (g : gname) (q : Qp) (a : A), Observe [| (q ≤ 1)%Qp |] (own g (●V{#q} a))
my_pretty_internals.Internals.InsertInFieldList_cons_match:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} (o : my_pretty_internals.Internals.offset_lit) 
    (os0 os1 : list my_pretty_internals.Internals.offset_lit) (Robj0 Robj1 Robj0' Robj1' : Rep) (RB : list
                                                                                                        my_pretty_internals.Internals.object_component) 
    (R' : Rep) (out : list my_pretty_internals.Internals.offset_lit),
    my_pretty_internals.Internals.CommonPointerBase os0 Robj0 Robj0' os1 Robj1 Robj1' out
    → my_pretty_internals.Internals.CombineObjectRep Robj0' Robj1' R'
      → my_pretty_internals.Internals.InsertInFieldList (my_pretty_internals.Internals.OBJ_offset (o :: os0) Robj0)
          (my_pretty_internals.Internals.OBJ_offset (o :: os1) Robj1 :: RB) (my_pretty_internals.Internals.OBJ_offset (o :: out) R' :: RB)
gset_bij.gset_bij_view_rel_raw_unit:
  ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} {B : Type} {EqDecision1 : EqDecision B} {H0 : Countable B} (n : nat),
    ∃ bijL : gset (A * B), gset_bij.gset_bij_view_rel_raw n bijL ε
Step.alt_gen_committer_proper:
  ∀ {PROP : bi} {H : prop_constraints.Ghostly PROP} {BiFUpd0 : BiFUpd PROP} (x : App.app) (E : coPset) (m : masks.t) (γ : AuthSet.gname),
    Proper (equiv ==> pointwise_relation (App.evt x) equiv ==> equiv) (Step.alt_gen_committer x E m γ)
merge_diag:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K},
    FinMap K M → ∀ {A C : Type} (f : option A → option A → option C) (m : M A), merge f m m = omap (λ x : A, f (Some x) (Some x)) m
paths.big_opL_map_filter:
  ∀ {M : ofe} {o : M → M → M} {H : Monoid o},
    Proper (equiv ==> equiv ==> equiv) o
    → ∀ {A B : Type} (h : A → D.option B) (f : B → M) (l : D.list A),
        D.big_opL o (λ (_ : nat) (y : B), f y) (D.map_filter h l)
        ≡ D.big_opL o (λ (_ : nat) (y : A), D.default monoid_unit (D.omap f (h y))) l
map_positive_l_alt:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 : M A), m1 ≠ ∅ → m1 ∪ m2 ≠ ∅
z_to_bytes._Z_from_to_bytes_le_roundtrip:
  ∀ (cnt : nat) (sgn : signed) (v : Z),
    match sgn with
    | Signed => (- 2 ^ (8 * cnt - 1) ≤ v ≤ 2 ^ (8 * cnt - 1) - 1)%Z
    | Unsigned => (0 ≤ v < 2 ^ (8 * cnt))%Z
    end → z_to_bytes._Z_from_bytes_le sgn (z_to_bytes._Z_to_bytes_le cnt sgn v) = v
SMethod_proper':
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {cc : calling_conv} {ar : function_arity} 
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type), Proper (equiv ==> equiv) (SMethod class qual ret targs)
Step.gen_requester_proper:
  ∀ {PROP : bi} {H : prop_constraints.Ghostly PROP} {BiFUpd0 : BiFUpd PROP} (x : App.app) (E : coPset) (m : masks.t) (γ : AuthSet.gname),
    Proper (equiv ==> pointwise_relation (App.evt x) equiv ==> equiv) (Step.gen_requester x E m γ)
gmap_equivI:
  ∀ {M : ucmra} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : ofe} (m1 m2 : gmap K A),
    m1 ≡ m2 ⊣⊢ ∀ i : K, m1 !! i ≡ m2 !! i
functions.SMethodOptCast_None_Some_mono:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {cc : calling_conv} {ar : function_arity} 
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type) (off2 : offset) (wpp1 : DOT_ptr_offset
                                                                                                         → WpSpec mpredI ptr ptr) 
    (wpp2 : ptr → WpSpec mpredI ptr ptr),
    (∀ thisp : ptr, wpspec_relation bi_entails (wpp1 (thisp ,, off2)) (wpp2 thisp))
    → fs_entails (functions.SMethodOptCast class None qual ret targs wpp1) (functions.SMethodOptCast class (Some off2) qual ret targs wpp2)
big_opS_union:
  ∀ {M : ofe} {o : M → M → M} {Monoid0 : Monoid o} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (f : A → M) (X Y : gset A),
    X ## Y → ([^o set] y ∈ (X ∪ Y), f y) ≡ o ([^o set] y ∈ X, f y) ([^o set] y ∈ Y, f y)
join.wp_operand_condition_to_bool:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (ρ : region) (tu : translation_unit) 
    (ty : exprtype) (tst th el : Expr) (Q : val → FreeTemps → mpred), ::wpOperand ρ tst ⊢ ::wpOperand ρ (Eif tst th el ty)
coGset.coGset_disj_alloc_empty_updateP_strong:
  ∀ {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} {H0 : Infinite A} (P : A → Prop) (Q : coGset.coGset_disj A → Prop),
    (∀ Y : coGset A, ∃ j : A, (j ∉ Y) ∧ P j) → (∀ i : A, P i → Q (coGset.CoGSet {[i]})) → coGset.CoGSet ∅ ~~>: Q
arrayR_cons_obs:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {X : Type} (R : X → Rep) 
    (ty : type) (x : X) (xs : list X),
    (∀ x0 : X, Observe (type_ptrR ty) (R x0)) → arrayR ty R (x :: xs) ⊣⊢ R x ∗ .[ ty ! 1 ] |-> arrayR ty R xs
Build_BiBUpdMixin:
  ∀ (PROP : bi) (H : BUpd PROP),
    NonExpansive bupd
    → (∀ P : PROP, P ⊢ |==> P)
      → (∀ P Q : PROP, (P ⊢ Q) → (|==> P) ⊢ |==> Q)
        → (∀ P : PROP, (|==> |==> P) ⊢ |==> P) → (∀ P R : PROP, (|==> P) ∗ R ⊢ |==> P ∗ R) → BiBUpdMixin PROP H
big_opM_opM:
  ∀ {M : ofe} {o : M → M → M} {Monoid0 : Monoid o} {K1 : Type} {EqDecision0 : EqDecision K1} {H : Countable K1} 
    {A K2 : Type} {EqDecision1 : EqDecision K2} {H0 : Countable K2} {B : Type} (f : K1 → A → K2 → B → M) (m1 : gmap K1 A) 
    (m2 : gmap K2 B),
    ([^ o map] k1↦x1 ∈ m1, [^ o map] k2↦x2 ∈ m2, f k1 x1 k2 x2) ≡ ([^ o map] k2↦x2 ∈ m2, [^ o map] k1↦x1 ∈ m1, f k1 x1 k2 x2)
big_opS_commute1:
  ∀ {M1 M2 : ofe} {o1 : M1 → M1 → M1} {o2 : M2 → M2 → M2} {Monoid0 : Monoid o1} {Monoid1 : Monoid o2} {A : Type} 
    {EqDecision0 : EqDecision A} {H : Countable A} (h : M1 → M2) {R : relation M2},
    WeakMonoidHomomorphism o1 o2 R h → ∀ (f : A → M1) (X : gset A), X ≠ ∅ → R (h ([^o1 set] x ∈ X, f x)) ([^o2 set] x ∈ X, h (f x))
aacc_intro:
  ∀ {PROP : bi} {H : BiFUpd PROP} {TA TB : tele} (Eo Ei : coPset) (α : TA → PROP) (P : PROP) (β Φ : TA → TB → PROP),
    Ei ⊆ Eo → ⊢ ∀.. x : TA, α x -∗ (α x ={Eo}=∗ P) ∧ (∀.. y : TB, β x y ={Eo}=∗ Φ x y) -∗ atomic_acc Eo Ei α P β Φ
map_size_fmap:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A B : Type} (f : A → B) (m : M A), size (f <$> m) = size m
map_fmap_mono:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A B : Type} (f : A → B) (m1 m2 : M A), m1 ⊆ m2 → f <$> m1 ⊆ f <$> m2
big_opMS_commute1:
  ∀ {M1 M2 : ofe} {o1 : M1 → M1 → M1} {o2 : M2 → M2 → M2} {Monoid0 : Monoid o1} {Monoid1 : Monoid o2} {A : Type} 
    {EqDecision0 : EqDecision A} {H : Countable A} (h : M1 → M2) {R : relation M2},
    WeakMonoidHomomorphism o1 o2 R h → ∀ (f : A → M1) (X : gmultiset A), X ≠ ∅ → R (h ([^o1 mset] x ∈ X, f x)) ([^o2 mset] x ∈ X, h (f x))
Step.gen_committer_proper:
  ∀ {PROP : bi} {H : prop_constraints.Ghostly PROP} {BiFUpd0 : BiFUpd PROP} (x : App.app) (E : coPset) (m : masks.t) (γ : AuthSet.gname),
    Proper (equiv ==> pointwise_relation (App.evt x) equiv ==> equiv) (Step.gen_committer x E m γ)
SMethodCast_None_Some_mono:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {cc : calling_conv} {ar : function_arity} 
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type) (off2 : offset) (wpp1 : DOT_ptr_offset
                                                                                                         → WpSpec mpredI ptr ptr) 
    (wpp2 : ptr → WpSpec mpredI ptr ptr),
    (∀ thisp : ptr, wpspec_relation bi_entails (wpp1 (thisp ,, off2)) (wpp2 thisp))
    → fs_entails (functions.SMethodOptCast class None qual ret targs wpp1) (functions.SMethodOptCast class (Some off2) qual ret targs wpp2)
map_imap_empty:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A B : Type} (f : K → A → option B), map_imap f ∅ = ∅
EnvRing.mkX_ok:
  ∀ [R : Type] [rO rI : R] [radd rmul rsub : R → R → R] [ropp : R → R] [req : R → R → Prop],
    Equivalence req
    → ring_eq_ext radd rmul ropp req
      → almost_ring_theory rO rI radd rmul rsub ropp req
        → ∀ [C : Type] [cO cI : C] [cadd cmul csub : C → C → C] [copp : C → C] [ceqb : C → C → bool] [phi : C → R],
            ring_morph rO rI radd rmul rsub ropp req cO cI cadd cmul csub copp ceqb phi
            → ∀ (p : positive) (l : Env.Env R), req (Env.nth p l) (EnvRing.Pphi radd rmul phi l (EnvRing.mk_X cO cI p))
operators.wp_eval_mod_longlong:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (av bv : Z) (Q : val → mpredI),
    [| bv ≠ 0%Z |] ∗ [| bitsize.bound (int_rank.bitsize int_rank.Ilonglong) Signed (av `quot` bv) |] ∗ Q (av `rem` bv)%Z
    ⊢ operators.wp_eval_binop.body tu Bmod "long long" "long long" "long long" av bv Q
wp_stmt_shift:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (tu : translation_unit) (ρ : region) 
    (b : bool) (thn els : Stmt) (Q : Kpred), (|={⊤}=> branch.stmt tu ρ b thn els (|={⊤}=> Q)) ⊢ branch.stmt tu ρ b thn els Q
operators.wp_eval_mod_long:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (av bv : Z) (Q : val → mpredI),
    [| bv ≠ 0%Z |] ∗ [| bitsize.bound (int_rank.bitsize int_rank.Ilong) Signed (av `quot` bv) |] ∗ Q (av `rem` bv)%Z
    ⊢ operators.wp_eval_binop.body tu Bmod "long" "long" "long" av bv Q
operators.wp_eval_mod_int:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (av bv : Z) (Q : val → mpredI),
    [| bv ≠ 0%Z |] ∗ [| bitsize.bound (int_rank.bitsize int_rank.Iint) Signed (av `quot` bv) |] ∗ Q (av `rem` bv)%Z
    ⊢ operators.wp_eval_binop.body tu Bmod "int" "int" "int" av bv Q
set_unfold_list_intersection_with:
  ∀ {A : Type},
    EqDecision A
    → ∀ (y : A) (l k : list A) (P Q : A → Prop) (R : A → A → Prop) (f : A → A → option A),
        (∀ x : A, SetUnfoldElemOf x l (P x))
        → (∀ x : A, SetUnfoldElemOf x k (Q x))
          → (∀ x1 x2 : A, SetUnfold (f x1 x2 = Some y) (R x1 x2))
            → SetUnfoldElemOf y (list_intersection_with f l k) (∃ x1 x2 : A, P x1 ∧ Q x2 ∧ R x1 x2)
view_auth_dfrac_validI:
  ∀ {M : ucmra} {A : ofe} {B : ucmra} (rel : view_rel A B) (relI : uPred M) (dq : dfrac) (a : A),
    (∀ (n : nat) (x : M), uPred_holds relI n x ↔ rel n a ε) → uPred_cmra_valid (●V{dq} a : view rel) ⊣⊢ ⌜✓ dq⌝ ∧ relI
curry4_proper':
  ∀ {A : Type} {RA : relation A} {B : Type} {RB : relation B} {C : Type} {RC : relation C} {D : Type} {RD : relation D} 
    {E : Type} {RE : relation E},
    Proper ((prod_relation (prod_relation (prod_relation RA RB) RC) RD ==> RE) ==> RA ==> RB ==> RC ==> RD ==> RE) curry4
map_Forall_singleton:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (P : K → A → Prop) (i : K) (x : A), map_Forall P ({[i := x]} : M A) ↔ P i x
App.all_aux: seal (@App.all_def)
mdc_path_normalize_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (nm : globname) (p : ptr) 
    (mdc mdc' : list globname) (q : cQp.t),
    mdc =[Vm?]= mdc' → CancelX MatchNormal [mdc_path nm mdc q p] [tele] CoverAny [derivationR nm mdc' q p]
D.mtele_append_args_invP':
  ∀ {t : D.tele} {mt1 : D.mtele t} {mt2 : D.mtele (D.to_tele mt1)} {args : D.tele_arg t} {P : D.sigT
                                                                                                (λ _ : D.tele_arg (D.to_tele mt1),
                                                                                                   D.tele_arg (D.to_tele mt2))
                                                                                              → Type},
    (∀ (eargs1 : D.tele_arg (D.to_fun mt1 args)) (eargs2 : D.tele_arg (D.to_fun mt2 (D.to_tele_args eargs1))),
       P {| D.projT1 := D.to_tele_args eargs1; D.projT2 := D.to_tele_args eargs2 |})
    → ∀ eargs : D.tele_arg (D.to_fun (D.mtele_append mt1 mt2) args), P (D.mtele_append_args_inv (D.to_tele_args eargs))
auth_updateP_both_unpersist: ∀ {A : ucmra} (a b : A), ●□ a ⋅ ◯ b ~~>: λ k : viewR auth_view_rel, ∃ q : Qp, k = ●{#q} a ⋅ ◯ b
algebra.prod_includedI:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A B : cmra} (x y : A * B), includedI.includedI x y ⊣⊢ includedI.includedI x.1 y.1 ∧ includedI.includedI x.2 y.2
map_disjoint_union_list_r_2:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (ms : list (M A)) (m : M A), Forall (λ m2 : M A, m2 ##ₘ m) ms → m ##ₘ ⋃ ms
arrayR_agree:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} {X T : Type} (ty : type) 
    (R : T → X → Rep) (q1 q2 : T) (l k : list X),
    (∀ (q3 q4 : T) (x1 x2 : X), Observe2 [| x1 = x2 |] (R q3 x1) (R q4 x2))
    → base.length l = base.length k → Observe2 [| l = k |] (arrayR ty (R q1) l) (arrayR ty (R q2) k)
arrayR_nil_build_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (ty : type) (T : Type) (TR : T → Rep) (l : ptr),
    is_Some (size_of σ ty) → CancelX MatchNormal [valid_ptr l] [tele] CoverAny [l |-> arrayR ty TR []]
map_to_list_submseteq:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 : M A), m1 ⊆ m2 → map_to_list m1 ⊆+ map_to_list m2
own_agree':
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : ofe} {HasOwn0 : HasOwn PROP (agreeR A)},
            HasOwnValid PROP (agreeR A) → ∀ (g : gname) (x y : agreeR A), Discrete x → Observe2 [| x ≡ y |] (own g x) (own g y)
option_included: ∀ {A : cmra} (ma mb : option A), ma ≼ mb ↔ ma = None ∨ ∃ a b : A, ma = Some a ∧ mb = Some b ∧ (a ≡ b ∨ a ≼ b)
uncurry4_proper':
  ∀ {A : Type} {RA : relation A} {B : Type} {RB : relation B} {C : Type} {RC : relation C} {D : Type} {RD : relation D} 
    {E : Type} {RE : relation E},
    Proper ((RA ==> RB ==> RC ==> RD ==> RE) ==> prod_relation (prod_relation (prod_relation RA RB) RC) RD ==> RE) uncurry4
map_Exists_singleton:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (P : K → A → Prop) (i : K) (x : A), map_Exists P ({[i := x]} : M A) ↔ P i x
cinv_cancel:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiBUpd0 : BiBUpd PROP} {BiFUpd0 : BiFUpd PROP},
    BiBUpdFUpd PROP
    → BiLaterContractive PROP
      → ∀ {HasOwn0 : HasOwn PROP fracR},
          HasOwnValid PROP fracR → ∀ (E : coPset) (N : namespace) (γ : gname) (P : PROP), ↑N ⊆ E → cinv N γ P -∗ cinv_own γ 1 ={E}=∗ ▷ P
eq_existT_curried_congr:
  ∀ {A : Type} {P : A → Type} {u1 v1 : A} {u2 : P u1} {v2 : P v1} {p p' : u1 = v1} {q : eq_rect u1 P u2 v1 p = v2} 
    {q' : eq_rect u1 P u2 v1 p' = v2} (r : p = p'),
    eq_rect p (λ H : u1 = v1, eq_rect u1 P u2 v1 H = v2) q p' r = q' → eq_existT_curried p q = eq_existT_curried p' q'
coq_tactics.tac_specialize_frame:
  ∀ {PROP : bi} (Δ : environments.envs PROP) (j : base.ident.ident) (q am : bool) (R P1 P2 P1' Q Q' : PROP),
    environments.envs_lookup j Δ = Some (q, R)
    → IntoWand q false R P1 P2
      → (if am then AddModal P1' P1 Q else TCEq P1' P1)
        → environments.envs_entails (environments.envs_delete true j q Δ) (P1' ∗ locked Q')
          → Q' = (P2 -∗ Q)%I → environments.envs_entails Δ Q
disjoint_filter_complement:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C → ∀ (P : A → Prop) {H7 : ∀ x : A, Decision (P x)} (X : C), filter P X ## filter (λ x : A, ¬ P x) X
trv_ref_spec_sind:
  ∀ P : type_qualifiers → type → type → SProp,
    (∀ (q : type_qualifiers) (t : type), ~~ is_ref t → ~~ is_qualified t → P q t (Trv_ref (tqualified q t)))
    → (∀ (q : type_qualifiers) (t : type), P q (Tref t) (tref QM t))
      → (∀ (q : type_qualifiers) (t ret : type), trv_ref_spec QM t ret → P QM t ret → P q (Trv_ref t) ret)
        → (∀ (q q' : type_qualifiers) (t ret : type),
             trv_ref_spec (merge_tq q q') t ret → P (merge_tq q q') t ret → P q (Tqualified q' t) ret)
          → ∀ (t : type_qualifiers) (t0 t1 : type), trv_ref_spec t t0 t1 → P t t0 t1
map_disjoint_union_list_l_2:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (ms : list (M A)) (m : M A), Forall (λ m2 : M A, m2 ##ₘ m) ms → ⋃ ms ##ₘ m
big_sepM_forall:
  ∀ {PROP : bi} {K : Type} {EqDecision0 : EqDecision K} {H : Countable K} {A : Type},
    BiAffine PROP
    → ∀ (Φ : K → A → PROP) (m : gmap K A), Persistent2 Φ → ([∗ map] k↦x ∈ m, Φ k x) ⊣⊢ ∀ (k : K) (x : A), ⌜m !! k = Some x⌝ → Φ k x
big_sepS_insert:
  ∀ {PROP : bi} {A : Type} {EqDecision0 : EqDecision A} {H : Countable A} (Φ : A → PROP) (X : gset A) (x : A),
    x ∉ X → ([∗ set] y ∈ ({[x]} ∪ X), Φ y) ⊣⊢ Φ x ∗ ([∗ set] y ∈ X, Φ y)
abs_pointer_toR_cancel:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (x p : ptr) (ty : type) 
    (mk : ptr → val) (q : cQp.t) (R : Rep), CancelX MatchNormal [x |-> primR ty q (mk p)] [tele] CoverAny [x |-> abs_pointer_toR ty mk q R]
lookup_singleton:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (i : K) (x : A), ({[i := x]} : M A) !! i = Some x
environments.envs_lookup_delete_list_sound:
  ∀ {PROP : bi} (Δ Δ' : environments.envs PROP) (rp : bool) (js : list base.ident.ident) (p : bool) (Ps : list PROP),
    environments.envs_lookup_delete_list rp js Δ = Some (p, Ps, Δ') → environments.of_envs Δ ⊢ □?p [∗] Ps ∗ environments.of_envs Δ'
own_frac_auth_agreeI:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiInternalEq0 : BiInternalEq PROP},
    BiEmbedInternalEq siPropI PROP
    → ∀ {BiPlainly0 : BiPlainly PROP},
        BiEmbedPlainly siPropI PROP
        → ∀ {A : cmra} {HasOwn0 : HasOwn PROP (frac_auth.frac_authR A)},
            HasOwnValid PROP (frac_auth.frac_authR A)
            → ∀ (g : gname) (q : Qp) (a b : A),
                Observe2 (a ≡ b) (own g (frac_auth.frac_auth_auth_frac q a)) (own g (frac_auth.frac_auth_frag 1 b))
wp_operand_cast_null_int:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (ρ : region) (e : Expr) (ty : type) (Q : val → FreeTemps → mpredI),
    can_represent_null (type_of e) → is_pointer ty → ::wpOperand ρ e ⊢ ::wpOperand ρ (Ecast (Cnull2ptr ty) e)
trv_ref_spec_ind:
  ∀ P : type_qualifiers → type → type → Prop,
    (∀ (q : type_qualifiers) (t : type), ~~ is_ref t → ~~ is_qualified t → P q t (Trv_ref (tqualified q t)))
    → (∀ (q : type_qualifiers) (t : type), P q (Tref t) (tref QM t))
      → (∀ (q : type_qualifiers) (t ret : type), trv_ref_spec QM t ret → P QM t ret → P q (Trv_ref t) ret)
        → (∀ (q q' : type_qualifiers) (t ret : type),
             trv_ref_spec (merge_tq q q') t ret → P (merge_tq q q') t ret → P q (Tqualified q' t) ret)
          → ∀ (t : type_qualifiers) (t0 t1 : type), trv_ref_spec t t0 t1 → P t t0 t1
map_Exists_to_list:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K},
    FinMap K M → ∀ {A : Type} (P : K → A → Prop) (m : M A), map_Exists P m ↔ Exists (uncurry P) (map_to_list m)
map_size_non_empty_iff:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m : M A), size m ≠ 0 ↔ m ≠ ∅
SMethodCast_mono_fupd':
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {cc : calling_conv} {ar : function_arity} 
    (class : globname) (qual : type_qualifiers) (ret : type) (targs : list type) (cast : offset),
    Proper (pointwise_relation ptr (wpspec_relation_fupd bi_entails) ==> fs_entails_fupd) (SMethodCast class cast qual ret targs)
map_Forall_to_list:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K},
    FinMap K M → ∀ {A : Type} (P : K → A → Prop) (m : M A), map_Forall P m ↔ Forall (uncurry P) (map_to_list m)
telescopes.mtele_append_args_invP':
  ∀ {t : telescopes.tele} {mt1 : telescopes.mtele t} {mt2 : telescopes.mtele (telescopes.to_tele mt1)} {args : telescopes.tele_arg t} 
    {P : telescopes.sigT (λ _ : telescopes.tele_arg (telescopes.to_tele mt1), telescopes.tele_arg (telescopes.to_tele mt2)) → Type},
    (∀ (eargs1 : telescopes.tele_arg (telescopes.to_fun mt1 args)) (eargs2 : telescopes.tele_arg
                                                                               (telescopes.to_fun mt2 (telescopes.to_tele_args eargs1))),
       P {| telescopes.projT1 := telescopes.to_tele_args eargs1; telescopes.projT2 := telescopes.to_tele_args eargs2 |})
    → ∀ eargs : telescopes.tele_arg (telescopes.to_fun (telescopes.mtele_append mt1 mt2) args),
        P (telescopes.mtele_append_args_inv (telescopes.to_tele_args eargs))
na_inv_proper:
  ∀ {PROP : bi} {BiEmbed0 : BiEmbed siPropI PROP} {BiBUpd0 : BiBUpd PROP} {BiFUpd0 : BiFUpd PROP},
    BiBUpdFUpd PROP
    → BiLaterContractive PROP
      → ∀ {HasOwn0 : HasOwn PROP (prodR coPset.coPset_disjR (gset.gset_disjR positive))},
          HasOwnValid PROP (prodR coPset.coPset_disjR (gset.gset_disjR positive))
          → HasOwnUpd PROP (prodR coPset.coPset_disjR (gset.gset_disjR positive))
            → ∀ (p : na_inv_pool_name) (N : namespace), Proper (equiv ==> equiv) (na_inv p N)
arrayR_anyR_f:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} {T : Type} (f : T → val) 
    (loc : ptr) (n : nat) (ty : type) (l : list T) (q : cQp.t),
    n = base.length l → loc |-> arrayR ty (λ x : T, primR ty q (f x)) l ⊢ loc |-> arrayR ty (λ _ : (), anyR ty q) (repeat () n)
_valid_ptr_off_sub_nonnull_2:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} {vt : validity_type} {ty : type} 
    (p : ptr) (i : Z) (sz : N),
    i ≠ 0 → size_of σ ty = Some sz → _valid_ptr vt p ⊢ _valid_ptr vt (p .[ ty ! i ]) -∗ [| p .[ ty ! i ] ≠ nullptr |]
map_size_ne_0_lookup_2:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m : M A) (i : K), is_Some (m !! i) → size m ≠ 0
do_delay_cases_ind:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {σ : genv} (tu : translation_unit) (ρ : region) 
    (v : Z) (DONE : Prop) (cases : list ((Z → Prop) * list Stmt)) (P : mpred) (Q : Kpred),
    delayed_case.result tu ρ P DONE cases v Q ↔ (Forall (λ '(pr, ss), P ⊢ [| pr v |] -∗ wp_block tu ρ ss Q) cases → DONE)
set_map_singleton_L:
  ∀ {A C : Type} {H : ElemOf A C} {H0 : Empty C} {H1 : Singleton A C} {H2 : Union C} {H3 : Intersection C} {H4 : Difference C} 
    {H5 : Elements A C} {EqDecision0 : EqDecision A},
    FinSet A C
    → ∀ {B D : Type} {H7 : ElemOf B D} {H8 : Empty D} {H9 : Singleton B D} {H10 : Union D},
        SemiSet B D → LeibnizEquiv D → ∀ (f : A → B) (x : A), set_map f {[x]} = {[f x]}
auth_auth_dfrac_op_validI:
  ∀ {M A : ucmra} (dq1 dq2 : dfrac) (a1 a2 : A),
    uPred_cmra_valid (●{dq1} a1 ⋅ ●{dq2} a2) ⊣⊢ uPred_cmra_valid (dq1 ⋅ dq2) ∧ a1 ≡ a2 ∧ uPred_cmra_valid a1
operators.wp_eval_add_int_ptr:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} {resolve : genv} (tu : translation_unit) 
    (w : int_rank) (s : signed) (av : Z) (bv : DOT_from DOT_ptr_offset) (Q : val → mpredI) (ty : type),
    HasSize ty
    → (let p' := bv .[ ty ! av ] in valid_ptr p' ∗ Q (Vptr p'))
      ⊢ operators.wp_eval_binop.body tu Badd (Tnum w s) (Tptr ty) (Tptr ty) av (Vptr bv) Q
cofe_solver.solver.unfold_ne:
  ∀ (F : oFunctor) {Fcontr : oFunctorContractive F} {Fcofe : ∀ (T : ofe) (Cofe0 : Cofe T), Cofe (oFunctor_apply F T)} 
    {Finh : Inhabited (oFunctor_apply F unitO)} (n : nat), Proper (dist n ==> dist n) (cofe_solver.solver.unfold F)
auth_both_dfrac_valid_discrete: ∀ {A : ucmra}, CmraDiscrete A → ∀ (dq : dfrac) (a b : A), ✓ (●{dq} a ⋅ ◯ b) ↔ ✓ dq ∧ b ≼ a ∧ ✓ a
shift_pinned_ptr_sub:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {H : cpp_logic thread_info _Σ} {σ : genv} (ty : type) (z : Z) (va : vaddr) 
    (p1 p2 : ptr) (o : N),
    p1 .[ ty ! z ] = p2 → size_of σ ty = Some o → valid_ptr p2 ∗ pinned_ptr va p1 ⊢ pinned_ptr (Z.to_N (va + z * o)) p2
RingMicromega.Psatz_rect:
  ∀ [C : Type] (P : RingMicromega.Psatz C → Type),
    (∀ p : RingMicromega.Psatz C, P p → ∀ p0 : RingMicromega.Psatz C, P p0 → P (RingMicromega.PsatzLet p p0))
    → (∀ n : nat, P (RingMicromega.PsatzIn C n))
      → (∀ p : RingMicromega.PolC C, P (RingMicromega.PsatzSquare p))
        → (∀ (p : RingMicromega.PolC C) (p0 : RingMicromega.Psatz C), P p0 → P (RingMicromega.PsatzMulC p p0))
          → (∀ p : RingMicromega.Psatz C, P p → ∀ p0 : RingMicromega.Psatz C, P p0 → P (RingMicromega.PsatzMulE p p0))
            → (∀ p : RingMicromega.Psatz C, P p → ∀ p0 : RingMicromega.Psatz C, P p0 → P (RingMicromega.PsatzAdd p p0))
              → (∀ c : C, P (RingMicromega.PsatzC c)) → P (RingMicromega.PsatzZ C) → ∀ p : RingMicromega.Psatz C, P p
lib.invariants.inv_combine:
  ∀ {hlc : has_lc} {Σ : gFunctors} {invGS_gen0 : invGS_gen hlc Σ} (N1 N2 N : namespace) (P Q : iProp Σ),
    N1 ## N2 → ↑N1 ∪ ↑N2 ⊆ ↑N → lib.invariants.inv N1 P -∗ lib.invariants.inv N2 Q -∗ lib.invariants.inv N (P ∗ Q)
ptr_ord_comparable_off:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {H : cpp_logic thread_info _Σ} {σ : genv} (o1 : offset) (base : DOT_from DOT_ptr_offset) 
    (p1 : DOT_ptr_offset) (f : vaddr → vaddr → bool) (res : bool),
    p1 = base ,, o1
    → (∀ va1 va2 : vaddr, ptr_vaddr p1 = Some va1 → ptr_vaddr base = Some va2 → f va1 va2 = res)
      → valid_ptr p1 ∗ valid_ptr base ⊢ ptr_ord_comparable p1 base f res
wp_mfptr_frame_fupd_strong:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} {Σ : cpp_logic thread_info _Σ} (tt1 tt2 : type_table) (t : exprtype) 
    (t0 : functype) (v : ptr) (l : list ptr) (Q1 Q2 : ptr → mpredI),
    type_table_le tt1 tt2 → (∀ v0 : ptr, Q1 v0 ={⊤}=∗ Q2 v0) ⊢ wp_mfptr tt1 t t0 v l Q1 -∗ wp_mfptr tt2 t t0 v l Q2
set_guard_True:
  ∀ {M : Type → Type} {H : ∀ A : Type, ElemOf A (M A)} {H0 : ∀ A : Type, Empty (M A)} {H1 : ∀ A : Type, Singleton A (M A)} 
    {H2 : ∀ A : Type, Union (M A)} {MBind0 : MBind M} {MRet0 : MRet M} {FMap0 : FMap M} {MJoin0 : MJoin M} {H3 : MonadSet M} 
    {A : Type} {P : Prop} {H4 : Decision P} (X : M A), P → guard P ≫= (λ _ : P, X) ≡ X
map_disjoint_union_l:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m1 m2 m3 : M A), m1 ∪ m2 ##ₘ m3 ↔ m1 ##ₘ m3 ∧ m2 ##ₘ m3
delete_notin:
  ∀ {K : Type} {M : Type → Type} {H : FMap M} {H0 : ∀ A : Type, Lookup K A (M A)} {H1 : ∀ A : Type, Empty (M A)} 
    {H2 : ∀ A : Type, PartialAlter K A (M A)} {H3 : OMap M} {H4 : Merge M} {H5 : ∀ A : Type, MapFold K A (M A)} 
    {EqDecision0 : EqDecision K}, FinMap K M → ∀ {A : Type} (m : M A) (i : K), m !! i = None → delete i m = m
wp_init_initlist_prim_array_implicit_B:
  ∀ (thread_info : biIndex) (_Σ : gFunctors) (Σ : cpp_logic thread_info _Σ) (σ : genv) (tu : translation_unit) (ρ : region) 
    (base : ptr) (arr_ty : type) (Q : FreeTemps → mpredI) (ty_prim : type) (len : N) (init_val : val),
    zero_init_val tu ty_prim = Some init_val
    → HasSize ty_prim
      → is_array_of arr_ty ty_prim
        → erase_qualifiers ty_prim = ty_prim → Bwd (::wpPRᵢ ρ (Pointer ↦ base) (Einitlist [] (Some (Eimplicit_init ty_prim)) arr_ty))


.... huge respnse exceeding o4-mini context size. clipped here
