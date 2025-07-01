## User 1

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

# Separtion Logic Library for reasoning about C++ programs in Coq
The current task may involve writing Gallina definitions (e.g. specifications of c++ functions) involving a separation logic formalization in Coq.
This formalization is just an instantiation of the iris separation logic library, which was first presented in the 2015 POPL paper titled 
"Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning", which I assume you already understand.
This section gives a brief review of our iris instantiation for reasoning about C++ programs in Coq.

You already know about `Prop`, the type of logical propositions in Coq.
For example. `True -> False`, `True /\ False`, `forall n:nat, n=n`, `exists n:nat, n=n` 
are propositions in Coq of type `Prop`.

Assertions in separation logic can also talk about the state of the memory (stack/heap) and assert ownership over memory cells.
(This can be generalized beyond memory, to state of the world.)
In Coq, we have defined the type `mpred` of separation logic assertions. 
Given `a:N`, the separation logic assertion `a_addr |-> primR "int" (cQp.mut 1) (Vint a)`
asserts that `a_addr` is a memory location which stores a primitive value (`primR`) `Vint a` of the primitive type "int". `a_addr` has type `ptr` (`bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr`), which is type we have axiomatized in Gallina to represent abstract memory locations in C++.

The argument `cQp.mut 1` of type `cQp.t` signifies the ownership fraction and constness.
For now, always use the `cQp.mut` constructor of type `Qp -> cQp.t`.
The `1:Qp` in `cQp.mut 1` says that the `a_addr |-> primR "int" (cQp.mut 1) (Vint a)` has complete (fraction 1) ownership of the location. 
So nobody else can be reading/writing that location concurrently. `Qp` is a type of positive rational numbers in Coq. 
Unlike in other programming languages, in Coq, the type `Q` (rational numbers), just like the type `Z` (integers), has infinite precision: there are no rounding errors.

Ownership of any positive fraction of a memory location containing a primitive value suffices to read it.
However, to write to a location containing a primitive value, full (1) fraction is needed.
This follows most separation logics with fractional permissions/ownerships.

In `(Vint a)`, `Vint` has type  `Z->val`
`val` is the type of (primitive) values stored at C++ "pointers" (abstract memory locations):

```gallina
Variant val : Set :=
    Vint : Corelib.Numbers.BinNums.Z → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
  | Vchar : Corelib.Numbers.BinNums.N → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
  | Vptr : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
  | Vraw : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_byte → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
  | Vundef : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
  | Vmember_ptr : name
                  → Corelib.Init.Datatypes.option (bluerock.lang.cpp.syntax.core.atomic_name_ type)
                    → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val.

Arguments bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vint _%_Z_scope
Arguments bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar _%_N_scope
Arguments bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vmember_ptr _%_cpp_name_scope _
```
In Coq, `Variant` is just like `Inductive`, except that in `Variant` type declarations, types of constructor arguments cannot refer to the type being defined. Such references happen in "recursive" Inductive types like `list` (the `cons` constructor).

Any proposition of type Prop can also be injected to mpred. If `P:Prop`, then `[| P |]` is of type mpred.
`[| P |]` says nothing about the state of the world (it is "pure") and just asserts the logical property P.
mpred has analogues of the logical connectives of Prop.
For example, if `A:mpred`, `B:mpred`, `A //\\ B` and `A \\// B` are the classical conjunctions and disjunctions.
For universal quantification in mpred, use `Forall` (instead of `forall` in Prop).
Similarly, for existential quantification, use `Exists` (instead of `exists` in Prop).
For example, if A:N->mpred, `Forall a:N, A n` and `Exists a:N, A n` have type `mpred`.

The main new connective in mpred is the separating conjunction, for which we have defined in Coq the notation `**` in our setup.
if `A:mpred`, `B:mpred`, `A ** B` denotes the separating conjunction of A and B.
Unlike `A //\\ B`, `A ** B` asserts that the ownership footprint of A and B are disjoint.

Given `A:mpred`, `B:mpred`, `A |-- B` of type `Prop` denotes separation logic entailment.
It is similar to implication `(A->B)` in classical logic. 
In addition, it also says that the ownership footprint of B is included in the ownership footprint of A. Here are some examples of valid entailments:
```gallina
mloc |-> primR "int" (cQp.mut 1) (Vint 1) |-- Exists a, mloc |-> primR "int" (cQp.mut 1) (Vint a)
mloc |-> primR "int" (cQp.mut 1) (Vint 1) |-- mloc |-> primR "int" (cQp.mut (1/2)) (Vint 1)
P ** Q |-- P
```
In contrast, `mloc |-> primR "int" (cQp.mut 1) (Vint 1) |-- mloc |-> primR "int" (cQp.mut (1/2)) (Vint 2)`
does not hold and we can in fact prove
`(mloc |-> primR "int" (cQp.mut 1) (Vint 1) |-- mloc |-> primR "int" (cQp.mut (1/2)) (Vint 2)) -> False.`

The following is also not provable because the LHS has a smaller fractional ownersip (1/3 instead of 1/2).
```
  Lemma insufficientFrac mloc :
    mloc |-> primR "int" (1/3) (Vint 0) |--
   mloc  |-> primR "int" (1/2) (Vint 0).
  Abort. (* not provable *)
```

`A -|- B`, read as `A` bi-entails `B` is defined as `((A |-- B) /\ (B--A))`.


## deeper dive on `|->` (points_to) assertion

```gallina
  Example as11 (mloc: ptr) (bv:Z) :mpred :=  mloc |-> primR "int" 1 (Vint bv).
```
As mentioned before, the LHS of `|->` must be a memory location, of type `ptr`.
In our C++ semantics the memory location corresponding to a global variable `b` is represented as `_global "b"`:

```gallina
Example memLoc: ptr := _global "b".
```

The RHS of `|->` must be a "memory representation", of type `Rep`.
`Rep`s:
- defines how some "mathematical" Coq object is laid out in memory
- specify the amount of ownership
`primR` axiomatizes the `Rep` for primitive/scalar c++ types: int/char/long/int*/...
  
```gallina
  Example intRep (q:Qp) (x:Z) : Rep := primR "int" q (Vint x).
```
The last argument of of `primR` is of type `val` whose `Inductive` (`Variant`) definition was shown above.
As shown above, there are other constructors of the `val` type, e.g. the `Vptr` constructor that embeds a memory location (`ptr`) into a `val`. 
For example, we can write a `Rep` as follows:

```gallina
  Example ptrRep (q:Qp) (mloc: ptr) : Rep := primR "int*" q (Vptr mloc).
```
`Rep`s are morally functions of type `ptr -> mpred` and the `|->` can be thought of applying the `Rep` on the RHS of `|->` to the memory location on the left of `|->`. 
For example, the following assertion (`as12`) asserts that the global variable `b` of type `int*` currently has stored the memory location `mloc` and also asserts full (`1`) ownership of the location `_global "b"` (but no ownership of `mloc`).
```gallina
  Example as12 (mloc:ptr) :mpred :=  _global "b" |-> primR "int*" 1 (Vptr mloc).
```

We can use those primititive `Rep`s and the offset operations (e.g. field offsets, array index offsets) on `ptr` to define `Rep`s for non-scalar types like structs/arrays, as we will see later.
# Separation Logic Specs of C++ functions

The current task may involve writing separation logic specs of C++ functions.
This section explains some custom Coq notations we have developed for writing specs of C++ functions in Coq.
Consider a very simple C++ function foo:

## A simple spec example
```c++
using uint = unsigned int;

uint x = 0;
uint y;

void foo() {
    y=0;
    y=x+1;
}
```

Here's its spec in Gallina in our framework:

```gallina
Notation uint := "unsigned int"%cpp_type.

  cpp.spec "foo()" as foo_spec with (
        \pre{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv (* forall xv .. *)
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N ** _global "x" |-> primR uint (cQp.mut (1/2))  xv
      ).
```

`cpp.spec` is an elpi-wrapper that creates a regular Gallina `Definition` of `foo_spec` and also declares some typeclass instances that our proof automation can use to find specs. In this case, it produces the following definition:


```gallina
Definition foo_spec : mpred :=
  specify {| info_name := "foo()"; info_type := tFunction "void" [] |}
        (\pre{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv (* forall xv .. *)
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N ** _global "x" |-> primR uint (cQp.mut (1/2))  xv).
```

`cpp.spec` automatically finds out the type of the c++ function and populates the `info_type` record element.
In `tFunction "void" []`, the first argument is the return type of `foo` and the list is the types of arguments.
We have cpp2v, a clang-ast-visitor tool that converts c++ ASTs to Gallina (as a .v file). These .v files define `module` of type `translation_unit`, denoting the AST of the C++ file:

```gallina
Record translation_unit : Type := {
  symbols : symbol_table;
  types : type_table;
  initializer : InitializerBlock;
  byte_order  : endian;
}.
```
To write specs of a c++ file, we need to `Require Import` the file produced by cpp2v.
`cpp.spec` finds the type signatures from the resultant `module:translation_unit` in context.
`cpp.spec` also detects some common mistakes in specs so we use it instead of writing the `Definition` directly.
The general syntax of `cpp.spec` is:
```gallina
cpp.spec [fully_qualified_cpp_function_name] as [gallina_defn_name] with ([spec]).
```

`spec` should be of type `WpSpec mpred val val`. `WpSpec` is a compex record type and we do not construct its elements by directly. Instead, we use notations like `\pre` `\post` which construct the appropriate record. 
Lets look at the spec part of `foo_spec` above, which I have reproduced below.
```gallina
  (\pre{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv (* forall xv .. *)
   \pre _global "y" |-> anyR uint (cQp.mut 1)
   \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N ** _global "x" |-> primR uint (cQp.mut (1/2))  xv).
```

The first 2 lines specify 2 preconditions of the function and the last line specifies the postcondition. In general, a spec is just a precondition and postcondition. Multiple assertions can be combined using separation logic's `**` into a single precondition. However, for more readability, we can write different conjuncts in separate lines using the `pre` notation repeatedly in each line.

Let's look at the second line, which is the simpler precondition:
```gallina
   \pre _global "y" |-> anyR uint (cQp.mut 1)
```
It asserts full ownership of the memory location for the global variable `"y"`.
But it does not at all constrain the value that is stored at the variable `y`.
Infact, it allows `y` to be unitialized.
C++ semantics requires memory locations being read to be initialized but `foo` only writes to `y`. 
Writing to uninitialized memory locations is fine. Below is a formal characterization of `anyR`:

```gallina
Lemma anyR_iff : 
  (_global "y" |-> uninitR uint 1 \\// (Exists xv:Z, _global "y" |-> primR uint 1 xv))
  -|-  _global "y" |-> anyR uint 1.
Proof. 
  rewrite bi.or_alt. go.
  ren_hyp t bool.
  destruct t; go. 
Qed.
```

Now look at the first precondition in `foo_spec`:

```gallina
\pre{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv (* forall xv .. *)
```
`\pre` can be followed curly braces containing variable quantifications. 
These variables are universally quantified and are in scope even in the subsequent `\pre` and `\post` items.
In other words, the caller of the function gets to choose any well-typed instantiation of these variables.
This precondition says that the memory location for the global variable `"x"` has the value `xv`, which is a Gallina variable (not a c++ variable). The type of `xv` is the familiar `Z` (`Corelib.Numbers.BinNums.Z`) from the Coq standard library.
This precondition also asserts `1/2` ownership over the memory location. 
Because `foo()` only reads the memory location, any (positive) fraction suffices. 
Later, we will see a generalized variant of foo_spec.
Now look at the postcondition:
```
   \post _global "y" |-> primR uint (cQp.mut 1) (((xv+1) `mod` (2^32))%N `mod` (2^32))%N ** _global "x" |-> primR uint (cQp.mut (1/2))  xv).
```
The second conjunct `_global "x" |-> primR uint (cQp.mut (1/2))  xv` is exactly the same as the precondition: `foo()` doesnt change the variable `x` and doesnt store or pass any fraction of the ownership of `x` to another thread, so it returns back the entire ownership of `x`.
Similarly `foo()` returns back the entire (`1`) ownership of `y`, but changes the value of `y` to `xv+1`, as specified by the first conjunct `_global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N ** _global "x"`.

### variants of the above spec

First, lets formally see that meaning of multiple `\pre`s: they are equivalent to combining them by `**`. For example, the above spec is equivalent to the following which is often considered less readable.
```gallina
  cpp.spec "foo()" as foo_spec with (
        \pre{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv ** _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N ** _global "x" |-> primR uint (cQp.mut (1/2))  xv
      ).
```

We have notations to make specs less verbose. For example, the conjunct `_global "x" |-> primR uint (cQp.mut (1/2))  xv` was both a precondition and a postcondition. We can use `\prepost` to equivalently write such conjuncts only once:
```gallina
  cpp.spec "foo()" as foo_spec with (
        \prepost{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv (* this is both a precondition and a postcondition *)
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N
      ).
```

Finally, lets see a stronger spec where the precondition is weakened by generalizing the onwership fraction `(1/2)` to an arbitrary positive rational number (type `Qp`, which is a Gallina type defined by the stdpp library distributed by iris developers (`stdpp.numbers.Qp`)).
Qp has regular arithmetic operations/notations like +, /, * defined. Use `Qp` as the scope delimiting key to use these notations, 
e.g. (1/2+1/3)%Qp.

```gallina
    cpp.spec "foo()" as foo_spec with (
        \prepost{(xv:Z) (q:Qp)} _global "x" |-> primR uint (cQp.mut q) xv (* this is both a precondition and a postcondition *)
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N
      ).
```
Note that there can be multiple variable quantifications in curly braces but they need to put in parentheses, just as one would do in Gallina after `forall` e.g, `forall (n:nat) (m:nat), 0<=n+m`.

## Specs involving pointer variables

Consider the function `fooptr` below:
```c++
int a = 0;
int *cptr;

void fooptr () {
    cptr = &a;
}
```

`fooptr` has the following spec:

```gallina
  cpp.spec "fooptr()" as ptrspec with
      (\pre _global "cptr" |-> anyR "int*" 1
       \post _global "cptr" |-> primR "int*" 1 (Vptr (_global "a")) 
      ).
```
Both the the precondition an the postcondition assert full (`1`) ownership of the (C++) global variable `cptr` of type `int*`.
The precondition allows that variable to contain any value or even be uninitialized.
The postcondition guarantees that `cptr` has the value that is the memory location of the (C++) global variable `a`.

## Specs of functions receiving arguments and returning values

Consider the simple twice function below, which accepts arguments and returns a value.
```c++
uint twice (uint x) {return 2*x;}
```

Here is a very simple but very weak spec, but illustrates how to capture arguments and return values in specs:
```gallina
  cpp.spec "twice(unsigned int)" as twice_weak_spec with (
     \arg "x" (Vint 1)
     \post [Vint 2] emp
      ).
```
The first line of the core spec (`\arg "x" (Vint 1)`) says that the there is one argument, whose C++ name is `x` and its value is assumed to be `Vint 1` as a precondition.
The last argument of `\arg` must be of type `val`.
Similarly, after `\post`, we can specify the returned value of type `val` in square brackets. So, in `\post [Vint 2] emp`, `[Vint 2]` says that the function returns `2`, assuming then precondition are true. the last argument of `\post` must be a separation logic assertion (of type `mpred`) formally representing the postcondition of the function.
`emp: mpred` denotes empty ownership. It is the left/right identity element of separating conjunction (`**`), just like `True:Prop` is the identity element of regular logical conjunction in classical/intuitionistic logics (`Prop`).
In fact, `emp:mpred` can be defined as `[| True |]`.
In this case, the function `twice` is not passed in any external ownership and does not return any ownership: the argument is passed by value and and the result is returned by value. Later, we will see cases where arguments are passed by reference and in such cases, external ownership is passed in as a precondition and returned as a postcondition.

Before that, lets make the spec more general. The only change we need is to generalize over the `1` in `\arg "x" (Vint 1)` to an arbitrary universally quantified number.
Just like `\pre`, `\arg` can have universally quantified variables in curly braces:

```gallina
  cpp.spec "twice(unsigned int)" as twice_spec with (
     \arg{xv:Z} "x" (Vint xv)
     \post [Vint ((xv*2) `mod` (2^32))] emp
      ).
```
Now the precondition is relaxed to allow passing
any non-negative integer as an argument.
Even though the spec, as written, doesnt say that `xv` is non-negative,
the way we have defined semantics of function calls allows the proof of this spec to assume `(0<=xv<2^32)`. This allows the spec to be less verbose and avoid mentioning the conditions on the `val` (last) argument of `arg` imposed by its type.
More formally, in a proof that an implementation satisfies a spec, one gets to use implicit assumptions that 
the values specified as last arguments of `\arg` satisfy `bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.has_type_prop`
for the C++ type of the argument:

```gallina
bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.has_type_prop
     : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val → bluerock.lang.cpp.syntax.core.type → Prop
```
You can issue the query `Search bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.has_type_prop` if you need to more precisely know the implicit assumptions.

Even the `\post` keyword allows variable quantification in curly braces.  Unlike in `\pre`, `\arg`, `\prepost` where the variable quantifications are universal (instantiation chosen by caller and the implementation must consider all well-typed instantiations), the variable quantifications in the curly braces just after `\post` are existential in nature: the implementation of the function gets to choose the instantiation and the callers must consider all well-typed insantiations.
Existential quantifications in `\post` are useful when we do not want the caller to know the exact returned value or when the returned value is non-deterministic.
For example, lets weaken the spec above to weaken the postcondition to merely say that the returned value is even and not guarantee anything else: 

```gallina
  cpp.spec "twice(unsigned int)" as twice_weak_spec2 with (
     \arg{xv:Z} "x" (Vint xv)
     \post{xvfinal} [Vint xvfinal] [| xvfinal `mod` 2 = 0 |]
      ).
```
This spec would make more sense if the function had name `someEvenNumberBasedOn` rather than `twice`. A valid implementation could pick a random number less than half of INT_MAX and multiply it by 2 to compute the returned value. 


## Specs of functions passing arguments by reference

`doubleInPlace` is similar to `twice` except the the argument is passed by reference and the result is stored in the same place.
```c++
void doubleInPlace (uint & x) {x=2*x;}
```
Below is its spec.

```gallina
  cpp.spec "doubleInPlace(unsigned int &)" as doubleInPlace_spec with (
     \arg{xloc:ptr} "x" (Vptr xloc)
     \pre{xv:Z} xloc |-> primR "unsigned int" (cQp.mut 1) (Vint xv)
     \post xloc |-> primR "unsigned int" (cQp.mut 1) (Vint ((xv*2) `mod` (2^32)))
      ).
```
Unlike in `twice(unsigned int)`, the argument now contains not an integer value but a memory location, say `xloc`.
In the C++ axiomatization, an argument passed by reference is similar to an argument passed as a pointer.
The `\pre` line then asserts full (1) ownership of `xloc` and asserts that it contains a primitive integer, say `xv`.
The postcondition returns all that ownership of `xloc` but asserts the updated (twice) value.

## Specs of functions with composite datatype arguments.

`primR`, the representation of primitive types like int/char/long/.. is axiomatized by our C++ semantics.
However, the representation of composite types like int[], structs can be constructed using `primR` and an axiomatized offset operation on memory locations (`ptr`):

```gallina
bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM._offset_ptr: ptr → offset → ptr
```

`offset` can be constructed in 2 ways: field offsets of structs/classes, array offsets.

`o_sub` is the axiomatised operator to construct array offsets:
```gallina
bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_sub : genv → type → Z → offset
```
The `genv` is automatically inferred using typeclasses. When writing specs, a `Section` variable of type `genv` is typically always in context. 
A `genv` represents platform parameters like endianness, word size of the machine. 
The `type` argument is the C++ type of the array, and the `Z` argument is the array index.

### Array offsets
Consider the following global variable in a C++ file:
```c++
int arr[3];
```

In Gallina,  `_global "arr"` represents the memory location of that C++ global variable `arr`.
`_offset_ptr (_global "arr") (o_sub _ "int" 2)` represents the C++ location `arr[2]`.
We have defined a notation to make gallina array index offsets look somewhat like C++, except that `o_sub` needs the C++ type as well explicitly.

```coq
  Example notation_example1: (_global "arr").["int"!2] =  _offset_ptr (_global "arr") (o_sub _ "int" 2).
  Proof.
    reflexivity.
  Qed.
```


With that notation, we can write the following assertion that asserts full ownership of the cell `arr[2]` in C++ and also asserts that that cell has the value 99.

```gallina
Example array_cell_assertion := (_global "arr").["int"!2]  |-> primR "int" 1 (Vint 99).
```

#### `arrayR`
While writing specs of functions that return arrays or receive them as arguments, it can be verbose to separately assert ownership of every cell. Thus, we have `arrayR`, a recursive definition (NOT an axiom) which asserts ownership of all cells. Its definition has a few layers so lets just illustrate it with an example:

```galina
Example arrayR3Unfold {T:Type} (p:ptr) (n1 n2 n3: T) (R:T->Rep):
  p |-> arrayR uint R [n1;n2;n3]
    -|- ( valid_ptr (p .[ uint ! 3 ])
            ** p |-> R n1
            ** p .[ uint ! 1 ] |-> R n2
            ** p .[ uint ! 2 ] |-> R n3).
```
The last 3 conjuncts just assert the ownership of the first 3 cells, parametrized by `R` which defines how a mathematical item of Gallina type `T` is represented in C++ memory.
The first conjunct, `valid_ptr (p .[ uint ! 3 ])`, is crucial to show that pointer increments are not undefined behaviour (UB). For example, the following program has UB according to C++ semantics:

```c++
void ubptr(){
  int arrl[3];
  int *p=arrl;
  p++;// proof generates gallina obligation `valid_ptr arrl[1]`
  p++;// generates obligation `valid_ptr arrl[2]`
  p++;// generates obligation `valid_ptr arrl[3]`
  p++;// generates obligation `valid_ptr arrl[4]`: NOT PROVABLE`
}
```
In C++, it is valid to have a pointer point one past the end of an array, but you must not dereference it.
It is undefined behavior to increment a pointer past the "one past the end" position, EVEN IF YOU DONT DEREFERENCE THAT POINTER.
The `arrayR` definition has the `valid_ptr` assertion for just the index last the last one and not for the previous indices because those assertions can be derived. For example, we can derive  `valid_ptr (p .[ uint ! 2 ])` from `valid_ptr (p .[ uint ! 3 ])`. Also, `valid_ptr` assertions are `Persistent`. Persistent separation logic assertions can be freely duplicated (not that `valid_ptr` doesnt mean that the pointer is live, it just prevents UB pointer increments):

```coq
Lemma valid_ptr_dup (p:ptr) : valid_ptr p |-- valid_ptr p ** valid_ptr p.
Proof using. go. Qed.
```

Below is a more concrete example illustrating the use of `arrayR`:

```coq
  Example arrayR3 (p:ptr) (n1 n2 n3: Z) (q: Qp):
    p |-> arrayR uint (fun i:Z => primR uint q i) [n1;n2;n3]
      -|- ( valid_ptr (p .[ uint ! 3 ])
              ** p |-> primR uint q n1
              ** p .[ uint ! 1 ] |-> primR uint q n2
              ** p .[ uint ! 2 ] |-> primR uint q n3).
  Proof. ... Qed.
```
Using `arrayR` we can conveniently specify functions receiving/returning arrays, e.g.:

```c++
uint gcdl (uint * nums, uint length) {
    uint result=0;
    for (uint i=0; i<length; i++) {
        result=gcd(result, nums[i]);
    }
    return result;
}
```
It spec is:
```gallina
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with
  (   \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)}
             numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "length" (Vint (length l))
      \post [Vint (Stdlib.Lists.List.fold_left Z.gcd l 0)] emp).
```


`Stdlib.Lists.List.fold_left`, `Z.gcd` are all Gallina functions from the standard library, independent of C++:

```gallina
  Example fold_left_gcd (n1 n2 n3: Z) :
    Stdlib.Lists.List.fold_left Z.gcd [n1;n2;n3] 0 =  Z.gcd (Z.gcd (Z.gcd 0 n1) n2) n3.
  Proof. reflexivity. Qed.
```

Many C++ specs connect C++ code to their pure versions in Gallina, which already have plenty of correctness properties proved in the standard library. Sometimes, new Gallina functions need to be defined to write the spec of C++ functions and in such cases, one needs to worry that the Gallina functions used in the spec themselves dont have bugs. These concerns can be alleviated by proving correctness properties about the new Gallina functions. 

### Struct/Class field offsets
Similarly, consider the following struct

```c++
struct Node {
    Node(Node *next, int data) : next_(next), data_(data) {}

    Node *next_;
    int data_;
};
```

Our semantics axiomatizes the following to refer to the offset of a struct/class field:

```gallina
bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM._field : bluerock.lang.cpp.syntax.core.name -> bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.offset
```

The first argument, bluerock.lang.cpp.syntax.core.name, is supposed to be the name of the field.
We have custom notations (in scope `%cpp_name`) defined to parse string constants in regular double quotes as `bluerock.lang.cpp.syntax.core.name`.
As an example, if `nbase:ptr` is the memory location where a struct object lives, 
`_offset_ptr nbase (_field "::Node::data_"%cpp_name)` is the memory location where its `::data_` field lives.
We don't need to explicitly write the `%cpp_name` part as Coq has been told (via the `Arguments` directive) that the argument of `_field` should be parsed in the `%cpp_name` notation scope.

As with arrays, we have convenience notations to make gallina field offsets look somewhat like C++:
```coq
  Example notation_example2 (nbase:ptr) :
    nbase ,, _field "::Node::data_" = _offset_ptr nbase (_field "::Node::data_").
  Proof using. reflexivity. Qed.
```
We have an even more concise notation specialized to `_field` offsets:
```coq
  Example notation_example3 (nbase:ptr) :
    nbase ., "::Node::data_" = _offset_ptr nbase (_field "::Node::data_").
  Proof using. reflexivity. Qed.
```

Just we defined `arrayR` to describe ownership of entire arrays in `\pre` and `\post` conditions, we can define `NodeRf`:

```gallina
Definition NodeRf  (q: cQp.t) (data: Z) (nextLoc: ptr) : ptr -> mpred :=
  fun (nodebase: ptr) =>
  nodebase ,, _field "Node::data_" |-> primR "int" q (Vint data)
  ** nodebase ,, _field "Node::next_" |-> primR "Node*" q (Vptr nextLoc)
  ** nodebase |-> structR "Node" q.
```


`structR "Node" q` asserts that the intrinsic identiy of the object is `Node`. This assertion is used in our C++ semantics to rule out unsafe dynamic casts. In general, `structR` also denotes the ownership of the padding in the objects if there is any: `memcpy` needs ownersip of the padding as well. Also, the destructor proof requires returning full ownersips of not just all the fields but also the `structR "Node" 1`.
Now we can use `NodeRf` in specs of `Node` functions, e.g.

```c++
void incdata(Node * n){
  n->data_++;
}
```

Its spec is

```gallina
  cpp.spec "incdata(Node *)"  as incd_spec with (
     \arg{nbase} "n" (Vptr nbase)
     \pre{data nextLoc} NodeRf 1 data nextLoc nbase
     \pre [| data < 2^31 -1 |] (* to prevent overflow. overflow in signed addition is undefined behaviour *)
     \post NodeRf 1 (1+data) nextLoc nbase
      ).
```

However, we can write the above spec in an equivalent but more idiomatic way where we use the `|->` (points_to) notation just as we do for primitive C++ types like `int`.
First, note that `Rep` is morally equivalent to `ptr -> mpred`, so the return type of `NodeRf` can just be `Rep`.
Also, we have lifted the separation logic operators like `**`, `-*`, `//\\` to also work on `Rep` in the usual pointwise way.
Also, we have `_offsetR : offset → Rep → Rep` and `|->` is overloaded to mean `_offsetR` when its left hand side is `offset` instead of `ptr`. 
`_offsetR` is just a convenience defined to satisfy the following property:

```coq
Lemma _at_offsetR:
  ∀ (p : ptr) (o : offset) (r : Rep),
    (p |-> o |-> r) -|- (p ,, o |-> r).
```


With these tools, `NodeRf` can be dedfined more concisely, but equivalently as follows to return a `Rep` instead of a `ptr->mpred`.

```gallina
Definition NodeR  (q: cQp.t) (data: Z) (nextLoc: ptr): Rep :=
  _field "Node::data_" |-> primR "int" q (Vint data)
  ** _field "Node::next_" |-> primR "Node*" q (Vptr nextLoc)
  ** structR "Node" q.
```
One advantage is that we can now use NodeR with the standard `|->` (points_to) notation just like we do for primitive types:

```gallina
  Lemma nodeRequiv (base:ptr) (data:Z) (nextLoc: ptr) (q: cQp.t):
    NodeRf q data nextLoc base -|- base |-> NodeR q data nextLoc.
  Proof using. unfold NodeRf, NodeR. iSplit; go. Qed.
```


```gallina
  cpp.spec "incdata(Node *)"  as incd_spec_idiomatic with (
     \arg{nbase} "n" (Vptr nbase)
     \pre{data nextLoc} nbase |-> NodeR (cQp.mut 1) data nextLoc
     \pre [| data < 2^31 -1 |]
     \post nbase |-> NodeR (cQp.mut 1) (1+data) nextLoc
   ).
```
Because `incdata` modifies the object, it requires the full ownership as a precondition. Functions that do not modify or destruct the object can just get away with any fraction `q` in the precondition.

Structs and classes can have methods. Method specs are exactly like function specs
except that when `cpp.spec` determines that the C++ item being specified is a method/constructor/destructor (and not a regular function), it expects the last argument (just after `with`) to be a function taking the `this` memory location as argument. For example, consider the following `incdataM` method:

```c++
struct Node {
    Node(Node *next, int data) : next_(next), data_(data) {}

    Node *next_;
    int data_;
    void incdataM(){
      this->data_++;
    }
  
};
```

Here is a spec of `incdataM`:
```gallina
  cpp.spec "Node::incdataM()"  as incdata_method_Spec with (fun (this:ptr) =>
     \pre{data nextLoc} this |-> NodeR (cQp.mut 1) data nextLoc
     \pre [| data < 2^31 -1 |]  
     \post this |-> NodeR (cQp.mut 1) (1+data) nextLoc
   ).
```

Similarly, here is the spec of the `Node` constructor:

```coq
  cpp.spec "Node::Node(Node*, int)" as node_constr with (fun (this:ptr) =>
     \arg{nextLoc} "n" (Vptr nextLoc)
     \arg{data} "n" (Vint data)
     \post this |-> NodeR (cQp.mut 1) data nextLoc
    ).

```
Constructors typically return full(1) ownership of the object. This ownership can then be split into multiple pieces, e.g.  to share with different threads.
Conversely, destructor specs typically take the full ownership as precondition and dont return any ownership of the object in the postcondition:

```gallina
  cpp.spec "Node::~Node()" as node_destr with (fun (this:ptr) =>
    \pre{(data:Z) (nextLoc:ptr)} this |-> NodeR (cQp.mut 1) data nextLoc
    \post emp).
```

We have registered `cQp.mut` as a coercion so that we can write just `1` instead of `(cQp.mut 1)` above, but coercions should be avoided when you are trying to debug a compile error.

### base/derived class offsets

`_base` represent the offset of the base class subobject, as illustrated in the example below 
```gallina
  Example derivedToBaseOffset: offset := _base  "std::atomic<int>" "std::__atomic_base<int>".
```
The first argument is the name of the class of the current object. The second argument is the name of the base class.
`_derived` is the inverse operation, illustrated by the following example:
```gallina
  Example baseToDerivedOffset: offset := _derived  "std::__atomic_base<int>" "std::atomic<int>".
```
We have the following equations (`_derived` := `o_derived σ` (notation) and `_base` := `o_base σ` (notation)) formalizing the inverseness:

```
o_derived_base:
  ∀ (σ : genv) (p : ptr) (base derived : name), directly_derives σ derived base → p ,, o_derived σ base derived ,, o_base σ derived base = p
o_base_derived:
  ∀ (σ : genv) (p : ptr) (base derived : name), directly_derives σ derived base → p ,, o_base σ derived base ,, o_derived σ base derived = p
```

`_base` can be used to get the offsets of subclass fields when writing `Rep` predicates of derived classes.
For example, consider the following dummmy c++ class:
```c++
class foo: public bar {
  int x;
  }
```
Its Rep predicate will look like:
```gallina
Definition fooR (q:cQp.t) (bm: BarModel) (xv:Z) :=
  _base "foo" "bar" |-> barR q bm
  ** _field "foo::x" |-> primR "int" q (Vint xv).
```

### Fractional ownership of arrays/classes
For `Rep`s of primitive types (e.g. `int`), our semantics already defines the significance of fractions. 
A thread owning `mloc |-> primR "int" (cQp.mut q) v` can depend on the value of the location `mloc` being `v`: because the thread has a q (0<q) fraction, 
no other thread can have 1 fraction and thus no other thread can write to `mloc`.
We (not the semantics) get to define `Rep`s of Classes and thus we get to decide whether the `Rep` predicates even takes a fraction (`cQp.t`) argument and 
the significance of the fraction.
A thread `base |-> NodeR (cQp.mut q) data nextLoc`, can rely on the Node object to not change and not be destructed: because the functions/methods that change the object (e.g. `incdataM`) require 1 ownership, as does the destructor.
Given the `base |-> NodeR (cQp.mut q) data nextLoc`


```coq
Lemma nodeRsplit (q1 q2: Qp) data nextLoc (base:ptr):
 base |-> NodeR (cQp.mut (q1+q2)) data nextLoc -|- base |-> NodeR (cQp.mut q1) data nextLoc ** base |-> NodeR (cQp.mut q2) data nextLoc.
```



### Logical Abstraction with Rep Predicates for classes

`NodeR` specs provided no abstraction: it just exposed the 2 C++ fields as 2 Gallina arguments of their corresponding Gallina types. Many `Rep` predicates provide a much more pure/clean/mathematical/high-level logical abstraction of C++ fields. For example, consider linked lists:

```c++
typedef Node * List;
```

We can define a Gallina `Rep` for `ListR` in a way that makes the users of the spec treat the linked list as just a mathematical/Gallina list of numbers, without having to deal with the complicated ways the list is laid out in memory:

```gallina
  Fixpoint ListR (q : cQp.t) (l : list Z) : Rep :=
    match l with
    | [] => nullR
    | hd :: tl =>
        Exists (tlLoc: ptr),
          NodeR q hd tlLoc
          ** pureR (tlLoc |-> ListR q tl)
    end.
```

Some example lemmas to illustrate `ListR`:
```coq
  Example listRUnfold (q:Qp) (head:ptr): head |-> ListR q [4;5;6] |--
    Exists node5loc node6loc,
       head |-> NodeR q 4 node5loc
       ** node5loc |-> NodeR q 5 node6loc
       ** node6loc |-> NodeR q 6 nullptr
       (* ** [| node5loc <> node6loc <> head|] *).
  Proof using. work. unfold NodeR.  go. Qed.

  Example nullReq (p: ptr): p |-> nullR |-- [| p = nullptr |].
  Proof. go. Qed.
```

Now we can write specs of linked list functions, e.g.:

```c++
List reverse(List l) {
  List prev = nullptr;
  List next = nullptr;
  while (l != nullptr) {
    next = l->next_;
    l->next_ = prev;
    prev = l;
    l = next;
  }
    return prev;
}
```

Spec:

```gallina
  cpp.spec "reverse(Node*)" as reverse_spec with
    (\arg{lp} "l" (Vptr lp)
     \pre{l: list Z} lp |-> ListR 1 l
     \post{r}[Vptr r] r |-> ListR 1 (List.rev l)).
```
The spec essentially says that the c++ implementation should behave like the Gallina `List.rev` function for which we have several properties proven in the Coq standard library.

When writing `Rep` predicates, carefully think whether some C++-related details can be abstracted away. Avoid `Rep` predicates that just expose all class fields unless the C++ class really provides no abstraction and is just a thin wrapper.



## Specs/reps of templated classes

The above strategy can be used to write specs and Rep predicates of *concrete* instantiations of templated classes/functions. However, in such cases, it is often better to write more generic spec and Rep predicates (to avoid duplication). As a simplest example, consider `std::optional`. We can write its `Rep` predicate generically as follows:


```gallina


  (* this is the offset at which the value of the Some type is stored in case this optional is a Some. this is some implementation-defined offset, typically some base class offset(s) followed by some field offset. *)
  Definition opt_somety_offset (somety:type): offset. Proof. Admitted.

(* this is the offset at which a bool is stored, indicating whether this is a Some or None. this is some implementation-defined offset, typically some base class offset(s) followed by some field offset. *)
  Definition opt_engaged_offset (somety:type): offset. Proof. Admitted.

  
  Definition optionR {SomeTyModel:Type} (somety: bluerock.lang.cpp.syntax.core.type)
    (someTyRep: SomeTyModel -> Rep) (q:Qp) (o: option SomeTyModel): Rep :=
    structR (Ninst "std::optional" [Atype somety]) (cQp.mut q) **
    match o with
    | None => opt_engaged_offset somety |-> boolR (cQp.mut q) false
    | Some b => opt_somety_offset somety |-> someTyRep b
                ** opt_engaged_offset somety |-> boolR (cQp.mut q) true
    end.

```

`somety:type` is a C++ type and `SomeTyModel` is supposed to be the Gallina model of `somety`.
The `Rep` being defined will be for `std::optional<somety>`.
The `Rep` predicate `someTyRep` is a parameter defining how a mathematical/Gallina `SomeTyModel` is laid out in memory as data of c++ type `somety`.

`(Ninst "std::optional" [Atype somety])` of type `bluerock.lang.cpp.syntax.core.name` illustrates that even though we were able to write C++ names of type as string-like literals, names have structure and the notation mechanism parses those into the structure.
names (`bluerock.lang.cpp.syntax.core.name`) are defined mutually inductively with types, expressions, statements. Below is a heavily elided glimples of the big block of mutually inductive definitions:

```
Notation name := name'

Inductive name' : Set :=
    Ninst : name → list temp_arg → name
  | Nglobal : atomic_name → name
  | Ndependent : type → name
  | Nscoped : name → atomic_name → name
  | Nunsupported : string → name
  with temp_arg' : Set := ...
  with type' : Set :=
    Tparam : ident → type
  | Tptr : type → type
  | Tref : type → type
  | Tnum : int_rank → signed → type
  | Tchar_ : char_type → type
  | Tvoid : type
  | Tarray : type → N → type
  | Tnamed : name → type
  | Tenum : name → type
  | Tfunction : function_type_ type → type
  | Tbool : type
  | Tmember_pointer : type → type → type
  ...
  with Expr' : Set :=
    Eparam : ident → Expr
  | Evar : localname → type → Expr
  | Eglobal : name → type → Expr
  | Estring : literal_string.t → type → Expr
  | Eint : Z → type → Expr
  | Ebool : bool → Expr
  | Eunop : UnOp → Expr → type → Expr
  | Ebinop : BinOp → Expr → Expr → type → Expr
  | Ederef : Expr → type → Expr
  ....
  with Stmt' : Set :=
    Sseq : list Stmt → Stmt
  | Sdecl : list VarDecl → Stmt
  | Sif : option VarDecl → Expr → Stmt → Stmt → Stmt
  | Sif_consteval : Stmt → Stmt → Stmt
  | Swhile : option VarDecl → Expr → Stmt → Stmt
  ...
  with VarDecl' : Set :=...
  with BindingDecl' : Set :=...
  with Cast' : Set :=...
  .
```

We can now instantiate `optionR` to define Rep predicates of various instantiations of `std::optional`:

```gallina
  (* Rep predicate for `std::optional<int>` *)
  Definition optionalIntR  (q:cQp.t) (o: option Z) : Rep  :=
    @optionR Z "int" (fun (z:Z) => primR "int" q (Vint z)) q o.

  (* Rep predicate for `std::optional<List>` *)
  Definition optionalListR  (q:cQp.t) (o: option (list Z)) : Rep  :=
    @optionR (list Z) "Node*" (fun (l: list Z) => ListR q l) q o.
```
(C++ type aliases should be unfolded when refering to C++ names in galline: so we write `Node*` not `List`.)

Now, we can use `cpp.spec` to write specs of methods of instantiations of `std::optional`, e.g.:

```gallina
   cpp.spec "std::optional<int>::value()" as value_int_spec with
       (fun (this:ptr) =>
       \prepost{(z : Z) (q : cQp.t)} this |-> optionalIntR q (Some z)
       \post[Vptr (this ,, opt_somety_offset "int")] emp).
```
The `value()` method returns a reference to the stored integer, thus the spec returns the memory location where the int is stored.
Unfortunately, `cpp.spec` can only be used to write specs of fully instantiated function/method names. However, as mentioned above, `cpp.spec` is just an elpi helper that figures out the types of methods/functions and then uses the underlying `specify` assertion.
We can directly write generic specs by using `specify`:


```
   Definition value ty T :=
    specify
    {|
      info_name :=
        Nscoped (Ninst "std::optional" [Atype ty])
          (Nfunction function_qualifiers.Ncl "value" []);
      info_type :=
        tMethod (Ninst "std::optional" [Atype ty]) QC "const evmc::address&" []
    |}
    (λ this : ptr,
       \prepost{(R : T → Rep) (t : T) (q : Qp)} this |-> optionR ty R q (Some t)
         \post[Vptr (this ,, opt_somety_offset ty)] emp).
		 
  Definition has_value ty T :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "std::optional" [Atype ty])
          (Nfunction function_qualifiers.Nc "has_value" []);
      info_type := tMethod (Ninst "std::optional" [Atype ty]) QC "bool" []
    |}
    (λ this : ptr,
       \prepost{(R : T → Rep) (o : option T) (q : Qp)} this |-> optionR ty R q o
       \post[Vbool (isSome o)]
                emp).
```

The first argument of `specify` is of type `sym_info`. Writing it directly by hand (especially the `info_type` field) can be problematic.
You can first use `lookupSymbolByFullName` to get the type of a concrete.
```coqquery
Compute (lookupSymbolByFullName module "std::optional<unsigned long>::has_value() const").
```
response:
```
     = Some
         {|
           info_name := "std::optional<unsigned long>::has_value() const"; info_type := tMethod "std::optional<unsigned long>" QC "bool" []
         |}
  : option sym_info
```

Here, `module:translation_unit` is the AST in gallina of the C++ file being specified/verified.
## Spec Examples
TODO

## finding existing specs in the context

You can use the regular Coq `Search` vernacular to find specs of C++ function of a given fully qualified C++ name exists in the current context. This works because `cpp.spec` declares an instance of the typeclass
`bluerock.auto.cpp.database.spec.SpecFor.C`.
More concretely, the above spec (`foo_spec`) declares a typeclass instance of type `bluerock.auto.cpp.database.spec.SpecFor.C "foo()" foo_spec`. 
Thus, you can issue the following query to find out all the available specs for `foo()`. 
The name (here, `foo()`) must be a fully qualified C++ name.

```coqquery
Search (bluerock.auto.cpp.database.spec.SpecFor.C "foo()" _).
```

## querying AST of C++ functions/classes

Before writing `Rep` predicates of C++ classes and specs of C++ methods/functions, it is useful to view their definitions.
You can do that by issuing a coqquery code block response as you do for Coq queries.
You cannot directly print `module:translation_unit` as the output is huge and likely beyond your context-size limit.
So, we have defined functions to lookup in it ASTs of specific classes/methods/functions.
```gallina
(* lookup the body of a function or a method of nm, which must be a fully qualified C++ name *)
Definition lookup_function
           (tu : translation_unit) (nm : name)
  : option (sum Func Method) :=
  match symbols tu !! nm with
  | Some (Ofunction f) => Some (inl f)
  | Some (Omethod m)   => Some (inr m)
  | _                  => None
  end.


(* lookup a Struct/Class declaration and its methods by fully‐qualified name *)
Definition lookup_struct
           (tu: bluerock.lang.cpp.syntax.translation_unit.translation_unit)
           (nm: bluerock.lang.cpp.syntax.core.name)
  : option ( bluerock.lang.cpp.syntax.decl.Struct
             * list ( bluerock.lang.cpp.syntax.core.obj_name
                      * bluerock.lang.cpp.syntax.decl.Method ) ) :=
  match bluerock.lang.cpp.syntax.translation_unit.types tu !! nm with
  | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st) =>
      let syms := bluerock.lang.cpp.syntax.translation_unit.symbols tu in
      let mds :=
        List.fold_right
          (fun entry acc =>
             match select_method_of_class nm entry with
             | Corelib.Init.Datatypes.Some md => md :: acc
             | Corelib.Init.Datatypes.None => acc
             end)
          []
          (symbol_table_to_list syms) in
      Corelib.Init.Datatypes.Some (st, mds)
  | _ =>
      Corelib.Init.Datatypes.None
  end.
```
Here is are some example usages:

```coqquery
Compute (lookup_struct module "monad::BlockState").
Compute (lookup_function module "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const").
```

To prevent the response to your queries exceeding your context limit, the bodies of the methods are erased by the following method (`erase_body`) even when they are available in the `translation_unit`. You can use `lookup_function` to query their bodies:

```gallina
Definition AvailableButErased: option (OrDefault Stmt).
  exact None.
Qed. (* Qed instead of Defined makes it opaque so Compute wont unfold it to None *)

Definition erase_body (m:Method) : Method :=
  match m_body m with
  | Some (UserDefined _) =>  m &: _m_body .= AvailableButErased
  | _ => m
  end.
```

The names in the AST are normalized by the clang-AST visitor so they are normalized even in the C++ AST in Coq. For example, we wrote the spec of the linked list reverse function as:

```gallina
  cpp.spec "reverse(Node*)" as reverse_spec with
    (\arg{lp} "l" (Vptr lp)
     \pre{l: list Z} lp |-> ListR 1 l
     \post{r}[Vptr r] r |-> ListR 1 (List.rev l)).
```
even though the c++ method definition was

```c++
List reverse(List l) {...
```

This is because the AST in Coq has the following C++ type alias unfolded everywhere:
```c++
typedef Node * List;
```

The lookup functions above (e.g. `lookup_struct`) and `cpp.spec` expect names with type aliases unfolded. To help with that, we have the following functions that take a C++ fully qualified name (where type aliases may be folded) as a `PrimString.string` and returns a `core.name` (structured name) or `core.type` where the type aliases of the `translation_unit` are all unfolded everywhere.


```gallina
bluerock.lang.cpp.syntax.name_notation.parser.parse_name_with
     : bluerock.lang.cpp.syntax.translation_unit.translation_unit
       → Corelib.Strings.PrimString.string
         → Corelib.Init.Datatypes.option
             bluerock.lang.cpp.syntax.core.name

bluerock.lang.cpp.syntax.name_notation.parser.parse_type_with
     : bluerock.lang.cpp.syntax.translation_unit.translation_unit
       → Corelib.Strings.PrimString.string
         → Corelib.Init.Datatypes.option
             bluerock.lang.cpp.syntax.core.type
```

For example, 
`parser.parse_name_with module "reverse(List)"` computes to 
`Some "reverse(Node*)"%cpp_name`

## source definitions of C++ functions/classes
As mentioned above, the AST in Coq has type aliases normalized. 
Also, default arguments of templates are inserted.
Also, source code comments are missing.
Together, these may make it hard to understand the code and how to write the specs.
So, we have implemented the `CppDefnOf cppfqn` query to get you the source code snippet corresponding to the c++ class/function whose c++ fully qualified name is `cppfqn`.
Here is an example valid response that you can issue:

```coqquery
Print nat.
CppDefnOf monad::Account
Search (genv -> genv).
```

Even though CppDefnOf is not technically a Coq query and the elisp-loop responding to you actually does not implement the  `CppDefnOf` queries via coqtop and uses clangd-lsp instead, you can issue `CppDefnOf` queries as if it were a Coq query.
Reading the actual source code and comments is very likely to give you some completementary information beyond the AST. Thus you should always issue a `CppDefnOf` together with `Compute (lookup_struct module "...")` or `Compute (lookup_function module "...")`.
Note that lookup_function needs a full name, e.g. `reverse(Node*)` and not just `reverse`. However, `CppDefnOf` goes to clangd-lsp and can can accept just `reverse`.



## Common mistakes in specs:

### too much ownership
Let's revisit the `foo` function:
```c++
void foo() {
    y=0;
    y=x+1;
}
```
Here is a suboptimal spec:
```gallina
Notation uint := "unsigned int"%cpp_type.

  cpp.spec "foo()" as foo_spec with (
        \pre{xv:Z} _global "x" |-> primR uint (cQp.mut 1) xv (* forall xv .. *)
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N ** _global "x" |-> primR uint (cQp.mut (1/2))  xv
      ).
```
The first `\pre` asserts full ownership of `x`, even though the function only reads `x`. So a stronger spec is to weaker the `\pre` to allow any `q` fractional ownership of `x`:

```gallina
    cpp.spec "foo()" as foo_spec with (
        \prepost{(xv:Z) (q:Qp)} _global "x" |-> primR uint (cQp.mut q) xv
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N
      ).
```


### missing or too-weak precondition
Carefully review the code to see which variables are being read or written. If the function calls other functions, search/review the preconditions in the callee's spec.
For example, the following spec of `foo` is wrong because its precondition does not assert any ownership of `x` thus the function's proof would get stuck at the point it reads the variable `x`

```gallina
    cpp.spec "foo()" as foo_spec with (
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N
      ).
```

The following spec is wrong because the precondition only asserts some `qy` fractional ownership of `y`, which is not sufficient for writing to `y`.

```gallina
    cpp.spec "foo()" as foo_spec with (
        \prepost{(xv:Z) (q:Qp)} _global "x" |-> primR uint (cQp.mut q) xv
        \pre{(qy:Qp)} _global "y" |-> anyR uint (cQp.mut qy)
        \post _global "y" |-> primR uint (cQp.mut qy) ((xv+1) `mod` (2^32))%N
      ).
```


### missing postcondition
Ownership is only created at constructor calls and destructed at destructor calls.
Every resource passed to a function as a part of its precondition must either be returned back (after possible modifications of the value), or destructed, or passed to some other (possibly new) thread (e.g. via signals/semaphores/fork). Functions can also rearrange ownersip: e.g. some ownersip pience can move from being attached to a function argument to some other argument (e.g. for functions that insert the argument into a data structure).

For example, the following spec is wrong because it does not return back the ownerhip of `x`:
```gallina
    cpp.spec "foo()" as foo_spec with (
        \pre{(xv:Z) (q:Qp)} _global "x" |-> primR uint (cQp.mut q) xv
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) ((xv+1) `mod` (2^32))%N
      ).
```

### quirks of `cpp.spec`:

#### type required for `this`:
for method/constructor/destructor specs, the `this` argument must have a type annotation, as in the example as below:

```gallina
  cpp.spec "Node::Node(Node*, int)" as node_constr with (fun (this:ptr) =>
     \arg{nextLoc} "n" (Vptr nextLoc)
     \arg{data} "n" (Vint data)
     \post this |-> NodeR (cQp.mut 1) data nextLoc
    ).
```

Replacing `(fun (this:ptr) => ...)` by `(fun this => ...)` will cause issues with parsing the spec notation.
This parsing is done by custom Elpi code

####  `\post` quirks
Every spec can have at most one `\post`. multiple conjuncts can be compbined using `**`.
Also, if you need existentially quantify something in the postcondition, there are 2 ways to do it.
For example, consider the following spec of `twice`:

```gallina
  cpp.spec "twice(unsigned int)" as twice_weak_spec2 with (
     \arg{xv:Z} "x" (Vint xv)
     \post{xvfinal} [Vint xvfinal] [| xvfinal `mod` 2 = 0 |]
      ).
```
Just to illustrate existential quantifications in `\post`, the above spec can be equivalently written as:

```gallina
  cpp.spec "twice(unsigned int)" as twice_weak_spec2 with (
     \arg{xv:Z} "x" (Vint xv)
     \post{(xvfinal xvfinalhalf : Z)} [Vint xvfinal] [| xvfinalhalf * 2 =  xvfinal|]
      ).
```
However, this spec is not idiomatic. The last argument of `\post` is of type `mpred` and and thus supports existential quantification. Thus the existential quantification over `xvfinalhalf` can be moved to the last argument:

```gallina
  cpp.spec "twice(unsigned int)" as twice_weak_spec3 with (
     \arg{xv:Z} "x" (Vint xv)
     \post{(xvfinal : Z)} [Vint xvfinal] (Exists xvfinalhalf, [| xvfinalhalf * 2 =  xvfinal|])
      ).
```
Note the variables existentially quantified in the last argument are NOT in scope in the previous argument (square bracket denoting the return value). Thus, we can NOT move the quanification over `xvfinal`, which is mentioned in the return value, to the last argument to colocate it with the quantification over `xvfinalhalf`.
Note that the (existential) variable quantifications in the curly brace just after `\post` is scope in the next argument (return value). Typically, in the curly braces after `\post`, we ONLY quantify the variables that are mentioned in the return value. In fact, `cpp.spec` has a quirk that if there is no return value (e.g. the function returns value, in which case, the square bracket is entirely omitted), there must be no curly brace.


## Common mistakes in Rep predicates:

### missing `structR`
A rep predicate of a class foo should include the `structR foo q` conjunct (in rare cases, `structR foo 1` when the objects of the class are not supposed to be shared at all between threads).

### incomplete field names:
field names in `_field` whould be fully qualified. In particular, the fully qualified name of the class should be a prefix.
For example, use `_field "Node::next_"` not `_field "next_"`.

### use of anyR in Rep predicates
Rep predicates typically describe a fully constructed object. so `anyR` typically does not belong in a `Rep` predicate, because `anyR` allows the memory location to be uninitialized. If the value of a field is truly an implementation detail, you pass existentially qualified arguments to the Rep predicate of the type of the field.
If the field's value is NOT an implementation detail for the clients of the class, the field's value should be tied to something in the Gallinal model of the object. Sometimes, you may need to add additional Gallina-model arguments to the Rep predicate. Sometimes, you may need to Gallina model types, although try very hard to reuse existing types for which existing theories exist. When it makes sense, model arguments into Records, e.g. arguments that are related to each other.
Monad DB: Two‑Layer Architecture & Client Patterns

This document collects the key takeaways from our recent deep‑dive into the `monad::Db` façade, its underlying MPT engine, its concrete implementations, and how the various sub‑systems (execution, consensus, RPC, StateSync) drive and read it.

---

## 1. Two‑Layer DB Architecture

Monad’s state persistence is implemented in two layers:

| Layer                            | Namespace       | Responsibilities                                                                              |
| :--------------------------------| :---------------| :---------------------------------------------------------------------------------------------|
| **Raw MPT engine**               | `monad::mpt::Db`| Low‑level Merkle‑Patricia‑Trie store (async I/O, lock‑free ring buffer for historic versions). |
| **High‑level blockchain façade**  | `monad::Db`     | Blockchain execution API: read/write account/storage/code, commit/finalize blocks, roots.     |

The high‑level façade (in `libs/execution/src/monad/db`) delegates all the heavy lifting to the raw MPT engine (`libs/db/src/monad/mpt`), avoiding duplication and focusing on blockchain semantics.

---

## 2. Raw MPT Interface: `monad::mpt::Db`

Located in **`libs/db/src/monad/mpt/db.hpp`**, the `mpt::Db` abstraction provides:

- **RODb**: read‑only trie (for RPC & StateSync clients).  
- **Db**: read‑write trie (for execution & consensus), with on‑disk or in‑memory backends and async I/O.

Core operations include:

- `get(prefix, version)`, `get_data(prefix, version)` → fetch leaf or root‑offset  
- `upsert(UpdateList, version)` → apply state/code/transaction updates, write new root  
- `copy_trie(src_ver, src_pref, dst_ver, dst_pref)` → snapshot‑copy proposal→finalized  
- `update_finalized_block(version)`, `update_verified_block(version)`, `update_voted_metadata(version, round)` → metadata ring  
- `get_latest_*` → read current ring watermarks  
- versioned traversals (`traverse`) for RPC/state‑sync dumps

---

## 3. High‑Level Façade: `monad::Db`

In **`libs/execution/src/monad/db/db.hpp`**, `monad::Db` defines the execution engine’s view of state:

```cpp
struct Db {
  // ── Read queries ──────────────────────────────────────
  virtual std::optional<Account>         read_account(Address) = 0;
  virtual bytes32_t                      read_storage(Address, Incarnation, bytes32_t const&) = 0;
  virtual std::shared_ptr<CodeAnalysis> read_code(bytes32_t const&) = 0;

  // ── Root queries ──────────────────────────────────────
  virtual BlockHeader    read_eth_header()    = 0;
  virtual bytes32_t      state_root()        = 0;
  virtual bytes32_t      receipts_root()     = 0;
  virtual bytes32_t      transactions_root() = 0;
  virtual std::optional<bytes32_t> withdrawals_root() = 0;

  // ── Wrap consensus callbacks ──────────────────────────
  virtual void set_block_and_round(uint64_t, std::optional<uint64_t> = std::nullopt) = 0;
  virtual void finalize(uint64_t, uint64_t)                                       = 0;
  virtual void update_verified_block(uint64_t)                                     = 0;
  virtual void update_voted_metadata(uint64_t, uint64_t)                           = 0;

  // ── Apply an executed block ─────────────────────────
  virtual void commit(StateDeltas const&, Code const&, MonadConsensusBlockHeader const&,
                      std::vector<Receipt> const& = {}, std::vector<std::vector<CallFrame>> const& = {},
                      std::vector<Address> const& = {}, std::vector<Transaction> const& = {},
                      std::vector<BlockHeader> const& = {},
                      std::optional<std::vector<Withdrawal>> const& = std::nullopt) = 0;
};
```

### Implementations

| Class       | File(s)                           | Role                                        |
| :---------- | :-------------------------------- | :-------------------------------------------|
| **TrieDb**  | `trie_db.hpp/cpp`                 | RW trie delegator → `mpt::Db` (execution)     |
| **TrieRODb**| `trie_rodb.hpp/cpp`               | RO trie delegator → `mpt::Db` (RPC, StateSync) |
| **DbCache** | `db_cache.hpp/cpp`                | In‑process LRU cache wrapper (RPC + local)   |
| **StateSync server context** | `statesync_server_context.hpp/cpp` | `monad::Db` wrapper that instruments commit/finalize to capture deletions for StateSync server |

### How TrieDb encodes EVM tables into the raw MPT

`TrieDb` uses a fixed one‑byte “nibble” per EVM table, concatenated onto the proposal/finalized prefix, so that all state, storage, code, receipts, transactions, headers, ommers, etc., live in disjoint subtries.  The nibble constants and prefix definitions live in `util.hpp`:

```cpp
// libs/execution/src/monad/db/util.hpp:L86-L97
inline constexpr unsigned char STATE_NIBBLE       = 0;
inline constexpr unsigned char CODE_NIBBLE        = 1;
inline constexpr unsigned char RECEIPT_NIBBLE     = 2;
inline constexpr unsigned char TRANSACTION_NIBBLE = 3;
inline constexpr unsigned char BLOCKHEADER_NIBBLE = 4;
inline constexpr unsigned char WITHDRAWAL_NIBBLE  = 5;
inline constexpr unsigned char OMMER_NIBBLE       = 6;
inline constexpr unsigned char TX_HASH_NIBBLE     = 7;
inline constexpr unsigned char BLOCK_HASH_NIBBLE  = 8;
inline constexpr unsigned char CALL_FRAME_NIBBLE  = 9;
inline constexpr unsigned char BFT_BLOCK_NIBBLE   = 10;
```【F:libs/execution/src/monad/db/util.hpp†L86-L97】

```cpp
// libs/execution/src/monad/db/util.hpp:L114-L117
inline constexpr unsigned char PROPOSAL_NIBBLE = 0;
inline constexpr unsigned char FINALIZED_NIBBLE = 1;
inline mpt::Nibbles const proposal_nibbles  = mpt::concat(PROPOSAL_NIBBLE);
inline mpt::Nibbles const finalized_nibbles = mpt::concat(FINALIZED_NIBBLE);
```【F:libs/execution/src/monad/db/util.hpp†L114-L117】

On `commit()`, `TrieDb` switches its **prefix** to `proposal_prefix(round)` (using the round number) and then writes every EVM table under that proposal prefix plus its table nibble and key bytes.  Upon `finalize()`, the entire proposal subtrie is copied into the immutable `finalized_nibbles` subtrie so that snapshot remains frozen.

---

## 4. Clients & Access Patterns

| Client                | Calls                             | Mutates? | Reads Prefix          | Writes Prefix           |
| :---------------------| :---------------------------------| :------- | :---------------------| :-----------------------|
| Execution RunLoop     | commit, finalize, update_*        | ✓        | proposal/finalized     | proposal → finalized    |
| Consensus WAL Replay  | (→ runloop)                       | ✓        | proposal              | proposal                |
| StateSync Server      | RO queries + instrumentation      | ⚠ only instrumentation | finalized_nibbles      | N/A                     |
| StateSync Client      | commit/finalize (ingest data), verify roots | ✓        | client‐side RO prefix | ingested upserts/deletions |
| RPC Server            | read_* + traverse queries         | ✗        | any (proposal/finalized) | N/A                    |
| CLI (`monad_cli`)     | read_* + traverse + metadata      | ✗        | any                   | N/A                     |

---

## 5. `monad::Db` Method Summaries

Below is a concise English summary of each method’s arguments, effects, and pre/post conditions:

| Method & Signature                                             | Arguments                          | What it does & Conditions                                                                                  |
| -------------------------------------------------------------- | --------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| `read_account(Address addr)`                                   | `addr`: account key             | **Reads** the account at `addr` in the current (block,round). Returns `None` if no account.                 |
| `read_storage(Address a, Incarnation i, bytes32_t key)`        | `a`, storage slot `key`, `i`      | **Reads** 32‑byte storage value at that slot/version. Defaults to zero if unset.                          |
| `read_code(bytes32_t hash)`                                    | `hash`: code key                 | **Reads** code analysis pointer for that account/class if present.                                         |
| `read_eth_header()`                                            | (none)                            | **Reads** the RLP‑decoded block header at current version.                                                  |
| `state_root(), receipts_root(), transactions_root(), withdrawals_root()` | (none)                   | **Reads** the MPT root for accounts/receipts/txs/withdrawals under current prefix/version.                  |
| `set_block_and_round(uint64_t block, optional<uint64_t> rnd)`  | `block`: version; `rnd`: round   | **Switches** read prefix+version. If `rnd` given → proposal_prefix(rnd); else → finalized prefix.         |
| `commit(StateDeltas&, Code&, Header&, …)`                       | EVM post‐state and block inputs   | **Writes** a new proposal snapshot for block `Header.number`. **Precondition:** execution succeeded.     |
| `finalize(uint64_t block, uint64_t rnd)`                       | `block`, `rnd`                   | **Freezes** the proposal snapshot → finalized prefix. Updates `latest_finalized_block_id`.                  |
| `update_verified_block(uint64_t block)`                        | `block`: verified block           | **Marks** the highest delayed‐execution block applied.                                                      |
| `update_voted_metadata(uint64_t block, uint64_t rnd)`          | `block`: voted block, `rnd`: voted round | **Stores** only the *highest‐round* QC. On next vote, if `rnd` > existing, overwrite `(block,rnd)`.          |

---
## 6. Clarifications & Common Points of Confusion

**Q: Why does the StateSync server context cache deletions?**  
A: The MPT traversal used to stream upserts only visits live (non‐deleted) leaves. To faithfully reproduce on the client that a slot or account was removed, the server must record which keys were zeroed out or accounts deleted during each block’s commit/finalize.  `statesync_server_context` instruments `commit()` and `finalize()` to build a bounded ring buffer of deletions and then iterates over them to emit explicit delete messages alongside the upsert stream.

**Q: Why not record all changed keys/accounts instead of just deletions?**  
A: Recording every changed key duplicates the work of the MPT traversal, which already streams all existing leaves as upserts. Only removed keys would otherwise vanish silently, so only deletions must be captured explicitly to guide the client’s trie GC.

**Q: How do finalize vs update_verified_block vs update_voted_metadata differ?**  
- `finalize(block,round)`: copies the proposal prefix snapshot into the immutable finalized prefix and bumps the finalized‐block watermark (no further writes ever touch that block).  
- `update_verified_block(block)`: marks which deferred‐execution block headers were validated/applied—this watermark may lag finalized blocks if there are no delayed headers.  
- `update_voted_metadata(block,round)`: logs the highest‐round QC vote the node has cast for a given block (overwriting any previous lower‐round vote), for crash recovery and RPC inspection.

**Q: Why record a vote (update_voted_metadata) on a block before it’s finalized?**  
A: Voting (producing a QC) is part of the PROPOSE phase, not finalization.  The node records its latest QC immediately after proposing, so that on restart it can recover its locked certificate and preserve consensus safety.

**Q: Does update_voted_metadata keep history of all votes?**  
A: No. The implementation only stores a single `(block,round)` pair—always the highest‐round seen so far. Older or duplicate rounds are ignored.

**Q: Must the block number passed to update_voted_metadata or update_verified_block match the current activeBlock?**  
A: Not necessarily.  These two methods record independent consensus metadata: one for QC votes and one for delayed‐execution verification.  They do not modify the active read/write snapshot (that is left to `set_block_and_round` and `finalize`).

**Q: How are `delayed_execution_results` populated?**  
A: The consensus layer (outside this repo) packs any deferred‐execution headers into `consensus_header.delayed_execution_results`.  MonAD only decodes them and validates them via `validate_delayed_execution_results(...)` against the local trie snapshot; the vector is not modified by the execution layer.

**Q: Does each block’s header contain the root after executing that block or N‑2?**  
A: Every block N’s header has its own post‑execution state root.  `block_state.commit(…)` writes the header (including `state_root = state_root()`) under version N, and only then can `finalize(N,…)` succeed.  There is no two‐block lag, and you cannot finalize a block you haven’t executed.

**Q: If you reset to the finalized state and then re‑commit the same (block,round), should the state deltas be computed as s₂ vs s₁ or s₂ vs s₀?**  
A: They must always be diff(s₂ vs s₀).  Before each commit you call `set_block_and_round(finalized_block,nullopt)` to reset the working prefix back to the finalized sub‑trie (state s₀), so `TrieDb::commit`’s guard sees a “new” (block,round) and invokes `copy_trie` to snapshot s₀ again (shallowly, only the root chunk is written).  Then `upsert(state_deltas,version)` applies the entire s₂−s₀ diff and `write_new_root_node(...,version)` simply overwrites that version’s root‐offset in place, yielding exactly s₂ under the proposal prefix and discarding any prior s₁.  
【F:monad/dbsummary2.md†L237-L241】【F:monad/dbsummary2.md†L253-L274】【F:monad/libs/execution/src/monad/db/trie_db.cpp†L484-L489】【F:monad/libs/execution/src/monad/db/trie_db.cpp†L187-L197】【F:monad/libs/db/src/monad/mpt/trie.cpp†L1935-L1946】

**Q: db.commit(…) takes a `MonadConsensusBlockHeader`. Which fields of it does commit actually use?**  
A: Internally, `TrieDb::commit` only *inspects* two parts of the header for prefix/version switching:
  1. `consensus_header.round` → to select `proposal_prefix(round)`;
  2. `consensus_header.execution_inputs.number` → to bump the MPT version (block number).
These drive the `if(consensus_header.round!=round_number_||header.number!=block_number_)` guard.【F:monad/libs/execution/src/monad/db/trie_db.cpp†L161-L169】


Additionally, commit *persists*:
  - The full `consensus_header` (RLP‑encoded under `BFT_BLOCK_NIBBLE`) so all its votes/signatures/delayed results are stored.【F:monad/libs/execution/src/monad/db/trie_db.cpp†L365-L370】
  - The `execution_inputs` block‑header fields (`number`, `timestamp`, etc) are used to build the canonical `BLOCKHEADER_NIBBLE` leaf via `rlp::encode_block_header` (together with computed roots/blooms).【F:monad/libs/execution/src/monad/db/trie_db.cpp†L412-L431】

**Q: In `set_block_and_round`, can the `round_number` argument be `std::nullopt` if the block has been finalized by calling `finalize()`?**  
A: Yes. Passing `std::nullopt` for `round_number` selects the finalized sub‑trie prefix.  The implementation in `TrieDb` is:

```cpp
// libs/execution/src/monad/db/trie_db.cpp:L484-L489
void TrieDb::set_block_and_round(
    uint64_t block_number,
    std::optional<uint64_t> round_number)
{
    if (!db_.is_on_disk()) {
        MONAD_ASSERT(block_number_ == 0);
        MONAD_ASSERT(round_number_ == std::nullopt);
        return;
    }
    prefix_ = round_number.has_value()
                ? proposal_prefix(round_number.value())
                : finalized_nibbles;
    MONAD_ASSERT(db_.find(prefix_, block_number).has_value());
    block_number_ = block_number;
    round_number_ = round_number;
}
```
【F:monad/libs/execution/src/monad/db/trie_db.cpp†L484-L489】

---
## 7. Genesis: Initial State Setup

The genesis block (block 0) is loaded from a JSON file via `read_genesis(…)` in `genesis.hpp`, which parses both the block header and the initial account allocations, then commits and finalizes block 0:

```cpp
// libs/execution/src/monad/execution/genesis.hpp:L132-L146
inline BlockHeader read_genesis(std::filesystem::path const& genesis_file, Db& db) {
    std::ifstream ifile(genesis_file);
    auto const genesis_json = nlohmann::json::parse(ifile);

    StateDeltas state_deltas;
    read_genesis_state(genesis_json, state_deltas);

    MonadConsensusBlockHeader consensus_header{};
    consensus_header.execution_inputs = read_genesis_blockheader(genesis_json);

    db.commit(state_deltas, Code{}, consensus_header);
    db.finalize(0, 0);
    return db.read_eth_header();
}
```

Here, `read_genesis_state` populates `state_deltas` with the `alloc` balances:

```cpp
// libs/execution/src/monad/execution/genesis.hpp:L108-L130
inline void read_genesis_state(nlohmann::json const& genesis_json, StateDeltas& state_deltas) {
    for (auto const& info : genesis_json["alloc"].items()) {
        Address addr{};
        auto const bs = evmc::from_hex("0x" + info.key());
        std::copy_n(bs->begin(), bs->length(), addr.bytes);

        Account acct{};
        acct.balance = intx::from_string<uint256_t>(
            info.value()["wei_balance"].get<std::string>());
        acct.nonce = 0;

        state_deltas.emplace(addr, StateDelta{.account={std::nullopt, acct}});
    }
}
```
【F:monad/libs/execution/src/monad/execution/genesis.hpp†L108-L130】

`TrieDb`’s initial constructor and commit snapshot‑guard automatically handle block 0/round 0:

```cpp
// libs/execution/src/monad/db/trie_db.cpp:L83-L89
TrieDb::TrieDb(mpt::Db& db)
  : db_{db}
  , block_number_{db.get_latest_finalized_block_id()==INVALID_BLOCK_ID?0:db.get_latest_finalized_block_id()}
  , round_number_{std::nullopt}
  , prefix_{finalized_nibbles}
{}

// libs/execution/src/monad/db/trie_db.cpp:L161-L169
if (db_.is_on_disk() &&
    (consensus_header.round != round_number_ ||
     header.number             != block_number_))
{
    // first commit for (0,0): no copy_trie since no prior state
    round_number_ = consensus_header.round;
    block_number_ = header.number;
    prefix_       = proposal_prefix(round_number_);
}
```
【F:monad/libs/execution/src/monad/db/trie_db.cpp†L83-L89】【F:monad/libs/execution/src/monad/db/trie_db.cpp†L161-L169】

Finally, finalizing block 0 shallow‑copies the proposal sub‑trie into the immutable finalized prefix:

```cpp
// libs/execution/src/monad/db/trie_db.cpp:L491-L502
db_.copy_trie(0, proposal_prefix(0), 0, finalized_nibbles, true);
db_.update_finalized_block(0);
```
【F:monad/libs/execution/src/monad/db/trie_db.cpp†L491-L502】

After this sequence, the database’s finalized prefix at version 0 contains the genesis state.

---
**Q: How do RODb and RWDb coordinate across separate processes?**  
A: As noted in the `mpt::Db` interface comment, `find`/`get`/`get_data` return non‑owning cursors that become invalid when the trie root is reloaded—either by an RWDb upsert, an RODb switch, or an RWDb in another process.

```cpp
// libs/db/src/monad/mpt/db.hpp:L87-L96
// The find, get, and get_data API calls return non-owning references.
// The result lifetime ends when a subsequent operation reloads the trie
// root. This can happen due to an RWDb upsert, an RODb reading a different
// version, or an RODb reading the same version that has been updated by an
// RWDb in another process.
```

Under the hood, both RODb and RWDb multiplex on the same on‑disk metadata region via `mmap(..., MAP_SHARED)`.  The ring‑buffer of root/verified/voted versions is stored in these in‑file metadata pages and updated atomically by RWDb; any process mapping the same file sees the new metadata immediately in memory.

```cpp
// libs/db/src/monad/mpt/update_aux.cpp:L563-L572
// Map the two mirror copies of the metadata region via mmap(..., MAP_SHARED)
db_metadata_[0].main = (detail::db_metadata *)mmap(
    nullptr, map_size, prot, MAP_SHARED, fd, offset0);
db_metadata_[1].main = (detail::db_metadata *)mmap(
    nullptr, map_size, prot, MAP_SHARED, fd, offset1);
```

Only the metadata pages (versions/ring buffers) are shared cross‑process.  The actual trie node chunks are loaded into each process’s own memory (via `mmap` or async read) and pinned locally by `OwningNodeCursor` (`shared_ptr<Node>`).  No per‑chunk pin flags are written back to the shared metadata region—only the ring‑buffer pages are memory‑mapped MAP_SHARED, so processes coordinate only on version metadata.  If a version is evicted by one process, readers holding `OwningNodeCursor`s for that version still keep their nodes alive in their own heap.

**Q: Doesn’t commit() issue an upsert and reload the trie root—won’t that invalidate existing cursors?**  
A: That comment in the `mpt::Db` interface applies _only_ if you call `find`/`get` on the _same_ mpt::Db instance that then `upsert`s.  In Monad we never mix reads and writes on one instance.  Instead, the execution runloop uses a separate RWOnDisk instance and RPC/CLI use a read‑only RODb instance.  Since RODb never calls upsert, its cursors stay valid even while the writer evicts old versions.

**Q: What if after checking version validity in the ring buffer, the reader is descheduled and another process evicts that version before the disk read completes?**  
A: The MPT I/O path double-checks validity at both ends.
```cpp
// libs/db/src/monad/mpt/find_notify_fiber.cpp:L274-L280
if (!aux.version_is_valid_ondisk(version)) {
    promise.set_value({start, find_result::version_no_longer_exist});
    return;
}
```
That check prevents starting a read for a version already evicted.

```cpp
// libs/db/src/monad/mpt/read_node_blocking.cpp:L22-L24, L54-L57
Node::UniquePtr read_node_blocking(aux, node_offset, version) {
    if (!aux.version_is_valid_ondisk(version)) {
        return {};
    }
    // perform pread(...) into buffer, then:
    return aux.version_is_valid_ondisk(version)
               ? deserialize_node_from_buffer(buffer + buffer_off,
                                             bytes_read - buffer_off)
               : Node::UniquePtr{};
}
```
If eviction occurs mid-read, the post-read check stops stale buffers from returning.

**Q: Does JSON‑RPC eth_call only read finalized state?**  
A: No. The eth_call RPC endpoint accepts both a `block_number` and a `round` argument, then does:
```cpp
// libs/rpc/src/monad/rpc/eth_call.cpp:L90-L94
tdb.set_block_and_round(
    block_number,
    round == mpt::INVALID_ROUND_NUM ? std::nullopt
                                    : std::make_optional(round));
```
If you pass a valid `round`, it reads the *proposal* subtrie (in‑flight state); if you pass `INVALID_ROUND_NUM` (or omit the round), it reads the *finalized* subtrie.


## Races betwen eth_call and multiple DB multiple commits to same round number:

RPC atomicity: it seems serving an RPC request may require multiple db reads and it is not clear to me whether all such reads to serve a single request will see the same state if there is a racy recommit for the same block and round number.
Lets take a concrete example: suppose the handling of an rpc request for block number 100, round number 100 started when block b was commited with post-block state s for block number 100, round 100 when the last finalized block is 99. Suppose that after the rpc handler read account ac1, a new block b' with state s' gets commited for the same block and round numbers (100,100) and then the rpc handler reads ac2 to service the *same* request. It is clear that the read of ac1will read from s.   It is not clear to me  whether the read of ac2 will read from s or s' ?

Answer: the read from ac2 will be from s, not s'.
At the beginning of eth_call, it does `set_block_and_round` exactly once. this looks up the state root (using db_.find) where s is stored on disk and stores it in prefix_cursor_ (say pre1.). Subsequent commit of b' will ensure that db.find on the round number will return a new prefix (say pre2). calls like TrieRODB::read_storage do NOT do db_.find again to find the root prefix. they keep using the result of the lookup done suring `set_block_and_round`.

Concrete example to illustrate the new prefix creation on the same 

Suppose the state of the Db is where block 99 is finialized.
Here is a conrete trace involving 2 process (Pexec, Prpc) where actions happen from that state in the following order:
- Pexec does db.commit() block b with post-block state s for block number 100, round 100.
- Prpc does trie_rodb.set_block_and_round(100,100). let pre1 be the value of trie_rodb.prefix_cursor_after this call
- Pexec does db.commit() block b' with post-block state s' for block number 100, round 100.
- Prpc does trie_rodb.set_block_and_round(100,100). let pre2 be the value of trie_rodb.prefix_cursor_after this call
is pre1==pre2?

No.


## Why multiple commits with same round number:

Consensus sends proposals to execution even *before* there is a QC on the proposal. So, a malicious leader can equivocate and send many distinct proposals in the same round.
Such bad behaviour would later be detected and the leader will face financial penalities (stake slashing).
But execution may get multiple blocks before the detection.

An alternative could be that consensus only sends proposals post QC: then execution will not get multiple proposals in the same round: there can be atmost 1 distinct proposal with QC in any round. However, we want to reduce latency.


(Each round has a new leader.)








**Q: Where and when does the execution layer advance the block number (i.e. the MPT version)?**  
A: In `TrieDb::commit`, at the very start of the method, before assembling any updates.  That bump to `block_number_`/`round_number_` is then used to stamp all ensuing updates, and finally `db_.upsert(..., block_number_, ...)` writes them out:
```cpp
// libs/execution/src/monad/db/trie_db.cpp:L187-L197
if (db_.is_on_disk() && (consensus_header.round != round_number_ ||
                         header.number     != block_number_)) {
    auto const dest_prefix = proposal_prefix(consensus_header.round);
    if (db_.get_latest_block_id() != INVALID_BLOCK_ID) {
        db_.copy_trie(
            block_number_, prefix_, header.number, dest_prefix, false);
    }
    round_number_ = consensus_header.round;
    block_number_ = header.number;
    prefix_       = dest_prefix;
}
```
【F:libs/execution/src/monad/db/trie_db.cpp†L187-L197】

**Q: What exactly does `finalize()` do?  Does it re‑write all leaf (account/storage) values?**  
A: No.  `TrieDb::finalize` simply invokes `copy_trie` to clone the proposal subtrie under `proposal_prefix(round)` into the `finalized_nibbles` prefix—then writes only the new root node and updates the finalized‐block watermark:
```cpp
// libs/execution/src/monad/db/trie_db.cpp:L483-L497
void TrieDb::finalize(uint64_t const block_number, uint64_t const round_number)
{
    if (db_.is_on_disk()) {
        auto const src_prefix = proposal_prefix(round_number);
        MONAD_ASSERT(db_.find(src_prefix, block_number).has_value());
        db_.copy_trie(
            block_number, src_prefix,
            block_number, finalized_nibbles,
            true  // block until root is persisted
        );
        db_.update_finalized_block(block_number);
    }
}
```
【F:libs/execution/src/monad/db/trie_db.cpp†L483-L497】

This performs a deep, in‑memory clone of the subtrie but **does not** eagerly re‑encode all leaf nodes.  Only the new root chunk is written to disk; all child chunks remain shared and are lazy‑loaded.

**Q: Why does commit take a nested `vector<vector<CallFrame>>`? Is this just debugging? Can RPC read it?**  
A: The outer `vector` is per‑transaction and the inner `vector<CallFrame>` is the sequence of EVM call‑trace frames for that transaction.  During commit, `TrieDb` RLP‑encodes and stores these frames under the `CALL_FRAME_NIBBLE` subtrie so tools can fetch post‑execution traces:
```cpp
// libs/execution/src/monad/db/trie_db.cpp:L297-L305
std::span<CallFrame const> frames{call_frames[i]};
byte_string_view view = bytes_alloc_.emplace_back(rlp::encode_call_frames(frames));
// chunk and upsert under CALL_FRAME_NIBBLE …
```
【F:libs/execution/src/monad/db/trie_db.cpp†L297-L305】

The `encode_call_frames`/`decode_call_frames` helpers live in:
```cpp
// libs/execution/src/monad/execution/trace/rlp/call_frame_rlp.hpp:L15-L20
byte_string encode_call_frames(std::span<CallFrame const>);
Result<std::vector<CallFrame>> decode_call_frames(byte_string_view &);
```
【F:libs/execution/src/monad/execution/trace/rlp/call_frame_rlp.hpp†L15-L20】

This feature drives CLI and debug‑trace tooling (e.g. eventual RPC `debug_traceBlockByNumber`‑style endpoints).  There is no consensus requirement on call frames, and today no built‑in JSON‑RPC method reads them—you’d need to traverse the `CALL_FRAME_NIBBLE` subtree and decode manually.
---
*Last updated:* __DATE__



## Open questions:
- leader can equivocate, but if a follower gets a second proposal for the same round, would it forward to execution or do something else, e.g. detect equivvocation and stop participating in that round, or even try to start a new round?
- if execution can indeed receive multiple proposals for the same round, is there a guarantee that the latest one must be the final one. what if an earlier one is picked to be the final one? all earlier ones become unreachanble by db._find


# Current Task
*

```gallina
fill in the following admits above in the file:

Definition maxL (l: list N) : N. Proof. Admitted.
Definition minL (l: list N) : N. Proof. Admitted.

  Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N. Proof. Admitted.

  Definition updateBlockNum (d: DbModel) (bnum: N) (f: BlockIndexState -> BlockIndexState): DbModel. Proof. Admitted.

  Definition finalizeProposal (pid: ProposalId) (d: BlockIndexState) : BlockIndexState. Proof. Admitted. 

Definition commit_model
  (preDb      : DbModel)
  (newProposal   : ProposalInDb)
  : DbModel. Proof. Admitted.
```

Put them in a new module to avoid name clash with the existing admits. I will later copy your definitions up  
Unfortunately, CppDefnOf is currrently not working so you can only issue Coq queries not clangd queries.

# Contents of the current file

```coq
(* TODO: put most Imports in a prelude *)
Require Import QArith.
Require Import Lens.Elpi.Elpi.
Require Import bluerock.lang.cpp.cpp.
Require Import stdpp.gmap.
Require Import monad.proofs.misc.
Require Import monad.proofs.evmopsem.
Print block.step.
Print evm.network.
Import linearity.
Require Import monad.asts.exb.
Require Export bluerock.auto.cpp.spec.

Require Import monad.proofs.libspecs.
Import cQp_compat.
#[local] Open Scope lens_scope.

#[local] Open Scope Z_scope.
  Open Scope N_scope.
(*
Require Import EVMOpSem.evmfull. *)
Import cancelable_invariants.
Require Import List.
Require Import bluerock.auto.cpp.
Require Import bluerock.auto.cpp.specs.
Require Import monad.proofs.exec_specs.

Record ConsensusBlockHeader :=
  {
    roundNum:N;
    (* TODO: add more fields *)
  }.
    
Notation EvmState := evm.GlobalState.

Record ProposalInDb :=
  {
    cheader: ConsensusBlockHeader;
    proposedBlock: Block;
    postBlockState: EvmState;
    txResults: list TransactionResult;
  }.
    
(* Todo: replace by ConsensusProposal
Record Proposal :=
  {
    roundNumber: N;
    proposedBlock: Block;
    (* delayed_execution_results is not really relevant because we know that last_verified=last_finalized+3 and we enforce this constraint logicall in these specs *)
  }.
 *)

Record BlockIndexState :=
  {
    unfinalizedProposals: list ProposalInDb;
    finalizedProposal : option ProposalInDb
  }.
    
Record ProposalId :=
  {
    idBlockNumber : N;
    idRoundNumber: option N;
  }.
    
Record DbModel : Type :=
  {
    blockIndicesStates: list BlockIndexState;
    
    activeProposal: option ProposalId;
    (*^ changed by set_block_and_round. None means set_block_and_round has never been called on this object yet *)
    
    votedMetadata: option (N * N);
    (*^ (block_num, round) from latest update_voted_metadata *)
    
    lastVerifiedBlockIndex: N;
    
    cinvId: gname;
    (* ^ Coq-specific detail: logical id of the concurrency invariant. there is no C++ analog of this *)
  }.

Definition allProposals (b: BlockIndexState) :=
  match finalizedProposal b with
  | None => (unfinalizedProposals b)
  | Some p => p::(unfinalizedProposals b)
  end.

Definition pblockNumber (p: ProposalInDb):=  number (header (proposedBlock p)).

Definition blockNumber (b: BlockIndexState) : N:=
  match allProposals b with
  | h::_ => pblockNumber h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

Definition proposalsHaveSameBlockNumber (b: BlockIndexState) :=
  forall (p1 p2: ProposalInDb),
    p1 ∈ (allProposals b)
    -> p2 ∈ (allProposals b)
    -> pblockNumber p1 = pblockNumber p2.

Definition hasAtLeastOneProposal (b: BlockIndexState) :=
  exists p: ProposalInDb, p ∈ (allProposals b).

Notation NoDuplicate := NoDup.

Definition validBlockIndexState  (b: BlockIndexState) :=
  hasAtLeastOneProposal b
  /\ proposalsHaveSameBlockNumber b
  /\ NoDuplicate (map (roundNum ∘ cheader) (allProposals b)).

Definition maxL (l: list N) : N. Proof. Admitted.
Definition minL (l: list N) : N. Proof. Admitted.
Open Scope N_scope.
Definition contiguousBlockNumbers (lb: list BlockIndexState) : Prop :=
  let blockNums := List.map blockNumber lb in
  let maxBlockNum := maxL blockNums in 
  let minBlockNum := minL blockNums in
  forall blockNum:N,  minBlockNum <= blockNum <= maxBlockNum -> exists b, blockNumber b = blockNum /\ b ∈ lb.
                           

Definition lowestBlockNumber (d: DbModel) : N:=
  match blockIndicesStates d with
  | h::_ => blockNumber h
  | [] => 0 (* dummy value. use sites will ensure this case never happens *)
  end.

(* upstream *)
Definition nthElem {A:Type} (l: list A) (n:N) : option A :=
  nth_error l (N.to_nat n).
             
Definition lookupBlockByNumber (bnum: N) (d: DbModel) : option BlockIndexState :=
  match List.filter (fun b => bool_decide (blockNumber b= bnum)) (blockIndicesStates d) with
  | h::tl => Some h (* [validBlockIndexState b] -> tl = [] *)
  | [] => None
  end.

Definition lookupProposalByRoundNum (b: BlockIndexState) (rnum: N) : option ProposalInDb :=
  match List.filter (fun p => bool_decide (roundNum (cheader p) = rnum)) (allProposals b) with
  | h::tl => Some h (* [validBlockIndexState b] -> tl = [] *)
  | [] => None
  end.
    
Definition lookupProposal (id: ProposalId)  (d: DbModel)
  : option ProposalInDb :=
  match lookupBlockByNumber (idBlockNumber id) d with
  | None => None
  | Some b =>
      match idRoundNumber id with
      | None => finalizedProposal b
      | Some rnum => lookupProposalByRoundNum b rnum
      end
  end.      

Definition lookupActiveProposal (d: DbModel) : option ProposalInDb :=
  match activeProposal d with
  | None => None
  | Some ap => lookupProposal ap d
  end.
    
Definition validActiveProposal  (m: DbModel) : Prop :=
  match activeProposal m with
  | None => True
  | Some pid => isSome (lookupProposal pid m)
  end.                       

(*
Definition validProposal (proposal: Proposal) (lastFin: option N) :=
    match lastFin with
    | Some lastFinBlock =>
        (bnumber (proposedBlock proposal) = 1 + lastFinBlock)%N
    | None => bnumber (proposedBlock proposal) = 0%N (* TODO: is this correct? I guess when we start the system, there will always be the finalized genesisd block? *)
    end.
*)    

(*
  Definition lastVerified (lastFinalized: option N) : option N :=
    match lastFinalized with
    | Some lastFinBlock  =>
        if (bool_decide (lastFinBlock < 3))
        then None
        else Some (lastFinBlock -3)
    | None => None
    end.


  Definition lastFinalizedBlockIndex' (finalizedBlocks: list Block) : option N :=
    match head finalizedBlocks with
    | Some lastFinBlock =>
        Some (bnumber lastFinBlock)
    | _  => None
    end.
  
  Definition lastFinalizedBlockIndex (m: DbModel) : option N :=
    lastFinalizedBlockIndex' (map fst (finalizedBlocks m)).
 *)

Definition splitL {A} (n:N) (l: list A) : (list A * (list A)) :=
  (takeN n l, dropN n l).

Definition validDbModel (m: DbModel) : Prop :=
  (forall b, b ∈ (blockIndicesStates m) -> validBlockIndexState b)
  /\ contiguousBlockNumbers (blockIndicesStates m)
  /\ NoDuplicate (map blockNumber (blockIndicesStates m))
  /\ validActiveProposal m
  /\ (exists numFinalized:N, let '(firstn, rest) := splitL numFinalized (blockIndicesStates m) in
         (forall b, b ∈ firstn -> isSome (finalizedProposal b))
         /\ (forall b, b ∈ rest -> isNone (finalizedProposal b))
     ).
       (* may need to also say that the evm.GlobalState parts are obtained by executiing EVM semantics of a block on the state at the end of the previous block, but maybe that is the client's responsibility? the db can be agnostig to the execution mechanism *)

  Definition dummyEvmState: evm.GlobalState. Proof. Admitted.
  
(*
Definition stateAfterLastFinalized (m: DbModel) : evm.GlobalState :=
match head (finalizedBlocks m) with
| Some lastFinBlock =>
hd dummyEvmState (map snd (finalizedBlocks m))
| _  => dummyEvmState (* validModel rules this case out *)
end.
 *)
  
Definition stateAfterActiveProposal (m: DbModel) : evm.GlobalState :=
  match lookupActiveProposal m with
  | None => dummyEvmState
  | Some p => postBlockState p
  end.
  

(** ignore the next 4 lines: Coq boilerplate *)
Open Scope Z_scope.
#[only(lens)] derive DbModel.
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI fracR}. (* some standard assumptions about the c++ logic *)
  Context  {MODd : exb.module ⊧ CU}.
  
  
  (** contains the auth ownership of monad::mpt::Db in-memory datastructures AND also the on-disk datastructures. there can be only 1 object owning the on-disk data at any given time. full 1 fraction is needed to update the state. this ownership [dbAuthR 1 _] is disjoint from [dbFragR] below. The latter can be used to read the database even when some other thread owns [dbAuthR 1 _]: the actual ownership of the disk/memory lives in a concurrent invariant *)
  Definition TrieDBR (q:Qp) (m: DbModel) : Rep. Proof. Admitted.

  (* Knowledge (no resource ownership) *)
  Definition SelectedProposalForBlockNum (blockNumber: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (* cannot use if different proposals can be done for the same round number *)
  Definition ProposedInRoundNum (roundNumber: N) (b: ProposalInDb) : mpred. Proof. Admitted.

  (* all reads will read from activeProposal, which is determined at TrieRODB::set_block_and_round *)
  Definition TrieRODBR (q:Qp) (activeProposal: option ProposalInDb) : Rep. Proof. Admitted.

  Notation dbAuthR := TrieDBR. (* TODO: inline *)

  (* when we fill in the definition of dbAuthR, we must ensure the lemmas below are provable *)
  Lemma dbAuthREntails (q:Qp) (m: DbModel) : dbAuthR q m |--  dbAuthR q m ** [| validDbModel m|].
  Proof. Admitted.
                                                     
  (** Raw db ownersip (the part that is remaining after dbAuthR above), shared with RODb instances. can use this to construct trie_rodb. RPC and statesync server(s) use fractions of this ownership to read the on-disk data *)
  Definition dbFragR  (q:Qp) : mpred. Proof. Admitted.

  cpp.spec "monad::Db::read_storage(const evmc::address&, monad::Incarnation, const evmc::bytes32&)"
    as read_storage_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{addressp} "address" (Vptr addressp)
      \prepost{q address} addressp |-> addressR q address
      \arg{incp} "incarnation" (Vptr incp)
      \prepost{q blockTxInd} incp |-> IncarnationR q blockTxInd
      \arg{keyp} "key" (Vptr keyp)
      \prepost{key:N} keyp |-> bytes32R q key
      
      \pre{activeProposal} [| lookupActiveProposal preDb = Some activeProposal |]
      \post{retp:ptr} [Vptr retp]
        retp |-> bytes32R
        1
        (lookupStorage (postBlockState activeProposal) address key blockTxInd)).


  Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N. Proof. Admitted.

  Definition updateBlockNum (d: DbModel) (bnum: N) (f: BlockIndexState -> BlockIndexState): DbModel. Proof. Admitted.

  Definition finalizeProposal (pid: ProposalId) (d: BlockIndexState) : BlockIndexState. Proof. Admitted. 
  
  cpp.spec "monad::Db::finalize(unsigned long, unsigned long)"
    as finalize_spec_auth with (fun (this:ptr) =>
      \prepost{q preDb} this |-> TrieDBR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round_number" (Vint roundNum)
      \let pid := {| idBlockNumber := blockNum; idRoundNumber:= Some roundNum |}
      \pre{prp} [| lookupProposal pid preDb = Some prp|]
      \pre [| lowestUnfinalizedBlockIndex preDb = Some blockNum |]
      \post
         this |-> TrieDBR q (updateBlockNum preDb blockNum (finalizeProposal pid))
         ** SelectedProposalForBlockNum blockNum prp (* this Knowledge assertion can be used to constrain the output of TrieRODB reads *)
                               ).
                               
  (* no finalize in triedb *)
  

  cpp.spec "monad::Db::update_verified_block(unsigned long)"
    as update_verified_block_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \pre [| match lowestUnfinalizedBlockIndex preDb with
              | Some s =>  blockNum < s
              | None => False (* if no block has been finalized yet, cannot call this method *)
              end |]
      \post this |-> dbAuthR q (preDb &: _lastVerifiedBlockIndex .= blockNum)).

Import libspecs.
cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as set_block_and_round_spec with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preDb} this |-> dbAuthR q preDb

    (* block_number: unsigned long *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNumber pid))

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" q (Vint v)) (cQp.mut q)
          (idRoundNumber pid))

    \pre{prp} [| lookupProposal pid preDb = Some prp|]

    (* On return, activeBlock is updated accordingly *)
    \post this |-> dbAuthR q (preDb &: _activeProposal .= Some pid)
  ).

(* cpp.spec "monad::RODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" *)
cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as rodb_set_block_and_round_spec1 with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preActive} this |-> TrieRODBR q preActive

    (* block_number: unsigned long *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNumber pid))

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" q (Vint v)) (cQp.mut q)
          (idRoundNumber pid))


    (* On return, activeBlock is updated accordingly *)
    \post{ret} [Vbool ret]
       if ret then Exists proposal,  this |-> TrieRODBR q (Some proposal)
                                     ** SelectedProposalForBlockNum (idBlockNumber pid) proposal
      else  this |-> TrieRODBR q None
  ).

(* cpp.spec "monad::RODb::set_block_and_round(unsigned long, std::optional<unsigned long>)" *)
cpp.spec "monad::Db::set_block_and_round(unsigned long, std::optional<unsigned long>)"
  as rodb_set_block_and_round_spec2 with (fun (this:ptr) =>
    (* Full ownership of the Db model *)
    \prepost{q preActive} this |-> TrieRODBR q preActive

    (* block_number: unsigned long *)
    \arg{pid: ProposalId} "block_number" (Vint (idBlockNumber pid))

    (* round_number: std::optional<unsigned long> by-pointer *)
    \arg{roundLoc}   "round_number" (Vptr roundLoc)
    \prepost{roundOpt: option N}
       (roundLoc |-> optionR "unsigned long"
          (fun v:N => primR "unsigned long" q (Vint v)) (cQp.mut q)
          (idRoundNumber pid))

    \pre{proposal} SelectedProposalForBlockNum (idBlockNumber pid) proposal

    (* On return, activeBlock is updated accordingly *)
    \post{ret} [Vbool ret]
       if ret then this |-> TrieRODBR q (Some proposal)
      else  this |-> TrieRODBR q None
   ).

  cpp.spec "monad::Db::update_voted_metadata(unsigned long, unsigned long)"
    as update_voted_metadata_spec with (fun (this:ptr) =>
      \prepost{q preDb} this |-> dbAuthR q preDb
      \arg{blockNum:N}   "block_number" (Vint blockNum)
      \arg{roundNum:N}   "round"        (Vint roundNum)
      \post this |-> dbAuthR q (preDb &: _votedMetadata .= Some (blockNum, roundNum))).

  Definition stateRoot (b: Block) : N. Proof. Admitted.
  Definition receiptRoot (b: Block) : N. Proof. Admitted.
  Definition transactionsRoot (b: Block) : N. Proof. Admitted.
  Definition withdrawalsRoot (b: Block) : N. Proof. Admitted.


  
Definition commitFullCppName : name:=
  "monad::Db::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)".
(** Compute the post-commit DbModel from pre-commit model and all commit arguments. *)


(** Compute the post-commit DbModel by prepending the new proposal and its state.
    Note: we do not record [rs] in the model (no field to hold transaction results). 
 *)
Definition commit_model
  (preDb      : DbModel)
  (newProposal   : ProposalInDb)
  : DbModel. Proof. Admitted.

(* TODO:
- handle garbage collection
- handle genesis block creation
 *)
Open Scope N_scope.
cpp.spec
  "monad::Db::commit(const tbb::detail::d2::concurrent_hash_map<evmc::address, monad::StateDelta, tbb::detail::d1::tbb_hash_compare<evmc::address>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::address, monad::StateDelta>>>&, const tbb::detail::d2::concurrent_hash_map<evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>, tbb::detail::d1::tbb_hash_compare<evmc::bytes32>, tbb::detail::d1::tbb_allocator<std::pair<const evmc::bytes32, std::shared_ptr<evmone::baseline::CodeAnalysis>>>>&, const monad::MonadConsensusBlockHeader&, const std::vector<monad::Receipt, std::allocator<monad::Receipt>>&, const std::vector<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>, std::allocator<std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>>>&, const std::vector<evmc::address, std::allocator<evmc::address>>&, const std::vector<monad::Transaction, std::allocator<monad::Transaction>>&, const std::vector<monad::BlockHeader, std::allocator<monad::BlockHeader>>&, const std::optional<std::vector<monad::Withdrawal, std::allocator<monad::Withdrawal>>>&)"
  as commit_spec with (fun (this:ptr) =>
    \prepost{(preDb:DbModel)} this |-> dbAuthR 1 preDb

    \arg{(deltas_ptr: ptr) (qs: Qp)} "#0" (Vptr deltas_ptr)
    \prepost{(newProposal: ProposalInDb)}
      deltas_ptr |-> StateDeltasR qs (stateAfterActiveProposal preDb, (postBlockState newProposal))

    \arg{(code_ptr:ptr) (qcd: Qp)} "#1" (Vptr code_ptr)
    \prepost
      code_ptr |-> CodeDeltaR qcd (stateAfterActiveProposal preDb, (postBlockState newProposal))

    \arg{hdr_ptr} "#2" (Vptr hdr_ptr)
    \prepost{ (qpr: Qp)}
      hdr_ptr |-> BheaderR qpr (header (proposedBlock newProposal))
      \pre [| match activeProposal preDb with
              | Some activeProp =>
                  pblockNumber newProposal = 1 + idBlockNumber activeProp
              | None => pblockNumber newProposal = 0
              end
              |]
   (*  \pre [| roundNumber newProposal ∉ (map (roundNumber ∘ fst) (nextBlockProposals preDb)) |] can this, depending on whether consensus can really send us 2 blocks for the same round number *)

    \arg{receipts_ptr} "#3" (Vptr receipts_ptr)
    \prepost{ (qtrs: Qp)}
      receipts_ptr |->
        VectorR
          "monad::Receipt"%cpp_type
          (fun r => ReceiptR r)
          qtrs (txResults newProposal)
          
   \arg{cfs_ptr} "#4" (Vptr cfs_ptr)
   (*       
    \prepost
      cfs_ptr |->
        monad.proofs.libspecs.VectorR
          "std::vector<monad::CallFrame>"%cpp_type
          (fun inner => emp)
          q []
          *)
    \arg{(senders_ptr: ptr) (qsn: Qp)} "#5" (Vptr senders_ptr)
    \prepost
      senders_ptr |->
        monad.proofs.libspecs.VectorR
          "evmc::address"%cpp_type
          (fun a => addressR qsn a)
          qsn (map sender (transactions (proposedBlock newProposal)))

    \arg{txns_ptr qtxn} "#6" (Vptr txns_ptr)
    \prepost
      txns_ptr |->
        monad.proofs.libspecs.VectorR
          "monad::Transaction"%cpp_type
          (fun t => monad.proofs.exec_specs.TransactionR qtxn t)
          qtxn (transactions (proposedBlock newProposal))

    \arg{ommers_ptr qo} "ommers" (Vptr ommers_ptr)
    \prepost
      ommers_ptr |->
        monad.proofs.libspecs.VectorR
          "monad::BlockHeader"%cpp_type
          (fun h => BheaderR qo h)
          qo (ommers (proposedBlock newProposal))

    \arg{wds_ptr} "#8" (Vptr wds_ptr)
    (*      
    \prepost{(ws: option (list monad.proofs.evmopsem.Withdrawal)))}
      wds_ptr |-> monad.proofs.libspecs.optionR
        "std::vector<monad::Withdrawal>"%cpp_type
        (fun ws => monad.proofs.libspecs.VectorR
                     "monad::Withdrawal"%cpp_type
                     (fun _ => pureR True) (* TOFIXLATER: refine to WithdrawalR *)
                     q ws)
        q ws
     *)   
    \post this |-> dbAuthR 1 (commit_model preDb newProposal)
                      ).
End with_Sigma.

```

 You cannot change the content above. Your response will always be inserted after the above content. Do not repeat the above content in your response.



# Response Format (IMPORTANT)
You can either give me (an elisp chat loop) the answer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```.
If you do not follow this format, I would not be able to respond to you properly.
Although I log and publish your responses in entirety, to respond to you, I ONLY LOOK AT THE LAST CODE BLOCK (```gallina or ```coqquery) IN YOUR RESPONSE.
If that is a ```coqquery block, I will send the queries to coqtop and give you back the responses.
If that is a ```gallina block, I will insert it into emacs+proof-general+company-coq and ask proof-general to check till the end. If there are coq errors, I will respond with the errors.

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
THIS IS IMPORTANT. EVERY QUERY MUST BE IN EXACTLY ONE LINE.
The elisp loop talking to you does not do any fancy parsing to split the coqquery code block in to queries: it just treats every line as a separate query.

DO NOT emit any `Require Import/Export` commands in either types of blocks (coqquery or gallina). All the availble libraries have already been `Require`d, so they are availble, at least with fully qualified names. If needed, you can Import (but not `Require Import`) modules defining notations.

Before the final ```gallina or ```coqquery block, explain why: explain your answer or why you need the information from the query AND why that information wasn't available in the queries you have issued so far.
In a ```gallina response, IF YOU LEAVE A HOLE OR DUMMY IMPLEMENTATION, YOU MUST MARK THAT WITH A TOFIXLATER comment, so that you -- not me -- will fix it later.



## Assistant 1

```gallina
Module DbModelOps.
  Import List.
  Open Scope N_scope.

  (** maxL: maximum element of a (nonempty) list of [N], with default 0 on empty *)
  Definition maxL (l: list N) : N :=
    match l with
    | [] => 0
    | x :: xs => fold_left N.max xs x
    end.

  (** minL: minimum element of a (nonempty) list of [N], with default 0 on empty *)
  Definition minL (l: list N) : N :=
    match l with
    | [] => 0
    | x :: xs => fold_left N.min xs x
    end.

  (** lowestUnfinalizedBlockIndex:
       among the [blockIndicesStates] of [d], pick those with
       [finalizedProposal = None] and return the minimum [blockNumber].
   *)
  Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N :=
    let unfin := filter (fun b => match finalizedProposal b with None => true | _ => false end)
                        (blockIndicesStates d) in
    match unfin with
    | [] => None
    | _  => Some (minL (map blockNumber unfin))
    end.

  (** updateBlockNum: update exactly the [BlockIndexState] whose [blockNumber]
       equals [bnum] by applying [f], leave others unchanged.
  *)
  Definition updateBlockNum
             (d: DbModel)
             (bnum: N)
             (f: BlockIndexState -> BlockIndexState)
    : DbModel :=
    {| blockIndicesStates :=
         map (fun b =>
                if bool_decide (blockNumber b = bnum)
                then f b else b)
             (blockIndicesStates d);
       activeProposal        := activeProposal d;
       votedMetadata         := votedMetadata d;
       lastVerifiedBlockIndex := lastVerifiedBlockIndex d;
       cinvId                := cinvId d
    |}.

  (** finalizeProposal: for a given [pid] = (blockNum, Some r),
       remove from [unfinalizedProposals] the one with [roundNum = r],
       and set [finalizedProposal] to that [Some p].
       If [idRoundNumber pid = None] or no match is found, do nothing.
  *)
  Definition finalizeProposal
             (pid: ProposalId)
             (d: BlockIndexState)
    : BlockIndexState :=
    match idRoundNumber pid with
    | None => d
    | Some r =>
      let bs := unfinalizedProposals d in
      let newUnfin := filter (fun p =>
                                negb (bool_decide (roundNum (cheader p) = r)))
                             bs in
      let finalP :=
        match lookupProposalByRoundNum d r with
        | Some p => Some p
        | None   => finalizedProposal d
        end in
      {| unfinalizedProposals := newUnfin;
         finalizedProposal     := finalP
      |}
    end.

  (** commit_model: prepend a new BlockIndexState (with no finalizedProposal)
      for the [newProposal] onto the existing [blockIndicesStates]. *)
  Definition commit_model
             (preDb      : DbModel)
             (newProposal: ProposalInDb)
    : DbModel :=
    let old := blockIndicesStates preDb in
    let newB := {| unfinalizedProposals := [newProposal];
                   finalizedProposal     := None
                |} in
    {| blockIndicesStates     := old ++ [newB];
       activeProposal        := activeProposal preDb;
       votedMetadata         := votedMetadata preDb;
       lastVerifiedBlockIndex := lastVerifiedBlockIndex preDb;
       cinvId                := cinvId preDb
    |}.
End DbModelOps.
```

## User 2

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART. But, keep in mind your complete response will be entered AFTER the content mentioned above in the section 'Contents of the current file'. So do not duplicate the content there. Also, the content above CANNOT be changed. 

Toplevel input, characters 0-306:
> Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N :=
>     let unfin := filter (fun b => match finalizedProposal b with None => true | _ => false end)
>                         (blockIndicesStates d) in
>     match unfin with
>     | [] => None
>     | _  => Some (minL (map blockNumber unfin))
>     end. 
Error:
The following term contains unresolved implicit arguments:
  (λ d : monad.proofs.dbspecs.DbModel,
     let unfin :=
       stdpp.base.filter
         (λ b : monad.proofs.dbspecs.BlockIndexState,
            match monad.proofs.dbspecs.finalizedProposal b with
            | Corelib.Init.Datatypes.Some _ => Corelib.Init.Datatypes.false
            | Corelib.Init.Datatypes.None => Corelib.Init.Datatypes.true
            end)
         (monad.proofs.dbspecs.blockIndicesStates d)
       in
     match unfin with
     | [] => Corelib.Init.Datatypes.None
     | _ :: _ =>
         Corelib.Init.Datatypes.Some
           (monad.proofs.dbspecs.DbModelOps.minL
              (Corelib.Lists.ListDef.map monad.proofs.dbspecs.blockNumber
                 unfin))
     end)
More precisely: 
- ?H: Cannot infer the implicit parameter H of stdpp.base.filter whose type
  is
  "∀ x : monad.proofs.dbspecs.BlockIndexState,
     stdpp.base.Decision
       ((λ b : monad.proofs.dbspecs.BlockIndexState,
           match monad.proofs.dbspecs.finalizedProposal b with
           | Corelib.Init.Datatypes.Some _ => Corelib.Init.Datatypes.false
           | Corelib.Init.Datatypes.None => Corelib.Init.Datatypes.true
           end)
          x)"
  (no type class instance found) in
  environment:
  d : monad.proofs.dbspecs.DbModel


Remember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.
 

## Assistant 2

Coq is complaining because I used the `filter` and `map` identifiers from stdpp, not from Coq’s standard `List` library.  In stdpp,  
```coq
filter : ∀ {A:Type} (P:A→Prop) `{∀ x, Decision (P x)}, list A → list A
```  
so it expects a Prop‐valued predicate and a `Decision` instance, but I gave it a `bool`‐valued test and no `Decision` instance.  The cure is to use Coq’s `List.filter` and `List.map` (which take `A→bool` and `A→B` respectively) rather than stdpp’s.

Below is the full module again, qualifying all uses of `filter`, `map`, and `++` to the Coq `List` module and importing the list notations.  This should typecheck when inserted *after* your existing file.

```gallina
Module DbModelOps.
  Import List ListNotations.
  Open Scope N_scope.

  (** maxL: maximum element of a (nonempty) list of [N], with default 0 on empty *)
  Definition maxL (l: list N) : N :=
    match l with
    | [] => 0
    | x :: xs => fold_left N.max xs x
    end.

  (** minL: minimum element of a (nonempty) list of [N], with default 0 on empty *)
  Definition minL (l: list N) : N :=
    match l with
    | [] => 0
    | x :: xs => fold_left N.min xs x
    end.

  (** lowestUnfinalizedBlockIndex:
       among the [blockIndicesStates] of [d], pick those with
       [finalizedProposal = None] and return the minimum [blockNumber].
   *)
  Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N :=
    let unfin :=
        List.filter
          (fun b => match finalizedProposal b with
                    | None => true | _ => false
                    end)
          (blockIndicesStates d) in
    match unfin with
    | [] => None
    | _  => Some (minL (List.map blockNumber unfin))
    end.

  (** updateBlockNum: update exactly the [BlockIndexState] whose [blockNumber]
       equals [bnum] by applying [f], leave others unchanged.
  *)
  Definition updateBlockNum
             (d: DbModel)
             (bnum: N)
             (f: BlockIndexState -> BlockIndexState)
    : DbModel :=
    {| blockIndicesStates :=
         List.map (fun b =>
                     if bool_decide (blockNumber b = bnum)
                     then f b else b)
                  (blockIndicesStates d);
       activeProposal         := activeProposal d;
       votedMetadata          := votedMetadata d;
       lastVerifiedBlockIndex := lastVerifiedBlockIndex d;
       cinvId                 := cinvId d
    |}.

  (** finalizeProposal: for a given [pid] = (blockNum, Some r),
       remove from [unfinalizedProposals] the one with [roundNum = r],
       and set [finalizedProposal] to that [Some p].
       If [idRoundNumber pid = None] or no match is found, do nothing.
  *)
  Definition finalizeProposal
             (pid: ProposalId)
             (d: BlockIndexState)
    : BlockIndexState :=
    match idRoundNumber pid with
    | None => d
    | Some r =>
      let bs := unfinalizedProposals d in
      let newUnfin :=
          List.filter
            (fun p => negb (bool_decide (roundNum (cheader p) = r)))
            bs in
      let finalP :=
        match lookupProposalByRoundNum d r with
        | Some p => Some p
        | None   => finalizedProposal d
        end in
      {| unfinalizedProposals := newUnfin;
         finalizedProposal     := finalP
      |}
    end.

  (** commit_model: prepend a new BlockIndexState (with no finalizedProposal)
      for the [newProposal] onto the existing [blockIndicesStates]. *)
  Definition commit_model
             (preDb       : DbModel)
             (newProposal : ProposalInDb)
    : DbModel :=
    let old := blockIndicesStates preDb in
    let newB :=
        {| unfinalizedProposals := [newProposal];
           finalizedProposal     := None
        |} in
    {| blockIndicesStates     := old ++ [newB];
       activeProposal         := activeProposal preDb;
       votedMetadata          := votedMetadata preDb;
       lastVerifiedBlockIndex := lastVerifiedBlockIndex preDb;
       cinvId                 := cinvId preDb
    |}.
End DbModelOps.
```

## User 3

commit_model is wrong. you are assuming that there was no BlockIndexState for thhat block number before. there could be one. you need to find it and add to its unfinalizedProposals. adding a new one is correct only if there was none before. remember that validDbModel requires that the block numbers in blockIndicesStates have no duplicates.

## Assistant 3

Below is the fixed `Module DbModelOps.` with `commit_model` updated to merge into an existing `BlockIndexState` when one already exists for the block number, or else append a new one.  All uses of `List.filter`/`List.map`/`++` are qualified to avoid the stdpp conflict.  Insert this *after* your existing file; do not repeat or modify anything above.

```gallina
Module DbModelOps.
  Import List ListNotations.
  Open Scope N_scope.

  (** maxL: maximum element of a (nonempty) list of [N], with default 0 on empty *)
  Definition maxL (l: list N) : N :=
    match l with
    | [] => 0
    | x :: xs => fold_left N.max xs x
    end.

  (** minL: minimum element of a (nonempty) list of [N], with default 0 on empty *)
  Definition minL (l: list N) : N :=
    match l with
    | [] => 0
    | x :: xs => fold_left N.min xs x
    end.

  (** lowestUnfinalizedBlockIndex:
       among the [blockIndicesStates] of [d], pick those with
       [finalizedProposal = None] and return the minimum [blockNumber].
   *)
  Definition lowestUnfinalizedBlockIndex (d: DbModel) : option N :=
    let unfin :=
        List.filter
          (fun b => match finalizedProposal b with
                    | None => true | _ => false
                    end)
          (blockIndicesStates d) in
    match unfin with
    | [] => None
    | _  => Some (minL (List.map blockNumber unfin))
    end.

  (** updateBlockNum: update exactly the [BlockIndexState] whose [blockNumber]
       equals [bnum] by applying [f], leave others unchanged.
  *)
  Definition updateBlockNum
             (d: DbModel)
             (bnum: N)
             (f: BlockIndexState -> BlockIndexState)
    : DbModel :=
    {| blockIndicesStates :=
         List.map (fun b =>
                     if bool_decide (blockNumber b = bnum)
                     then f b else b)
                  (blockIndicesStates d);
       activeProposal         := activeProposal d;
       votedMetadata          := votedMetadata d;
       lastVerifiedBlockIndex := lastVerifiedBlockIndex d;
       cinvId                 := cinvId d
    |}.

  (** finalizeProposal: for a given [pid] = (blockNum, Some r),
       remove from [unfinalizedProposals] the one with [roundNum = r],
       and set [finalizedProposal] to that [Some p].
       If [idRoundNumber pid = None] or no match is found, do nothing.
  *)
  Definition finalizeProposal
             (pid: ProposalId)
             (d: BlockIndexState)
    : BlockIndexState :=
    match idRoundNumber pid with
    | None => d
    | Some r =>
      let bs := unfinalizedProposals d in
      let newUnfin :=
          List.filter
            (fun p => negb (bool_decide (roundNum (cheader p) = r)))
            bs in
      let finalP :=
        match lookupProposalByRoundNum d r with
        | Some p => Some p
        | None   => finalizedProposal d
        end in
      {| unfinalizedProposals := newUnfin;
         finalizedProposal     := finalP
      |}
    end.

  (** commit_model:
      If there is already a [BlockIndexState] for this block number,
      prepend [newProposal] to its [unfinalizedProposals].
      Otherwise, append a fresh [BlockIndexState] with only [newProposal].
  *)
  Definition commit_model
             (preDb       : DbModel)
             (newProposal : ProposalInDb)
    : DbModel :=
    let bnum := pblockNumber newProposal in
    match lookupBlockByNumber bnum preDb with
    | Some _ =>
        (* merge into existing state *)
        updateBlockNum preDb bnum (fun bs =>
          {| unfinalizedProposals := newProposal :: unfinalizedProposals bs;
             finalizedProposal     := finalizedProposal bs
          |})
    | None =>
        (* append a new BlockIndexState *)
        {| blockIndicesStates     := blockIndicesStates preDb ++
                                     [{| unfinalizedProposals := [newProposal];
                                         finalizedProposal     := None |}];
           activeProposal         := activeProposal preDb;
           votedMetadata          := votedMetadata preDb;
           lastVerifiedBlockIndex := lastVerifiedBlockIndex preDb;
           cinvId                 := cinvId preDb
        |}
    end.
End DbModelOps.
```

