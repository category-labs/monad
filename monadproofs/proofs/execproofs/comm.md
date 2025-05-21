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
We have cpp2v, a clang-ast-visitor tool that converts c++ ASTs to Gallina, as an element of type `translation_unit`:.

```gallina
Record translation_unit : Type := {
  symbols : symbol_table;
  types : type_table;
  initializer : InitializerBlock;
  byte_order  : endian;
}.
```
`cpp.spec` looks for a variable in `Context` of type `translation_unit` and finds the type there.
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
We have custom notations (in scope `%cpp_name`) defined to parse string constants in regular double quotes as bluerock.lang.cpp.syntax.core.name.
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



### Abstraction with Rep Predicates for classes

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

## Spec Examples
TODO:


## finding existing specs in the context

You can use the regular Coq `Search` vernacular to find specs of C++ function of a given fully qualified C++ name exists in the current context. This works because `cpp.spec` declares an instance of the typeclass
`bluerock.auto.cpp.database.spec.SpecFor.C`.
More concretely, the above spec (`foo_spec`) declares a typeclass instance of type `bluerock.auto.cpp.database.spec.SpecFor.C "foo()" foo_spec`. 
Thus, you can issue the following query to find out all the available specs for `foo()`.

```coqquery
Search (bluerock.auto.cpp.database.spec.SpecFor.C "foo()" _).
```

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


# Current Task
Write a Rep predicate for the following C++ class and a spec for the add method.
Ensure that the Rep predicate only takes 1 Gallina Z as the "mathematical model" argument, not 4 Zs.

```c++
class uint256 {
public:
  using limb_t = unsigned long long;          // assumes 64-bit limbs
  limb_t data[4];                             // little-endian: data[0] is least-significant

  uint256() : data{0, 0, 0, 0} {}

  void add(const uint256& other);
};
```

## Results of some relevant queries
>>> Check "unsigned long long"%cpp_type.
"unsigned long long"%cpp_type
     : bluerock.lang.cpp.syntax.core.type

# Response Format (IMPORTANT)
You can either give me (an elisp chat loop) the answer or ask me to run a Coq query like `Search/About/Check`.
Your response MUST either END with the Coq answer in a ```gallina ... ``` code block , or a Coq query inside a ```coqquery ... ```.
If you do not follow this format, I would not be able to respond to you properly.
Although I log and publish your responses in entirety, to respond to you, I ONLY LOOK AT THE LAST CODE BLOCK (```gallina or ```coqquery) IN YOUR RESPONSE.
If that is a ```coqquery block, I will send the queries to coqtop and give you back the responses.
If that is a ```gallina block, I will insert it into emacs+proof-general+company-coq and ask proof-general to check till the end.
I will wrap your solution in a `Module` so you should NOT wrap your soln in a module.
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



## Assistant 1

I want to make sure I use the right names and argument order for the arrayR and structR predicates in our C++ separation-logic library, so I’ll first look them up. 

```coqquery
Search arrayR.
Search structR.
```

## User 2

>>> Search arrayR.
bluerock.lang.cpp.logic.arr.arrayR_valid_base_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) {xs : Corelib.Init.Datatypes.list X},
    bluerock.iris.extra.bi.observe.Observe bluerock.lang.cpp.logic.heap_pred.valid.validR (bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.lang.cpp.logic.arr.arrayR_affine:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (t : bluerock.lang.cpp.syntax.core.type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list T),
    bluerock.iris.extra.bi.derived_laws.nary.Affine1 P → iris.bi.derived_connectives.Affine (bluerock.lang.cpp.logic.arr.arrayR t P l)
bluerock.lang.cpp.logic.arr.arrayR_persistent:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (t : bluerock.lang.cpp.syntax.core.type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list T),
    bluerock.iris.extra.bi.derived_laws.nary.Persistent1 P
    → iris.bi.derived_connectives.Persistent (bluerock.lang.cpp.logic.arr.arrayR t P l)
bluerock.lang.cpp.logic.arr.arrayR_timeless:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (t : bluerock.lang.cpp.syntax.core.type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list T),
    bluerock.iris.extra.bi.derived_laws.nary.Timeless1 P → iris.bi.derived_connectives.Timeless (bluerock.lang.cpp.logic.arr.arrayR t P l)
bluerock.cpp.array._at_arrayR_nil_B:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    bluerock.auto.core.hints.classes.bwd.Bwd (base |-> bluerock.lang.cpp.logic.arr.arrayR ty P [])
bluerock.cpp.array._at_arrayR_nil_F:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    bluerock.auto.core.hints.classes.fwd.Fwd (base |-> bluerock.lang.cpp.logic.arr.arrayR ty P [])
bluerock.lang.cpp.logic.arr.arrayR_fractional:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : stdpp.numbers.Qp → X → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (l : Corelib.Init.Datatypes.list X),
    bluerock.iris.extra.bi.fractional.nary.Fractional1 R
    → iris.bi.lib.fractional.Fractional (λ q : stdpp.numbers.Qp, bluerock.lang.cpp.logic.arr.arrayR ty (R q) l)
bluerock.lang.cpp.logic.arr.arrayR_cfractional:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : bluerock.lang.cpp.algebra.cfrac.cQp.t
                                                              → X → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list X),
    (∀ a : X, bluerock.lang.cpp.bi.cfractional.CFractional (λ q : bluerock.lang.cpp.algebra.cfrac.cQp.t, R q a))
    → bluerock.lang.cpp.bi.cfractional.CFractional
        (λ q : bluerock.lang.cpp.algebra.cfrac.cQp.t, bluerock.lang.cpp.logic.arr.arrayR ty (R q) l)
bluerock.lang.cpp.logic.arr.arrayR_valid_type_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (l : Corelib.Init.Datatypes.list X),
    bluerock.iris.extra.bi.observe.Observe [| stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of resolve ty) |]
      (bluerock.lang.cpp.logic.arr.arrayR ty R l)
bluerock.cpp.array._at_arrayR_cons_B:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : T) (ms : Corelib.Init.Datatypes.list T),
    bluerock.auto.core.hints.classes.bwd.Bwd (base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (m :: ms))
bluerock.cpp.array._at_arrayR_cons_F:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : T) (ms : Corelib.Init.Datatypes.list T),
    bluerock.auto.core.hints.classes.fwd.Fwd (base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (m :: ms))
bluerock.cpp.array.arrayR_nil_build_B:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of σ ty)
    → bluerock.auto.core.hints.classes.bwd.Bwd (l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR [])
bluerock.lang.cpp.logic.cstring.cstring.R'_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.logic.arr.arrayR "char" (λ c : Corelib.Numbers.BinNums.N, bluerock.lang.cpp.primitives.charR q c) [0%N]
    ⊢ bluerock.lang.cpp.logic.cstring.cstring.R' q ""
bluerock.lang.cpp.logic.cstring.cstring.R_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.logic.arr.arrayR "char" (λ c : Corelib.Numbers.BinNums.N, bluerock.lang.cpp.primitives.charR q c) [0%N]
    ⊢ bluerock.lang.cpp.logic.cstring.cstring.R q ""
bluerock.lang.cpp.logic.arr.arrayR_singleton:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (x : X),
    bluerock.lang.cpp.logic.arr.arrayR ty R [x] ⊣⊢ bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ R x
bluerock.lang.cpp.logic.heap_pred.any.anyR_array':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (t : bluerock.lang.cpp.syntax.core.type) (n : Corelib.Numbers.BinNums.N) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t n) q
    ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR t (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR t q)
         (bluerock.prelude.list_numbers.replicateN n ())
bluerock.cpp.array.arrayR_observe_Forall:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (Q : T → Prop) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) 
    (l : Corelib.Init.Datatypes.list T),
    (∀ x : T, bluerock.iris.extra.bi.observe.Observe [| Q x |] (R x))
    → bluerock.iris.extra.bi.observe.Observe [| Corelib.Lists.ListDef.Forall Q l |] (bluerock.lang.cpp.logic.arr.arrayR ty R l)
bluerock.lang.cpp.logic.heap_pred.any.anyR_array:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (t : bluerock.lang.cpp.syntax.core.type) (n : Corelib.Numbers.BinNums.N) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t n) q
    ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR t (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR t q)
         (Corelib.Lists.ListDef.repeat () (Stdlib.NArith.BinNat.N.to_nat n))
bluerock.cpp.array.arrayR_nil_build:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of σ ty)
    → bluerock.lang.cpp.logic.pred.L.valid_ptr l ⊢ l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR []
bluerock.cpp.array.arrayR_map':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A B : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : A → bluerock.lang.cpp.logic.rep_defs.Rep) (f : B → A) 
    (ls : Corelib.Init.Datatypes.list B),
    bluerock.lang.cpp.logic.arr.arrayR ty R (f <$> ls) ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty (λ x : B, R (f x)) ls
bluerock.lang.cpp.logic.arr.arrayR_as_cfractional:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (R' : X
                                                                                                              → 
                                                                                                              bluerock.lang.cpp.algebra.cfrac.cQp.t
                                                                                                              → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (l : Corelib.Init.Datatypes.list X) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    (∀ x : X, bluerock.lang.cpp.bi.cfractional.AsCFractional (R x) (R' x) q)
    → bluerock.lang.cpp.bi.cfractional.AsCFractional (bluerock.lang.cpp.logic.arr.arrayR ty R l)
        (λ q0 : bluerock.lang.cpp.algebra.cfrac.cQp.t, bluerock.lang.cpp.logic.arr.arrayR ty (λ x : X, R' x q0) l) q
bluerock.lang.cpp.logic.arr.arrayR_as_fractional:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (R' : X
                                                                                                              → 
                                                                                                              stdpp.numbers.Qp
                                                                                                              → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (l : Corelib.Init.Datatypes.list X) (q : stdpp.numbers.Qp),
    (∀ x : X, iris.bi.lib.fractional.AsFractional (R x) (R' x) q)
    → iris.bi.lib.fractional.AsFractional (bluerock.lang.cpp.logic.arr.arrayR ty R l)
        (λ q0 : stdpp.numbers.Qp, bluerock.lang.cpp.logic.arr.arrayR ty (λ x : X, R' x q0) l) q
bluerock.lang.cpp.logic.arr.arrayR_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type),
    bluerock.lang.cpp.logic.arr.arrayR ty R [] ⊣⊢ bluerock.lang.cpp.logic.heap_pred.valid.validR ∗
    [| stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of resolve ty) |]
bluerock.cpp.array.arrayR_nil_build'_B:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (sz : Corelib.Numbers.BinNums.N) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    (∀ x : bluerock.lang.cpp.semantics.genv.genv, bluerock.lang.cpp.semantics.types.size_of x ty = Corelib.Init.Datatypes.Some sz)
    → bluerock.auto.core.hints.classes.bwd.Bwd (l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR [])
bluerock.cpp.array.arrayR_nil_len0_B:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (A : Type) (l : Corelib.Init.Datatypes.list A),
    stdpp.base.length l = 0
    → ∀ ty : bluerock.lang.cpp.syntax.core.type,
        bluerock.lang.cpp.semantics.types.HasSize ty
        → ∀ (x : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (R : A → bluerock.lang.cpp.logic.rep_defs.Rep),
            bluerock.auto.core.hints.classes.bwd.Bwd (x |-> bluerock.lang.cpp.logic.arr.arrayR ty R l)
bluerock.cpp.array._at_arrayR_one_combine:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (x : T), bluerock.lang.cpp.logic.pred.L.type_ptr ty base ∗ base |-> P x ⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P [x]
bluerock.lang.cpp.logic.arr.arrayR_valid_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (xs : Corelib.Init.Datatypes.list X),
    (i <= stdpp.base.length xs)%nat
    → bluerock.iris.extra.bi.observe.Observe (.[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.validR)
        (bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.cpp.array._at_arrayR_one_split:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (x : T), base |-> bluerock.lang.cpp.logic.arr.arrayR ty P [x] ⊢ bluerock.lang.cpp.logic.pred.L.type_ptr ty base ∗ base |-> P x
bluerock.cpp.array.arrayR_uninitR_anyR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (T : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (xs : Corelib.Init.Datatypes.list ()),
    p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR T q) xs
    ⊢ p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR T q) xs
bluerock.lang.cpp.logic.arr.arrayR_sub_type_ptr_nat_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (xs : Corelib.Init.Datatypes.list X),
    (i < stdpp.base.length xs)%nat
    → bluerock.iris.extra.bi.observe.Observe (.[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty)
        (bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.cpp.array.arrayR_replicateN_anyR_uninitR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (t : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (sz : Corelib.Numbers.BinNums.N),
    p
    |-> bluerock.lang.cpp.logic.arr.arrayR t (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR t q)
          (bluerock.prelude.list_numbers.replicateN sz ())
    ⊢ p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t sz) q
bluerock.lang.cpp.logic.cstring.cstring.bufR_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : Corelib.Numbers.BinNums.Z),
    1 ≤ sz
    → bluerock.lang.cpp.logic.arr.arrayR "char" (λ _ : (), bluerock.lang.cpp.primitives.charR q 0)
        (Corelib.Lists.ListDef.repeat () (Stdlib.ZArith.BinInt.Z.to_nat sz))
      ⊢ bluerock.lang.cpp.logic.cstring.cstring.bufR q sz ""
monad.proofs.misc.learnArrUnsafe:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (e : Type) (t : bluerock.lang.cpp.syntax.core.type) (a
                                                                                                      a' : e
                                                                                                           → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (b b' : Corelib.Init.Datatypes.list e),
    bluerock.auto.core.internal.lib.learn_exist_interface.HLearn bluerock.auto.core.internal.lib.learn_exist_interface.LearnNormal
      (bluerock.lang.cpp.logic.arr.arrayR t a b) (bluerock.lang.cpp.logic.arr.arrayR t a' b') [a = a'; b = b']
bluerock.lang.cpp.logic.cstring.cstring.bufR'_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : Corelib.Numbers.BinNums.Z),
    1 ≤ sz
    → bluerock.lang.cpp.logic.arr.arrayR "char" (λ _ : (), bluerock.lang.cpp.primitives.charR q 0)
        (Corelib.Lists.ListDef.repeat () (Stdlib.ZArith.BinInt.Z.to_nat sz))
      ⊢ bluerock.lang.cpp.logic.cstring.cstring.bufR' q sz ""
bluerock.cpp.array.arrayR_nil_build':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (sz : Corelib.Numbers.BinNums.N) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    (∀ x : bluerock.lang.cpp.semantics.genv.genv, bluerock.lang.cpp.semantics.types.size_of x ty = Corelib.Init.Datatypes.Some sz)
    → bluerock.lang.cpp.logic.pred.L.valid_ptr l ⊢ l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR []
bluerock.lang.cpp.logic.arr.arrayR_mono:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type),
    Corelib.Classes.Morphisms.Proper
      (Corelib.Classes.Morphisms.pointwise_relation X iris.bi.interface.bi_entails ==>
       Corelib.Init.Logic.eq ==> iris.bi.interface.bi_entails)
      (bluerock.lang.cpp.logic.arr.arrayR ty)
bluerock.cpp.array.arrayR_nil_len0:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (A : Type) (l : Corelib.Init.Datatypes.list A),
    stdpp.base.length l = 0
    → ∀ ty : bluerock.lang.cpp.syntax.core.type,
        bluerock.lang.cpp.semantics.types.HasSize ty
        → ∀ (x : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (R : A → bluerock.lang.cpp.logic.rep_defs.Rep),
            bluerock.lang.cpp.logic.pred.L.valid_ptr x ⊢ x |-> bluerock.lang.cpp.logic.arr.arrayR ty R l
bluerock.lang.cpp.logic.zstring.zstring.R'_unfold:
  ∀ (ct : bluerock.lang.cpp.syntax.preliminary.char_type) {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} 
    {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (zs : bluerock.lang.cpp.logic.zstring.zstring.t),
    bluerock.lang.cpp.logic.zstring.zstring.R' ct q zs
    ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tchar_ ct)
         (λ c : Corelib.Numbers.BinNums.N,
            bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tchar_ ct) q
              (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar c))
         zs ∗
    [| bluerock.lang.cpp.logic.zstring.zstring.WF' ct zs |]
bluerock.lang.cpp.logic.zstring.zstring.R_unfold:
  ∀ (ct : bluerock.lang.cpp.syntax.preliminary.char_type) {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} 
    {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (zs : bluerock.lang.cpp.logic.zstring.zstring.t),
    bluerock.lang.cpp.logic.zstring.zstring.R ct q zs
    ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tchar_ ct)
         (λ c : Corelib.Numbers.BinNums.N,
            bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tchar_ ct) q
              (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar c))
         zs ∗
    [| bluerock.lang.cpp.logic.zstring.zstring.WF ct zs |]
bluerock.lang.cpp.logic.arr.arrayR_validR_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Numbers.BinNums.Z) 
    (xs : Corelib.Init.Datatypes.list X),
    0 ≤ i ≤ stdpp.base.length xs
    → bluerock.iris.extra.bi.observe.Observe (.[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.validR)
        (bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.lang.cpp.logic.cstring.cstring.R'_unfold:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (cstr : bluerock.lang.cpp.logic.cstring.cstring.t),
    bluerock.lang.cpp.logic.cstring.cstring.R' q cstr
    ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR "char" (λ c : Corelib.Numbers.BinNums.N, bluerock.lang.cpp.primitives.charR q c)
         (bluerock.lang.cpp.logic.cstring.cstring.to_zstring cstr) ∗
    [| bluerock.lang.cpp.logic.cstring.cstring.WF' cstr |]
bluerock.lang.cpp.logic.cstring.cstring.R_unfold:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (cstr : bluerock.lang.cpp.logic.cstring.cstring.t),
    bluerock.lang.cpp.logic.cstring.cstring.R q cstr
    ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR "char" (λ c : Corelib.Numbers.BinNums.N, bluerock.lang.cpp.primitives.charR q c)
         (bluerock.lang.cpp.logic.cstring.cstring.to_zstring cstr) ∗
    [| bluerock.lang.cpp.logic.cstring.cstring.WF cstr |]
bluerock.lang.cpp.logic.arr.arrayR_sep:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {ty : bluerock.lang.cpp.syntax.core.type} {V : Type} (A B : V → bluerock.lang.cpp.logic.rep_defs.Rep) (xs : 
                                                                                                           Corelib.Init.Datatypes.list V),
    bluerock.lang.cpp.logic.arr.arrayR ty (λ v : V, A v ∗ B v) xs ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty (λ v : V, A v) xs ∗
    bluerock.lang.cpp.logic.arr.arrayR ty (λ v : V, B v) xs
bluerock.lang.cpp.logic.core_string.string_bytesR.unlock:
  @bluerock.lang.cpp.logic.core_string.string_bytesR =
  λ (thread_info : iris.bi.monpred.biIndex) (_Σ : iris.base_logic.lib.iprop.gFunctors) (Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ) (σ : bluerock.lang.cpp.semantics.genv.genv) 
    (cty : bluerock.lang.cpp.syntax.preliminary.char_type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (s : bluerock.lang.cpp.syntax.literal_string.literal_string.t),
    let ty := bluerock.lang.cpp.syntax.core.Tchar_ cty in
    bluerock.lang.cpp.logic.arr.arrayR ty
      (λ c : Corelib.Numbers.BinNums.N,
         bluerock.lang.cpp.logic.heap_pred.primR ty q (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.N_to_char cty c))
      (bluerock.lang.cpp.syntax.literal_string.literal_string.to_list_N s ++ [0%N])
bluerock.lang.cpp.logic.arr.arrayR_sub_svalidR_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Numbers.BinNums.Z) 
    (xs : Corelib.Init.Datatypes.list X),
    0 ≤ i < stdpp.base.length xs
    → bluerock.iris.extra.bi.observe.Observe (.[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.svalidR)
        (bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.lang.cpp.logic.arr.arrayR_combine:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (xs : Corelib.Init.Datatypes.list X),
    bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs) ∗
    .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn i xs) ⊢ bluerock.lang.cpp.logic.arr.arrayR ty R xs
bluerock.cpp.array.arrayR_singl_build_T_uchar:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (x : Corelib.Numbers.BinNums.Z),
    l |-> bluerock.lang.cpp.primitives.ucharR q x
    ⊢ l
      |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.primitives.ucharR q c) [x]
bluerock.lang.cpp.logic.arr.arrayR_sub_type_ptr_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Numbers.BinNums.Z) 
    (xs : Corelib.Init.Datatypes.list X),
    0 ≤ i < stdpp.base.length xs
    → bluerock.iris.extra.bi.observe.Observe (.[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty)
        (bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.cpp.array._at_arrayR_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    base |-> bluerock.lang.cpp.logic.arr.arrayR ty P [] ⊣⊢ □ bluerock.lang.cpp.logic.pred.L.valid_ptr base ∗
    [| bluerock.lang.cpp.semantics.types.HasSize ty |]
monad.proofs.misc.obsUintArrayR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (l : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.Z),
    bluerock.iris.extra.bi.observe.Observe [| ∀ a : Corelib.Numbers.BinNums.Z, Stdlib.Lists.List.In a l → 0 ≤ a |]
      (p
       |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned int"
             (λ i : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR "unsigned int" q i) l)
bluerock.cpp.array._at_arrayR_valid_obs__N:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {R : T → bluerock.lang.cpp.logic.rep_defs.Rep} {ty : bluerock.lang.cpp.syntax.core.type} (xs : Corelib.Init.Datatypes.list T) 
    (i : Corelib.Numbers.BinNums.N) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    (i ≤ bluerock.prelude.list_numbers.lengthN xs)%N
    → bluerock.iris.extra.bi.observe.Observe (bluerock.lang.cpp.logic.pred.L.valid_ptr (p .[ ty ! i ]))
        (p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.cpp.array.anyR_Tarray_0_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (n : Corelib.Numbers.BinNums.N),
    n = 0%N
    → ∀ (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
        l |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray "unsigned char" n) q
        ⊢ l |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" TR []
bluerock.lang.cpp.logic.arr.arrayR_proper_ho.arrayR_mono_ho:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {H : stdpp.base.Equiv T} (t : bluerock.lang.cpp.syntax.core.type),
    Corelib.Classes.Morphisms.Proper
      ((stdpp.base.equiv ==> iris.bi.interface.bi_entails) ==> stdpp.base.equiv ==> iris.bi.interface.bi_entails)
      (bluerock.lang.cpp.logic.arr.arrayR t)
bluerock.cpp.array.arrayR_map:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A B : Type} (ty : bluerock.lang.cpp.syntax.core.type) (f : A → B) (g : B → A) (r : A → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (la : Corelib.Init.Datatypes.list A),
    (∀ a : A, a ∈ la → g (f a) = a)
    → bluerock.lang.cpp.logic.arr.arrayR ty (λ b : B, r (g b)) (Corelib.Lists.ListDef.map f la)
      ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty r la
monad.proofs.misc.generalize_arrayR_loopinv_produce:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (i : Corelib.Init.Datatypes.nat) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (xs : Corelib.Init.Datatypes.list X),
    i = stdpp.base.length xs
    → p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs ⊣⊢ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs)
bluerock.lang.cpp.logic.arr._at_arrayR_valid_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (xs : Corelib.Init.Datatypes.list X) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    (i <= stdpp.base.length xs)%nat
    → bluerock.iris.extra.bi.observe.Observe (p .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.validR)
        (p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.lang.cpp.logic.arr._at_arrayR_sub_type_ptrR_nat_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (xs : Corelib.Init.Datatypes.list X),
    (i < stdpp.base.length xs)%nat
    → bluerock.iris.extra.bi.observe.Observe (p .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty)
        (p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs)
bluerock.lang.cpp.logic.arr.arrayR_proper:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type),
    Corelib.Classes.Morphisms.Proper
      (Corelib.Classes.Morphisms.pointwise_relation X stdpp.base.equiv ==> Corelib.Init.Logic.eq ==> stdpp.base.equiv)
      (bluerock.lang.cpp.logic.arr.arrayR ty)
monad.proofs.misc.arrayR_nils:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} {T : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : T
                                                                                                           → bluerock.lang.cpp.logic.rep_defs.Rep),
    bluerock.lang.cpp.logic.arr.arrayR ty R [] =
    (.[ ty ! 0%nat ] |-> bluerock.lang.cpp.logic.heap_pred.valid.validR ∗
     [| stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of CU ty) |] ∗ emp)%I
bluerock.cpp.array.arrayR_app__N:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {R : T → bluerock.lang.cpp.logic.rep_defs.Rep} {ty : bluerock.lang.cpp.syntax.core.type} (xs
                                                                                                         ys : Corelib.Init.Datatypes.list T),
    bluerock.lang.cpp.logic.arr.arrayR ty R (xs ++ ys) ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty R xs ∗
    .[ ty ! bluerock.prelude.list_numbers.lengthZ xs ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R ys
bluerock.lang.cpp.logic.arr.arrayR_app:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (xs
                                                                                                         ys : Corelib.Init.Datatypes.list X),
    bluerock.lang.cpp.logic.arr.arrayR ty R (xs ++ ys) ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty R xs ∗
    .[ ty ! stdpp.base.length xs ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R ys
bluerock.lang.cpp.logic.arr.arrayR_split:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (xs : Corelib.Init.Datatypes.list X),
    (i <= stdpp.base.length xs)%nat
    → bluerock.lang.cpp.logic.arr.arrayR ty R xs ⊢ bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs) ∗
      .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn i xs)
bluerock.cpp.oprimR.arrayR_uninitR_oprimR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (T : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (n : Corelib.Numbers.BinNums.N),
    p
    |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR T q)
          (bluerock.prelude.list_numbers.replicateN n ())
    ⊢ p
      |-> bluerock.lang.cpp.logic.arr.arrayR T
            (λ ov : Corelib.Init.Datatypes.option bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val,
               bluerock.cpp.oprimR.oprimR T q ov)
            (bluerock.prelude.list_numbers.replicateN n Corelib.Init.Datatypes.None)
bluerock.cpp.array.arrayR_combine2:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (i : Corelib.Numbers.BinNums.N) {T : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (la lb : Corelib.Init.Datatypes.list T),
    Stdlib.NArith.BinNat.N.of_nat (stdpp.base.length la) = i
    → .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R lb ∗ bluerock.lang.cpp.logic.arr.arrayR ty R la
      ⊢ bluerock.lang.cpp.logic.arr.arrayR ty R (la ++ lb)
bluerock.cpp.array.arrayR_replicateN_anyR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (t : bluerock.lang.cpp.syntax.core.type) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (R : bluerock.lang.cpp.algebra.cfrac.cQp.t → A → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (sz : Corelib.Numbers.BinNums.N) (a : A),
    (∀ (q0 : bluerock.lang.cpp.algebra.cfrac.cQp.t) (a0 : A), R q0 a0 ⊢ bluerock.lang.cpp.logic.heap_pred.anyR t q0)
    → p |-> bluerock.lang.cpp.logic.arr.arrayR t (R q) (bluerock.prelude.list_numbers.replicateN sz a)
      ⊢ p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t sz) q
bluerock.lang.cpp.logic.arr.arrayR_cons:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (x : X) 
    (xs : Corelib.Init.Datatypes.list X),
    bluerock.lang.cpp.logic.arr.arrayR ty R (x :: xs) ⊣⊢ bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ 
    R x ∗ .[ ty ! 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs
bluerock.cpp.array.into_sep_arrayR_cons:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (R : A → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (Q : bluerock.lang.cpp.logic.rep_defs.Rep) 
    (l : Corelib.Init.Datatypes.list A) (x : A) (l' : Corelib.Init.Datatypes.list A),
    iris.proofmode.classes.IsCons l x l'
    → iris.proofmode.classes_make.MakeSep (R x) (.[ ty ! 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R l') Q
      → iris.proofmode.classes.IntoSep (bluerock.lang.cpp.logic.arr.arrayR ty R l) (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty) Q
bluerock.lang.cpp.logic.arr.arrayR_pureR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} {ty : bluerock.lang.cpp.syntax.core.type} (R : X → bluerock.iris.extra.base_logic.mpred.mpred) (l : 
                                                                                                               Corelib.Init.Datatypes.list X),
    bluerock.lang.cpp.logic.arr.arrayR ty (λ v : X, bluerock.lang.cpp.logic.rep_defs.pureR (R v)) l
    ⊣⊢ bluerock.lang.cpp.logic.rep_defs.pureR ([∗ list] x ∈ l, R x) ∗ bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : X, emp) l
bluerock.lang.cpp.logic.arr.arrayR_proper_ho.arrayR_proper_ho:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {H : stdpp.base.Equiv T} (t : bluerock.lang.cpp.syntax.core.type),
    Corelib.Classes.Morphisms.Proper ((stdpp.base.equiv ==> stdpp.base.equiv) ==> stdpp.base.equiv ==> stdpp.base.equiv)
      (bluerock.lang.cpp.logic.arr.arrayR t)
bluerock.lang.cpp.logic.arr.arrayR_flip_mono:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (ty : bluerock.lang.cpp.syntax.core.type),
    Corelib.Classes.Morphisms.Proper
      (Corelib.Classes.Morphisms.pointwise_relation X (Corelib.Program.Basics.flip iris.bi.interface.bi_entails) ==>
       Corelib.Init.Logic.eq ==> Corelib.Program.Basics.flip iris.bi.interface.bi_entails)
      (bluerock.lang.cpp.logic.arr.arrayR ty)
bluerock.lang.cpp.logic.arr._at_arrayR_sub_type_ptrR_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Numbers.BinNums.Z) 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (xs : Corelib.Init.Datatypes.list X),
    0 ≤ i < stdpp.base.length xs
    → bluerock.iris.extra.bi.observe.Observe (p .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty)
        (p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs)
monad.proofs.misc.generalize_arrayR_loopinv:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (i : Corelib.Init.Datatypes.nat) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (xs : Corelib.Init.Datatypes.list X),
    i = 0%nat
    → p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs
      ⊣⊢ p .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn i xs)
bluerock.lang.cpp.logic.arr.arrayR_cons_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (x : X) 
    (xs : Corelib.Init.Datatypes.list X),
    (∀ x0 : X, bluerock.iris.extra.bi.observe.Observe (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty) (R x0))
    → bluerock.lang.cpp.logic.arr.arrayR ty R (x :: xs) ⊣⊢ R x ∗ .[ ty ! 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs
bluerock.cpp.array.arrayR_nil_build_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of σ ty)
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [bluerock.lang.cpp.logic.pred.L.valid_ptr l] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
        [l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR []]
bluerock.lang.cpp.logic.arr.arrayR_agree:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X T : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : T → X → bluerock.lang.cpp.logic.rep_defs.Rep) (q1 q2 : T) 
    (l k : Corelib.Init.Datatypes.list X),
    (∀ (q3 q4 : T) (x1 x2 : X), bluerock.iris.extra.bi.observe.Observe2 [| x1 = x2 |] (R q3 x1) (R q4 x2))
    → stdpp.base.length l = stdpp.base.length k
      → bluerock.iris.extra.bi.observe.Observe2 [| l = k |] (bluerock.lang.cpp.logic.arr.arrayR ty (R q1) l)
          (bluerock.lang.cpp.logic.arr.arrayR ty (R q2) k)
bluerock.cpp.array.arrayR_anyR_f:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (f : T → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (n : Corelib.Init.Datatypes.nat) (ty : bluerock.lang.cpp.syntax.core.type) (l : Corelib.Init.Datatypes.list T) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    n = stdpp.base.length l
    → loc |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ x : T, bluerock.lang.cpp.logic.heap_pred.primR ty q (f x)) l
      ⊢ loc
        |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR ty q)
              (Corelib.Lists.ListDef.repeat () n)
bluerock.cpp.array.UNSAFE_LearnArrayPrimEqual.UNSAFE_learn_arrayR_primR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} (Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ) (resolve : bluerock.lang.cpp.semantics.genv.genv) 
    {p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr} {q1 q2 : bluerock.lang.cpp.algebra.cfrac.cQp.t} 
    {x y : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.Z} {T T' : bluerock.lang.cpp.syntax.core.type},
    bluerock.auto.core.internal.lib.learn_exist_interface.HLearn bluerock.auto.core.internal.lib.learn_exist_interface.LearnAlways
      (p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR T' q1 c) x)
      (p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR T' q2 c) y)
      [y = x]
bluerock.lang.cpp.logic.arr.arrayR_ne:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) {T : iris.algebra.ofe.ofe} (n : Corelib.Init.Datatypes.nat),
    Corelib.Classes.Morphisms.Proper
      (Corelib.Classes.Morphisms.pointwise_relation T (iris.algebra.ofe.dist n) ==> Corelib.Init.Logic.eq ==> iris.algebra.ofe.dist n)
      (bluerock.lang.cpp.logic.arr.arrayR ty)
bluerock.cpp.array.arrayR_app_build_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (x1 x2 : Corelib.Init.Datatypes.list T),
    bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
      [l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR x1] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
      [l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR (x1 ++ x2)]
bluerock.cpp.array.anyR_arrayR_shatter:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (T : bluerock.lang.cpp.syntax.core.type) (n : Corelib.Numbers.BinNums.N) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (o : Corelib.Numbers.BinNums.N),
    bluerock.lang.cpp.semantics.types.size_of σ T = Corelib.Init.Datatypes.Some o
    → l |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray T n) q
      ⊣⊢ l
         |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR T q)
               (Corelib.Lists.ListDef.repeat () (Stdlib.NArith.BinNat.N.to_nat n))
bluerock.cpp.array.arrayR_app_build:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (x1 x2 : Corelib.Init.Datatypes.list T),
    l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR x1
    ⊢ l .[ ty ! stdpp.base.length x1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty TR x2 -∗
      l |-> bluerock.lang.cpp.logic.arr.arrayR ty TR (x1 ++ x2)
bluerock.lang.cpp.logic.arr.arrayR_snoc:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (xs : Corelib.Init.Datatypes.list X) 
    (y : X),
    bluerock.lang.cpp.logic.arr.arrayR ty R (xs ++ [y]) ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty R xs ∗
    .[ ty ! stdpp.base.length xs ] |-> (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ R y)
bluerock.cpp.array.observe_arrayR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (P : Corelib.Numbers.BinNums.Z → A → bluerock.lang.cpp.logic.rep_defs.RepI) (T : bluerock.lang.cpp.syntax.core.type) 
    (R : A → bluerock.lang.cpp.logic.rep_defs.Rep) (xs : Corelib.Init.Datatypes.list A),
    (∀ (i : Corelib.Numbers.BinNums.Z) (x : A), bluerock.iris.extra.bi.observe.Observe (P i x) (.[ T ! i ] |-> R x))
    → bluerock.iris.extra.bi.observe.Observe ([∗ list] i↦x ∈ xs, P i x) (bluerock.lang.cpp.logic.arr.arrayR T R xs)
bluerock.cpp.array.arrayRpure:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) {T : Type} (R1 : T → bluerock.lang.cpp.logic.rep_defs.Rep) (R2 : T
                                                                                                               → bluerock.iris.extra.base_logic.mpred.mpred) 
    (l : Corelib.Init.Datatypes.list T),
    bluerock.lang.cpp.logic.arr.arrayR ty (λ x : T, bluerock.lang.cpp.logic.rep_defs.pureR (R2 x) ∗ R1 x) l
    ⊣⊢ bluerock.lang.cpp.logic.rep_defs.pureR ([∗ list] x ∈ l, R2 x) ∗ bluerock.lang.cpp.logic.arr.arrayR ty R1 l
monad.proofs.misc.arrayR_combinep:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} {T : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : T
                                                                                                           → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (i : Corelib.Init.Datatypes.nat) (xs : Corelib.Init.Datatypes.list T) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs) ∗
    p .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn i xs)
    ⊢ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs
bluerock.cpp.array.arrayR_combine:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (i : Corelib.Init.Datatypes.nat) (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (m : Corelib.Init.Datatypes.list T),
    base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.firstn i m) ∗
    base .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.skipn i m)
    ⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P m
bluerock.lang.cpp.logic.arr.arrayR_agree_prefix:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X T : Type} (ty : bluerock.lang.cpp.syntax.core.type) (R : T → X → bluerock.lang.cpp.logic.rep_defs.Rep) (q1 q2 : T) 
    (l k : Corelib.Init.Datatypes.list X),
    (∀ (q3 q4 : T) (x1 x2 : X), bluerock.iris.extra.bi.observe.Observe2 [| x1 = x2 |] (R q3 x1) (R q4 x2))
    → (stdpp.base.length l <= stdpp.base.length k)%nat
      → bluerock.iris.extra.bi.observe.Observe2 [| l = Corelib.Lists.ListDef.firstn (stdpp.base.length l) k |]
          (bluerock.lang.cpp.logic.arr.arrayR ty (R q1) l) (bluerock.lang.cpp.logic.arr.arrayR ty (R q2) k)
bluerock.lang.cpp.logic.arr.arrayR_proper_ho.arrayR_ne_ho:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : iris.algebra.ofe.ofe} (t : bluerock.lang.cpp.syntax.core.type) (n : Corelib.Init.Datatypes.nat),
    Corelib.Classes.Morphisms.Proper
      ((iris.algebra.ofe.dist n ==> iris.algebra.ofe.dist n) ==> iris.algebra.ofe.dist n ==> iris.algebra.ofe.dist n)
      (bluerock.lang.cpp.logic.arr.arrayR t)
bluerock.cpp.array.arrayR_uninitR_anyR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (T : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (xs : Corelib.Init.Datatypes.list ()),
    bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
      [p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR T q) xs] [tele]
      bluerock.auto.core.hints.classes.cancelx.CoverAny
      [p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR T q) xs]
bluerock.cpp.array.arrayR_anyR_take:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (f : T → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (n : Corelib.Init.Datatypes.nat) (l : Corelib.Init.Datatypes.list T) (ty : bluerock.lang.cpp.syntax.core.type) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    n ≤ stdpp.base.length l
    → loc
      |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ x : T, bluerock.lang.cpp.logic.heap_pred.primR ty q (f x))
            (Corelib.Lists.ListDef.firstn n l)
      ⊢ loc
        |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR ty q)
              (Corelib.Lists.ListDef.repeat () n)
bluerock.cpp.array.arrayR_replicateN_anyR_uninitR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (t : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (sz : Corelib.Numbers.BinNums.N),
    bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
      [p
       |-> bluerock.lang.cpp.logic.arr.arrayR t (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR t q)
             (bluerock.prelude.list_numbers.replicateN sz ())]
      [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
      [p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t sz) q]
bluerock.lang.cpp.logic.arr._at_arrayR_valid:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (i : Corelib.Init.Datatypes.nat) 
    (xs : Corelib.Init.Datatypes.list X) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    (i <= stdpp.base.length xs)%nat
    → p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs ⊣⊢ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs ∗
      p .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.validR
bluerock.cpp.array.arrayR_split:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (i : Corelib.Init.Datatypes.nat) (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (m : Corelib.Init.Datatypes.list T),
    (i <= stdpp.base.length m)%nat
    → base |-> bluerock.lang.cpp.logic.arr.arrayR ty P m
      ⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.firstn i m) ∗
      base .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.skipn i m)
bluerock.cpp.array._at_arrayR_cons:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : T) (ms : Corelib.Init.Datatypes.list T),
    base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (m :: ms) ⊣⊢ bluerock.lang.cpp.logic.pred.L.type_ptr ty base ∗ 
    base |-> P m ∗ base .[ ty ! 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty P ms
bluerock.lang.cpp.logic.arr.arrayR_proper_ho.arrayR_flip_mono_ho:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {H : stdpp.base.Equiv T} (t : bluerock.lang.cpp.syntax.core.type),
    Corelib.Classes.Morphisms.Proper
      ((stdpp.base.equiv --> Corelib.Program.Basics.flip iris.bi.interface.bi_entails) ==>
       stdpp.base.equiv --> Corelib.Program.Basics.flip iris.bi.interface.bi_entails)
      (bluerock.lang.cpp.logic.arr.arrayR t)
bluerock.cpp.array.arrayR_singl_build_T_uchar_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (x : Corelib.Numbers.BinNums.Z),
    bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
      [l |-> bluerock.lang.cpp.primitives.ucharR q x] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
      [l
       |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.primitives.ucharR q c) [x]]
bluerock.cpp.array.anyR_Tarray_0_nil_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (T : Type) (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (n : Corelib.Numbers.BinNums.N),
    n = 0%N
    → ∀ (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (l : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
        bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
          [l |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray "unsigned char" n) q] [tele]
          bluerock.auto.core.hints.classes.cancelx.CoverAny [l |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" TR []]
bluerock.cpp.array.arrayR_anyR_array_CX:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (Vctr : A → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (T : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (xs : Corelib.Init.Datatypes.list A) 
    (len : Corelib.Numbers.BinNums.N),
    bluerock.prelude.list_numbers.lengthN xs = len
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [p |-> bluerock.lang.cpp.logic.arr.arrayR T (λ v : A, bluerock.lang.cpp.logic.heap_pred.primR T q (Vctr v)) xs] [tele]
        bluerock.auto.core.hints.classes.cancelx.CoverAny
        [p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray T len) q]
bluerock.cpp.array.arrayR_unsplit_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (i : Corelib.Numbers.BinNums.N) (T : Type) (l : 
                                                                                                               Corelib.Init.Datatypes.list T) 
    (v : T) (ty : bluerock.lang.cpp.syntax.core.type) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep),
    Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat i) = Corelib.Init.Datatypes.Some v
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [loc |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn (Stdlib.NArith.BinNat.N.to_nat i) l)] [tele]
        bluerock.auto.core.hints.classes.cancelx.CoverAny [loc |-> bluerock.lang.cpp.logic.arr.arrayR ty R l]
bluerock.cpp.oprimR.arrayR_uninitR_oprimR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (T : bluerock.lang.cpp.syntax.core.type) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (n : Corelib.Numbers.BinNums.N),
    bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
      [p
       |-> bluerock.lang.cpp.logic.arr.arrayR T (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR T q)
             (bluerock.prelude.list_numbers.replicateN n ())]
      [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
      [p
       |-> bluerock.lang.cpp.logic.arr.arrayR T
             (λ ov : Corelib.Init.Datatypes.option bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val,
                bluerock.cpp.oprimR.oprimR T q ov)
             (bluerock.prelude.list_numbers.replicateN n Corelib.Init.Datatypes.None)]
bluerock.cpp.array.arrayR_replicateN_anyR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (A : Type) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (t : bluerock.lang.cpp.syntax.core.type) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (R : bluerock.lang.cpp.algebra.cfrac.cQp.t → A → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (sz : Corelib.Numbers.BinNums.N) (a : A),
    (∀ (q0 : bluerock.lang.cpp.algebra.cfrac.cQp.t) (a0 : A), R q0 a0 ⊢ bluerock.lang.cpp.logic.heap_pred.anyR t q0)
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [p |-> bluerock.lang.cpp.logic.arr.arrayR t (R q) (bluerock.prelude.list_numbers.replicateN sz a)] [tele]
        bluerock.auto.core.hints.classes.cancelx.CoverAny
        [p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t sz) q]
bluerock.cpp.array.arrayR_put1:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) 
    (TR : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list T) (x : T),
    Stdlib.Lists.List.nth_error l 0 = Corelib.Init.Datatypes.Some x
    → loc |-> TR x
      ⊢ bluerock.lang.cpp.logic.pred.L.type_ptr ty loc ∗
        loc .[ ty ! 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty TR (Corelib.Lists.ListDef.skipn 1 l) -∗
        loc |-> bluerock.lang.cpp.logic.arr.arrayR ty TR l
bluerock.lang.cpp.logic.cstring.cstring.bufR'_unfold:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : Corelib.Numbers.BinNums.Z) (cstr : bluerock.lang.cpp.logic.cstring.cstring.t),
    bluerock.lang.cpp.logic.cstring.cstring.bufR' q sz cstr ⊣⊢ [| bluerock.lang.cpp.logic.cstring.cstring.size cstr ≤ sz |] ∗
    bluerock.lang.cpp.logic.cstring.cstring.R' q cstr ∗
    .[ "char" ! bluerock.lang.cpp.logic.cstring.cstring.size cstr ]
    |-> bluerock.lang.cpp.logic.arr.arrayR "char" (λ _ : (), bluerock.lang.cpp.primitives.charR q 0)
          (Corelib.Lists.ListDef.repeat () (Stdlib.ZArith.BinInt.Z.to_nat (sz - bluerock.lang.cpp.logic.cstring.cstring.size cstr)))
bluerock.lang.cpp.logic.cstring.cstring.bufR_unfold:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : Corelib.Numbers.BinNums.Z) (cstr : bluerock.lang.cpp.logic.cstring.cstring.t),
    bluerock.lang.cpp.logic.cstring.cstring.bufR q sz cstr ⊣⊢ [| bluerock.lang.cpp.logic.cstring.cstring.size cstr ≤ sz |] ∗
    bluerock.lang.cpp.logic.cstring.cstring.R q cstr ∗
    .[ "char" ! bluerock.lang.cpp.logic.cstring.cstring.size cstr ]
    |-> bluerock.lang.cpp.logic.arr.arrayR "char" (λ _ : (), bluerock.lang.cpp.primitives.charR q 0)
          (Corelib.Lists.ListDef.repeat () (Stdlib.ZArith.BinInt.Z.to_nat (sz - bluerock.lang.cpp.logic.cstring.cstring.size cstr)))
bluerock.cpp.array.arrayR_inrange_valid_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (T : Type) (x : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (i : Corelib.Numbers.BinNums.N) (ty : bluerock.lang.cpp.syntax.core.type) 
    (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list T) (v : T),
    Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat i) = Corelib.Init.Datatypes.Some v
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [x |-> bluerock.lang.cpp.logic.arr.arrayR ty R l] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
        [bluerock.lang.cpp.logic.pred.L.valid_ptr (x .[ ty ! i ])]
bluerock.lang.cpp.logic.zstring.zstring.bufR'_unfold:
  ∀ (ct : bluerock.lang.cpp.syntax.preliminary.char_type) {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} 
    {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : Corelib.Numbers.BinNums.Z) (cstr : bluerock.lang.cpp.logic.zstring.zstring.t),
    bluerock.lang.cpp.logic.zstring.zstring.bufR' ct q sz cstr ⊣⊢ [| bluerock.lang.cpp.logic.zstring.zstring.size cstr ≤ sz |] ∗
    bluerock.lang.cpp.logic.zstring.zstring.R' ct q cstr ∗
    .[ bluerock.lang.cpp.syntax.core.Tchar_ ct ! bluerock.lang.cpp.logic.zstring.zstring.size cstr ]
    |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tchar_ ct)
          (λ _ : (),
             bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tchar_ ct) q
               (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar 0))
          (Corelib.Lists.ListDef.repeat () (Stdlib.ZArith.BinInt.Z.to_nat (sz - bluerock.lang.cpp.logic.zstring.zstring.size cstr)))
bluerock.lang.cpp.logic.zstring.zstring.bufR_unfold:
  ∀ (ct : bluerock.lang.cpp.syntax.preliminary.char_type) {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} 
    {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : Corelib.Numbers.BinNums.Z) (zs : bluerock.lang.cpp.logic.zstring.zstring.t),
    bluerock.lang.cpp.logic.zstring.zstring.bufR ct q sz zs ⊣⊢ [| bluerock.lang.cpp.logic.zstring.zstring.size zs ≤ sz |] ∗
    bluerock.lang.cpp.logic.zstring.zstring.R ct q zs ∗
    .[ bluerock.lang.cpp.syntax.core.Tchar_ ct ! bluerock.lang.cpp.logic.zstring.zstring.size zs ]
    |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tchar_ ct)
          (λ _ : (),
             bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tchar_ ct) q
               (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar 0))
          (Corelib.Lists.ListDef.repeat () (Stdlib.ZArith.BinInt.Z.to_nat (sz - bluerock.lang.cpp.logic.zstring.zstring.size zs)))
bluerock.lang.cpp.logic.arr.arrayR_snoc_obs:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (xs : Corelib.Init.Datatypes.list X) (y : X),
    (∀ x : X, bluerock.iris.extra.bi.observe.Observe (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty) (R x))
    → p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (xs ++ [y]) ⊣⊢ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs ∗
      p .[ ty ! stdpp.base.length xs ] |-> R y
bluerock.cpp.array._arrayR_put1'_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (l : 
                                                                                                               Corelib.Init.Datatypes.list
                                                                                                               Corelib.Numbers.BinNums.Z) 
    (x : Corelib.Numbers.BinNums.Z),
    Stdlib.Lists.List.nth_error l 0 = Corelib.Init.Datatypes.Some x
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [loc |-> bluerock.lang.cpp.primitives.ucharR q x] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
        [loc
         |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.primitives.ucharR q c) l]
bluerock.cpp.array.arrayR_anyR_combine_char_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (b : bluerock.lang.cpp.syntax.preliminary.char_type) (ct : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    Corelib.Numbers.BinNums.N
    → ∀ (zs : Corelib.Numbers.BinNums.N) (H : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.N),
        (bluerock.prelude.list_numbers.lengthN H ≤ zs)%N
        → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
            [ct
             |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tchar_ b)
                   (λ c : Corelib.Numbers.BinNums.N,
                      bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tchar_ b) 1$m
                        (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar c))
                   H]
            [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
            [ct
             |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray (bluerock.lang.cpp.syntax.core.Tchar_ b) zs)
                   1$m]
bluerock.auto.cpp.hints.layout.implicit_destruct_tblockR_arrayR_primR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.type) {T : Type} 
    (f : T → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (ls : Corelib.Init.Datatypes.list T) (len : Corelib.Numbers.BinNums.N) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    Stdlib.NArith.BinNat.N.of_nat (stdpp.base.length ls) = len
    → q = 1%Qp
      → p |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ v : T, bluerock.lang.cpp.logic.heap_pred.primR ty q (f v)) ls
        ⊢ |={↑bluerock.lang.cpp.logic.pred.pred_ns}=>
            p |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.syntax.core.Tarray ty len) q
monad.proofs.misc.arrayR_combineC:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (T : Type) (ty : bluerock.lang.cpp.syntax.core.type) (R : T
                                                                                                           → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (i : Corelib.Init.Datatypes.nat) (xs : Corelib.Init.Datatypes.list T) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr),
    bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
      [p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs);
       p .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn i xs)]
      [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny [p |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs]
bluerock.cpp.array.arrayR_anyR_combine_char:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ct : bluerock.lang.cpp.syntax.preliminary.char_type) (t := bluerock.lang.cpp.syntax.core.Tchar_ ct) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (n : Corelib.Numbers.BinNums.N) (zs : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.N),
    let i := bluerock.prelude.list_numbers.lengthN zs in
    (i ≤ n)%N
    → p
      |-> bluerock.lang.cpp.logic.arr.arrayR t
            (λ c : Corelib.Numbers.BinNums.N,
               bluerock.lang.cpp.logic.heap_pred.primR t 1$m (bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vchar c))
            zs
      ⊢ p .[ t ! i ] |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t (n - i)) 1$m -∗
        p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t n) 1$m
bluerock.cpp.array.arrayR_anyR_unfocus1_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (x : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.type) (sz
                                                                                                            r : Corelib.Numbers.BinNums.N),
    (0 < r)%N
    → bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some sz
      → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
          [x |-> bluerock.lang.cpp.logic.heap_pred.anyR ty 1$m] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
          [x
           |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR ty 1$m)
                 (Corelib.Lists.ListDef.repeat () (Stdlib.NArith.BinNat.N.to_nat r))]
bluerock.cpp.array.arrayR_append':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (l : Corelib.Init.Datatypes.list T) (v : T) (ty : bluerock.lang.cpp.syntax.core.type) (sz : Corelib.Numbers.BinNums.N),
    bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some sz
    → (∀ v' : T, bluerock.iris.extra.bi.observe.Observe (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty) (R v'))
      → p |-> bluerock.lang.cpp.logic.arr.arrayR ty R l ∗ p .[ ty ! stdpp.base.length l ] |-> R v
        ⊢ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (l ++ [v])
bluerock.cpp.array.arrayR_append:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (l : Corelib.Init.Datatypes.list T) (v : T) (ty : bluerock.lang.cpp.syntax.core.type) (sz : Corelib.Numbers.BinNums.N),
    bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some sz
    → (∀ v' : T, bluerock.iris.extra.bi.observe.Observe (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty) (R v'))
      → p |-> bluerock.lang.cpp.logic.arr.arrayR ty R l
        ⊢ p .[ ty ! stdpp.base.length l ] |-> R v -∗ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (l ++ [v])
bluerock.cpp.array.wp_initlist_nil:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (Vctr : A → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (projV : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
                                                                                              → Corelib.Init.Datatypes.option A) 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (ρ : bluerock.lang.cpp.logic.wp.region) (l : A) 
    (ls_aux : Corelib.Init.Datatypes.list A) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ety : bluerock.lang.cpp.syntax.core.type) 
    (Q : bluerock.lang.cpp.logic.wp.FreeTemps → bluerock.lang.cpp.logic.wp.epred),
    ((let (cv, _) := bluerock.lang.cpp.syntax.types.decompose_type ety in
      let qf := bluerock.lang.cpp.algebra.cfrac.cQp.mk (bluerock.lang.cpp.syntax.preliminary.q_const cv) 1 in
      base
      |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.types.erase_qualifiers ety)
            (λ v : A, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.types.erase_qualifiers ety) qf (Vctr v))
            (Stdlib.Lists.List.rev (l :: ls_aux))) -∗
     Q 1%free)
    ⊢ bluerock.cpp.array.wp_initlist Vctr projV tu ρ [] (l :: ls_aux) base ety Q
bluerock.cpp.array.arrayR_split_eqv':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (i : Corelib.Init.Datatypes.nat) (ms : Corelib.Init.Datatypes.list T) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (ty : bluerock.lang.cpp.syntax.core.type) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (o : Corelib.Numbers.BinNums.N),
    i ≤ stdpp.base.length ms
    → bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some o
      → base |-> bluerock.lang.cpp.logic.arr.arrayR ty P ms
        ⊣⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.firstn i ms) ∗
        base .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.skipn i ms)
bluerock.cpp.array.arrayR_split_eqv:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (i : Corelib.Init.Datatypes.nat) (ms : Corelib.Init.Datatypes.list T) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (ty : bluerock.lang.cpp.syntax.core.type) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (o : Corelib.Numbers.BinNums.N),
    i < stdpp.base.length ms
    → bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some o
      → base |-> bluerock.lang.cpp.logic.arr.arrayR ty P ms
        ⊣⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.firstn i ms) ∗
        base .[ ty ! i ] |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.skipn i ms)
bluerock.cpp.array.arrayR_anyR_combine_int_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (b : bluerock.lang.cpp.syntax.preliminary.int_rank) (s : bluerock.prelude.arith.types.signed) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (n : Corelib.Numbers.BinNums.N) (zs : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.Z),
    bluerock.prelude.list_numbers.lengthZ zs ≤ n
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [p
         |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tnum b s)
               (λ z : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum b s) 1$m z) zs]
        [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
        [p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray (bluerock.lang.cpp.syntax.core.Tnum b s) n) 1$m]
bluerock.cpp.array.arrayR_append_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (T : Type) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (l : Corelib.Init.Datatypes.list T) (v : T) (ty : bluerock.lang.cpp.syntax.core.type) (sz : Corelib.Numbers.BinNums.N),
    bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some sz
    → (∀ v' : T, bluerock.iris.extra.bi.observe.Observe (bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty) (R v'))
      → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
          [p |-> bluerock.lang.cpp.logic.arr.arrayR ty R l] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
          [p |-> bluerock.lang.cpp.logic.arr.arrayR ty R (l ++ [v])]
bluerock.cpp.array.arrayR_anyR_combine_int:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (b : bluerock.lang.cpp.syntax.preliminary.int_rank) (s : bluerock.prelude.arith.types.signed) (t :=
                                                                                                   bluerock.lang.cpp.syntax.core.Tnum b s) 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (n : Corelib.Numbers.BinNums.N) (zs : Corelib.Init.Datatypes.list
                                                                                                         Corelib.Numbers.BinNums.Z),
    let i := bluerock.prelude.list_numbers.lengthN zs in
    i ≤ n
    → p |-> bluerock.lang.cpp.logic.arr.arrayR t (λ z : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR t 1$m z) zs
      ⊢ p .[ t ! i ] |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t (n - i)) 1$m -∗
        p |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tarray t n) 1$m
bluerock.cpp.array.arrayR_first:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (ms : Corelib.Init.Datatypes.list T),
    (stdpp.base.length ms > 0)%nat
    → (∃ (m : T) (ms' : Corelib.Init.Datatypes.list T), base |-> P m ∗ bluerock.lang.cpp.logic.pred.L.type_ptr ty base ∗
         base .[ ty ! 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty P ms' ∗ [| ms = m :: ms' |])
      ⊣⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P ms
monad.proofs.misc.arrLearn:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) {T : Type} 
    (ltr : Corelib.Init.Datatypes.list T) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type),
    p |-> bluerock.lang.cpp.logic.arr.arrayR ty R ltr ⊢ bluerock.lang.cpp.logic.pred.L.valid_ptr (p .[ ty ! stdpp.base.length ltr ]) ∗
    [| stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of CU ty) |] ∗
    □ ([∗ list] k↦_ ∈ ltr, bluerock.lang.cpp.logic.pred.L.type_ptr ty (p .[ ty ! k ])) ∗ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R ltr
bluerock.cpp.array.observe_2_arrayR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (P : Corelib.Numbers.BinNums.Z → A → A → bluerock.lang.cpp.logic.rep_defs.RepI) (T : bluerock.lang.cpp.syntax.core.type) 
    (R1 R2 : A → bluerock.lang.cpp.logic.rep_defs.Rep) (xs ys : Corelib.Init.Datatypes.list A),
    (∀ (i : Corelib.Numbers.BinNums.Z) (x y : A),
       bluerock.iris.extra.bi.observe.Observe2 (P i x y) (.[ T ! i ] |-> R1 x) (.[ T ! i ] |-> R2 y))
    → bluerock.iris.extra.bi.observe.Observe2 ([∗ list] i↦xy ∈ stdpp.base.zip xs ys, P i xy.1 xy.2)
        (bluerock.lang.cpp.logic.arr.arrayR T R1 xs) (bluerock.lang.cpp.logic.arr.arrayR T R2 ys)
bluerock.auto.cpp.hints.wp.default_initialize_array_fusion:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (Q : bluerock.lang.cpp.logic.wp.FreeTemps
                                                                           → bluerock.iris.extra.base_logic.mpred.mpred) 
    (sz : Corelib.Numbers.BinNums.N) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.type),
    match ty with
    | bluerock.lang.cpp.syntax.core.Tptr _ | bluerock.lang.cpp.syntax.core.Tnum _ _ | bluerock.lang.cpp.syntax.core.Tchar_ _ |
      bluerock.lang.cpp.syntax.core.Tenum _ | "bool"%cpp_type | bluerock.lang.cpp.syntax.core.Tfloat_ _ | "nullptr_t"%cpp_type =>
        Corelib.Init.Datatypes.true
    | _ => Corelib.Init.Datatypes.false
    end = Corelib.Init.Datatypes.true
    → bluerock.lang.cpp.semantics.types.HasSize ty
      → bluerock.lang.cpp.syntax.types.erase_qualifiers ty = ty
        → (p
           |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR ty 1$m)
                 (bluerock.prelude.list_numbers.replicateN sz ()) -∗
           p |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR (bluerock.lang.cpp.syntax.core.Tarray ty sz) -∗ Q 1%free)
          ⊢ bluerock.lang.cpp.logic.initializers.default_initialize_array (bluerock.lang.cpp.logic.initializers.default_initialize tu ty) tu
              ty sz p Q
bluerock.cpp.array.arrayR_unsplit:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (i : Corelib.Numbers.BinNums.N) (T : Type) (l : 
                                                                                                               Corelib.Init.Datatypes.list T) 
    (v : T) (ty : bluerock.lang.cpp.syntax.core.type) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep),
    Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat i) = Corelib.Init.Datatypes.Some v
    → loc |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn (Stdlib.NArith.BinNat.N.to_nat i) l)
      ⊢ loc .[ ty ! i ] |-> R v ∗
        loc .[ ty ! i + 1 ]
        |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn (Stdlib.NArith.BinNat.N.to_nat (i + 1)) l) -∗
        loc |-> bluerock.lang.cpp.logic.arr.arrayR ty R l
bluerock.cpp.array._arrayR_put1':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (l : 
                                                                                                               Corelib.Init.Datatypes.list
                                                                                                               Corelib.Numbers.BinNums.Z) 
    (x : Corelib.Numbers.BinNums.Z),
    Stdlib.Lists.List.nth_error l 0 = Corelib.Init.Datatypes.Some x
    → loc |-> bluerock.lang.cpp.primitives.ucharR q x
      ⊢ bluerock.lang.cpp.logic.pred.L.type_ptr "unsigned char" loc ∗
        loc .[ "unsigned char" ! 1 ]
        |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.primitives.ucharR q c)
              (Corelib.Lists.ListDef.skipn 1 l) -∗
        loc
        |-> bluerock.lang.cpp.logic.arr.arrayR "unsigned char" (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.primitives.ucharR q c) l
monad.proofs.misc.arrLearn2:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) {T : Type} 
    (ltr : Corelib.Init.Datatypes.list T) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type),
    p |-> bluerock.lang.cpp.logic.arr.arrayR ty R ltr ⊢ bluerock.lang.cpp.logic.pred.L.valid_ptr p ∗
    bluerock.lang.cpp.logic.pred.L.valid_ptr (p .[ ty ! stdpp.base.length ltr ]) ∗
    [| stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of CU ty) |] ∗
    □ ([∗ list] k↦_ ∈ ltr, bluerock.lang.cpp.logic.pred.L.type_ptr ty (p .[ ty ! k ])) ∗ p |-> bluerock.lang.cpp.logic.arr.arrayR ty R ltr
bluerock.auto.cpp.hints.wp.wp_init_initlist_prim_array_implicit:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (ρ : bluerock.lang.cpp.logic.wp.region) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (arr_ty : bluerock.lang.cpp.syntax.core.type) (Q : bluerock.lang.cpp.logic.wp.FreeTemps → bluerock.iris.extra.base_logic.mpred.mpredI) 
    (ty_prim : bluerock.lang.cpp.syntax.core.type) (len : Corelib.Numbers.BinNums.N) (init_val : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val),
    bluerock.lang.cpp.logic.expr.E.zero_init_val tu ty_prim = Corelib.Init.Datatypes.Some init_val
    → bluerock.lang.cpp.semantics.types.HasSize ty_prim
      → bluerock.lang.cpp.logic.expr.E.is_array_of arr_ty ty_prim
        → bluerock.lang.cpp.syntax.types.erase_qualifiers ty_prim = ty_prim
          → (base |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR (bluerock.lang.cpp.syntax.core.Tarray ty_prim len) -∗
             base
             |-> bluerock.lang.cpp.logic.arr.arrayR ty_prim (bluerock.lang.cpp.logic.heap_pred.primR ty_prim 1$m)
                   (bluerock.prelude.list_numbers.replicateN len init_val) -∗
             Q 1%free)
            ⊢ ::wpPRᵢ
                ρ
                (Pointer ↦ base) 
                (bluerock.lang.cpp.syntax.core.Einitlist []
                   (Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.core.Eimplicit_init ty_prim)) arr_ty)
                Q
bluerock.cpp.array.arrayR_anyR_unfocus1:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (x : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.type) (sz
                                                                                                            r : Corelib.Numbers.BinNums.N),
    (0 < r)%N
    → bluerock.lang.cpp.semantics.types.size_of σ ty = Corelib.Init.Datatypes.Some sz
      → x |-> bluerock.lang.cpp.logic.heap_pred.anyR ty 1$m
        ⊢ bluerock.lang.cpp.logic.pred.L.type_ptr ty x ∗
          x .[ ty ! 1 ]
          |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR ty 1$m)
                (Corelib.Lists.ListDef.repeat () (Stdlib.NArith.BinNat.N.to_nat (r - 1))) -∗
          x
          |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.anyR ty 1$m)
                (Corelib.Lists.ListDef.repeat () (Stdlib.NArith.BinNat.N.to_nat r))
bluerock.auto.cpp.hints.layout.implicit_destruct_tblockR_arrayR_primR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.type) (T : Type) 
    (f : T → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (ls : Corelib.Init.Datatypes.list T) (len : Corelib.Numbers.BinNums.N) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    Stdlib.NArith.BinNat.N.of_nat (stdpp.base.length ls) = len
    → q = 1%Qp
      → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
          [p |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ v : T, bluerock.lang.cpp.logic.heap_pred.primR ty q (f v)) ls] [tele]
          bluerock.auto.core.hints.classes.cancelx.CoverAny
          [(|={↑bluerock.lang.cpp.logic.pred.pred_ns}=>
              p |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.syntax.core.Tarray ty len) q)%I]
bluerock.lang.cpp.logic.arr.arrayR_cell:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {X : Type} (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (xs : Corelib.Init.Datatypes.list X) 
    (i : Corelib.Init.Datatypes.nat) (x : X) (iZ : Corelib.Numbers.BinNums.Z),
    iZ = i
    → xs !! i = Corelib.Init.Datatypes.Some x
      → bluerock.lang.cpp.logic.arr.arrayR ty R xs ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs) ∗
        .[ ty ! iZ ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ .[ ty ! iZ ] |-> R x ∗
        .[ ty ! iZ + 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn (Corelib.Init.Datatypes.S i) xs)
bluerock.cpp.array.arrayR_select:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {R : T → bluerock.lang.cpp.logic.rep_defs.Rep} {ty : bluerock.lang.cpp.syntax.core.type} (xs__i : 
                                                                                                         Corelib.Init.Datatypes.list T) 
    (x__i : T) (xs__n : Corelib.Init.Datatypes.list T) (i : Corelib.Numbers.BinNums.N),
    bluerock.lang.cpp.semantics.types.HasSize ty
    → bluerock.prelude.list_numbers.lengthN xs__i = i
      → bluerock.lang.cpp.logic.arr.arrayR ty R (xs__i ++ [x__i] ++ xs__n)
        ⊣⊢ .[ ty ! 0 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs__i ∗
        .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ .[ ty ! i ] |-> R x__i ∗
        .[ ty ! (i + 1)%N ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R xs__n
bluerock.lang.cpp.logic.raw.decode_uint_primR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (sz : bluerock.lang.cpp.syntax.preliminary.int_rank) (x : Corelib.Numbers.BinNums.Z),
    bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz bluerock.prelude.arith.types.Unsigned) q x
    ⊣⊢ ∃ (rs : Corelib.Init.Datatypes.list bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_byte) (l : Corelib.Init.Datatypes.list
                                                                                                               Corelib.Numbers.BinNums.N),
         [| bluerock.lang.cpp.logic.raw.decodes_uint l x |] ∗
         [| bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_int_byte <$> l = rs |] ∗
         [| stdpp.base.length l = Stdlib.NArith.BinNat.N.to_nat (bluerock.lang.cpp.syntax.preliminary.int_rank.bytesN sz) |] ∗
         bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR (bluerock.lang.cpp.syntax.core.Tnum sz bluerock.prelude.arith.types.Unsigned) ∗
         bluerock.lang.cpp.logic.arr.arrayR "unsigned char" (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.primitives.ucharR q c)
           (Stdlib.ZArith.BinInt.Z.of_N <$> l)
bluerock.cpp.array._at_arrayR_cell:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (P : T → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (ms : Corelib.Init.Datatypes.list T) (i : Corelib.Init.Datatypes.nat) (m : T),
    Stdlib.Lists.List.nth_error ms i = Corelib.Init.Datatypes.Some m
    → base |-> bluerock.lang.cpp.logic.arr.arrayR ty P ms
      ⊣⊢ base |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.firstn i ms) ∗
      □ bluerock.lang.cpp.logic.pred.L.type_ptr ty (base .[ ty ! i ]) ∗ base .[ ty ! i ] |-> P m ∗
      base .[ ty ! Corelib.Init.Datatypes.S i ]
      |-> bluerock.lang.cpp.logic.arr.arrayR ty P (Corelib.Lists.ListDef.skipn (Corelib.Init.Datatypes.S i) ms)
bluerock.auto.cpp.hints.wp.wp_array_init_prim_implicit:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (ρ : bluerock.lang.cpp.logic.wp.region) (full_len
                                                                                                               len : Corelib.Numbers.BinNums.N) 
    (ty_prim : bluerock.lang.cpp.syntax.core.type) (cur : Corelib.Numbers.BinNums.N) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (Q : bluerock.lang.cpp.logic.wp.FreeTemps → bluerock.iris.extra.base_logic.mpred.mpredI) (v : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val),
    bluerock.lang.cpp.syntax.types.erase_qualifiers ty_prim = ty_prim
    → bluerock.lang.cpp.semantics.types.HasSize ty_prim
      → bluerock.lang.cpp.logic.expr.E.zero_init_val tu ty_prim = Corelib.Init.Datatypes.Some v
        → full_len = (len + cur)%N
          → ((base |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR (bluerock.lang.cpp.syntax.core.Tarray ty_prim full_len) -∗
              base .[ ty_prim ! cur ]
              |-> bluerock.lang.cpp.logic.arr.arrayR ty_prim (bluerock.lang.cpp.logic.heap_pred.tptsto_fuzzyR ty_prim 1$m)
                    (bluerock.prelude.list_numbers.replicateN len v)) -∗
             Q 1%free)
            ⊢ bluerock.lang.cpp.logic.expr.E.wp_array_init tu ρ ty_prim base
                (bluerock.prelude.list_numbers.replicateN len (bluerock.lang.cpp.syntax.core.Eimplicit_init ty_prim)) cur
                (λ free : bluerock.lang.cpp.logic.wp.FreeTemps, Q free)
monad.proofs.misc.arrDecompose:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} {T : Type} (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (ltr : Corelib.Init.Datatypes.list T) (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (ty : bluerock.lang.cpp.syntax.core.type),
    p |-> bluerock.lang.cpp.logic.arr.arrayR ty R ltr
    ⊣⊢ (bluerock.lang.cpp.logic.pred.L.valid_ptr (p .[ ty ! stdpp.base.length ltr ]) ∗
        [| stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of CU ty) |] ∗
        □ ([∗ list] k↦_ ∈ ltr, bluerock.lang.cpp.logic.pred.L.type_ptr ty (p .[ ty ! k ]))) ∗
    ([∗ list] k↦t ∈ ltr, p .[ ty ! k ] |-> R t)
bluerock.cpp.array.arrayR_inrange_valid:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (T : Type) (x : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (i : Corelib.Numbers.BinNums.N) (ty : bluerock.lang.cpp.syntax.core.type) 
    (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (l : Corelib.Init.Datatypes.list T) (v : T),
    Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat i) = Corelib.Init.Datatypes.Some v
    → x |-> bluerock.lang.cpp.logic.arr.arrayR ty R l
      ⊢ (x |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn (Stdlib.NArith.BinNat.N.to_nat i) l) ∗
         x .[ ty ! i ] |-> R v ∗
         x .[ ty ! i + 1 ]
         |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn (Stdlib.NArith.BinNat.N.to_nat (i + 1)) l)) ∗
      bluerock.lang.cpp.logic.pred.L.valid_ptr (x .[ ty ! i ])
monad.proofs.misc.arrayR_cell2:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Sigma : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                                  thread_info _Σ} 
    {CU : bluerock.lang.cpp.semantics.genv.genv} (i : Corelib.Init.Datatypes.nat) {X : Type} (ty : bluerock.lang.cpp.syntax.core.type) 
    (R : X → bluerock.lang.cpp.logic.rep_defs.Rep) (xs : Corelib.Init.Datatypes.list X),
    i < stdpp.base.length xs
    → ∃ x : X,
        xs !! i = Corelib.Init.Datatypes.Some x
        ∧ (bluerock.lang.cpp.logic.arr.arrayR ty R xs ⊣⊢ bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn i xs) ∗
           .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ .[ ty ! i ] |-> R x ∗
           .[ ty ! i + 1 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn (1 + i) xs))
bluerock.cpp.array.arrayR_explode:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} {R : T → bluerock.lang.cpp.logic.rep_defs.Rep} {ty : bluerock.lang.cpp.syntax.core.type} (xs : Corelib.Init.Datatypes.list T) 
    (i : Corelib.Numbers.BinNums.N) (x : T),
    bluerock.lang.cpp.semantics.types.HasSize ty
    → (i < bluerock.prelude.list_numbers.lengthN xs)%N
      → bluerock.lang.cpp.logic.arr.arrayR ty R
          (bluerock.prelude.list_numbers.takeN i xs ++ [x] ++ bluerock.prelude.list_numbers.dropN (i + 1) xs)
        ⊣⊢ .[ ty ! 0 ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (bluerock.prelude.list_numbers.takeN i xs) ∗
        .[ ty ! i ] |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR ty ∗ .[ ty ! i ] |-> R x ∗
        .[ ty ! (i + 1)%N ] |-> bluerock.lang.cpp.logic.arr.arrayR ty R (bluerock.prelude.list_numbers.dropN (i + 1) xs)
bluerock.cpp.array._at_arrayR_cellN:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {T : Type} (i : Corelib.Numbers.BinNums.N) (l : Corelib.Init.Datatypes.list T) (ty : bluerock.lang.cpp.syntax.core.type) 
    (R : T → bluerock.lang.cpp.logic.rep_defs.Rep) (loc : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (v : T),
    Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat i) = Corelib.Init.Datatypes.Some v
    → loc |-> bluerock.lang.cpp.logic.arr.arrayR ty R l
      ⊣⊢ loc |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.firstn (Stdlib.NArith.BinNat.N.to_nat i) l) ∗
      □ bluerock.lang.cpp.logic.pred.L.type_ptr ty (loc .[ ty ! i ]) ∗ loc .[ ty ! i ] |-> R v ∗
      loc .[ ty ! i + 1 ]
      |-> bluerock.lang.cpp.logic.arr.arrayR ty R (Corelib.Lists.ListDef.skipn (Stdlib.NArith.BinNat.N.to_nat (i + 1)) l)
bluerock.cpp.array.array_combine_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (sz : bluerock.lang.cpp.syntax.preliminary.int_rank) (sgn : bluerock.prelude.arith.types.signed) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (l : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.Z) (z v : Corelib.Numbers.BinNums.Z) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    0 ≤ z
    → Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat (Stdlib.ZArith.BinInt.Z.to_N z)) = Corelib.Init.Datatypes.Some v
      → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
          [p .[ bluerock.lang.cpp.syntax.core.Tnum sz sgn ! Stdlib.ZArith.BinInt.Z.to_N z + 1 ]
           |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tnum sz sgn)
                 (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz sgn) q c)
                 (Corelib.Lists.ListDef.skipn (Stdlib.NArith.BinNat.N.to_nat (Stdlib.ZArith.BinInt.Z.to_N z + 1)) l)]
          [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
          [p
           |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tnum sz sgn)
                 (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz sgn) q c)
                 l]
bluerock.auto.cpp.hints.wp.default_initialize_array_fusion':
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (ty : bluerock.lang.cpp.syntax.core.type) 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (idx sz : Corelib.Numbers.BinNums.N) (Q : bluerock.lang.cpp.logic.wp.FreeTemps
                                                                                                           → bluerock.iris.extra.base_logic.mpred.mpred),
    bluerock.lang.cpp.semantics.types.HasSize ty
    → match ty with
      | bluerock.lang.cpp.syntax.core.Tptr _ | bluerock.lang.cpp.syntax.core.Tnum _ _ | bluerock.lang.cpp.syntax.core.Tchar_ _ |
        bluerock.lang.cpp.syntax.core.Tenum _ | "bool"%cpp_type | bluerock.lang.cpp.syntax.core.Tfloat_ _ | "nullptr_t"%cpp_type =>
          Corelib.Init.Datatypes.true
      | _ => Corelib.Init.Datatypes.false
      end = Corelib.Init.Datatypes.true
      → bluerock.lang.cpp.syntax.types.erase_qualifiers ty = ty
        → (p .[ ty ! idx ]
           |-> bluerock.lang.cpp.logic.arr.arrayR ty (λ _ : (), bluerock.lang.cpp.logic.heap_pred.uninitR ty 1$m)
                 (bluerock.prelude.list_numbers.replicateN sz ()) -∗
           Q 1%free)
          ⊢ stdpp.list.foldr
              (λ (i : Corelib.Numbers.BinNums.N) (PP : bluerock.lang.cpp.logic.wp.epred),
                 bluerock.lang.cpp.logic.initializers.default_initialize tu ty (p .[ ty ! i ])
                   (λ free' : bluerock.lang.cpp.logic.wp.FreeTemps, ::interp { free' }  PP))
              (p .[ ty ! idx + sz ] |-> bluerock.lang.cpp.logic.heap_pred.valid.validR -∗ Q 1%free)
              (bluerock.prelude.list_numbers.seqN idx sz)
bluerock.cpp.array.array_combine:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (sz : bluerock.lang.cpp.syntax.preliminary.int_rank) (sgn : bluerock.prelude.arith.types.signed) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (l : Corelib.Init.Datatypes.list Corelib.Numbers.BinNums.Z) (z v : Corelib.Numbers.BinNums.Z) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    0 ≤ z
    → Stdlib.Lists.List.nth_error l (Stdlib.NArith.BinNat.N.to_nat (Stdlib.ZArith.BinInt.Z.to_N z)) = Corelib.Init.Datatypes.Some v
      → p .[ bluerock.lang.cpp.syntax.core.Tnum sz sgn ! Stdlib.ZArith.BinInt.Z.to_N z + 1 ]
        |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tnum sz sgn)
              (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz sgn) q c)
              (Corelib.Lists.ListDef.skipn (Stdlib.NArith.BinNat.N.to_nat (Stdlib.ZArith.BinInt.Z.to_N z + 1)) l)
        ⊢ p .[ bluerock.lang.cpp.syntax.core.Tnum sz sgn ! Stdlib.ZArith.BinInt.Z.to_N z ]
          |-> bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz sgn) q v ∗
          p
          |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tnum sz sgn)
                (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz sgn) q c)
                (Corelib.Lists.ListDef.firstn (Stdlib.NArith.BinNat.N.to_nat (Stdlib.ZArith.BinInt.Z.to_N z)) l) -∗
          p
          |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.core.Tnum sz sgn)
                (λ c : Corelib.Numbers.BinNums.Z, bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.core.Tnum sz sgn) q c) l
bluerock.cpp.array.wp_array_init_initlist_aux:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {A : Type} (Vctr : A → bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (projV : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val
                                                                                              → Corelib.Init.Datatypes.option A) 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (ρ : bluerock.lang.cpp.logic.wp.region) (ls : 
                                                                                                               Corelib.Init.Datatypes.list
                                                                                                               bluerock.lang.cpp.syntax.core.Expr) 
    (ety : bluerock.lang.cpp.syntax.core.type) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (Q : 
                                                                                                               bluerock.lang.cpp.logic.wp.FreeTemps
                                                                                                               → bluerock.iris.extra.base_logic.mpred.mpredI) 
    (ls_aux : Corelib.Init.Datatypes.list A) (sz : Corelib.Numbers.BinNums.N),
    bluerock.prelude.list_numbers.lengthN ls_aux = sz
    → stdpp.option.is_Some (bluerock.lang.cpp.semantics.types.size_of σ ety)
      → bluerock.lang.cpp.syntax.types.is_scalar_type ety
        → ~~ bluerock.lang.cpp.syntax.preliminary.q_volatile (bluerock.lang.cpp.syntax.types.decompose_type ety).1
          → (∀ (a : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val) (b : A), projV a = Corelib.Init.Datatypes.Some b → a = Vctr b)
            → (∀ a : A, ~~ bluerock.lang.cpp.logic.heap_pred.is_raw_or_undef (Vctr a))
              → let sz' := (sz + bluerock.prelude.list_numbers.lengthN ls)%N in
                let Q' :=
                  λ free : bluerock.lang.cpp.logic.wp.FreeTemps,
                    (base
                     |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR
                           (bluerock.lang.cpp.syntax.core.Tarray (bluerock.lang.cpp.syntax.types.erase_qualifiers ety) sz') -∗
                     Q free)%I
                  in
                match ls_aux with
                | [] => emp
                | _ :: _ =>
                    let (cv, _) := bluerock.lang.cpp.syntax.types.decompose_type ety in
                    let qf := bluerock.lang.cpp.algebra.cfrac.cQp.mk (bluerock.lang.cpp.syntax.preliminary.q_const cv) 1 in
                    base
                    |-> bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR
                          (bluerock.lang.cpp.syntax.core.Tarray (bluerock.lang.cpp.syntax.types.erase_qualifiers ety) sz') -∗
                    base
                    |-> bluerock.lang.cpp.logic.arr.arrayR (bluerock.lang.cpp.syntax.types.erase_qualifiers ety)
                          (λ v : A,
                             bluerock.lang.cpp.logic.heap_pred.primR (bluerock.lang.cpp.syntax.types.erase_qualifiers ety) qf (Vctr v))
                          (Stdlib.Lists.List.rev ls_aux)
                end ∗ bluerock.cpp.array.wp_initlist Vctr projV tu ρ ls ls_aux base ety Q'
                ⊢ bluerock.lang.cpp.logic.expr.E.wp_array_init tu ρ ety base ls sz Q'

>>> Search structR.
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_frac_valid:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname),
    bluerock.lang.cpp.bi.cfractional.CFracValid0 (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_fractional:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname),
    bluerock.lang.cpp.bi.cfractional.CFractional (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls)
bluerock.auto.lazy_unfold.AutoUnlocking.Metadata_structR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (a : bluerock.lang.cpp.syntax.core.globname) (b : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.auto.lazy_unfold.AutoUnlocking.Metadata (bluerock.lang.cpp.logic.heap_pred.aggregate.structR a b)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_cfractional_eta:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname),
    bluerock.lang.cpp.bi.cfractional.CFractional
      (λ q : bluerock.lang.cpp.algebra.cfrac.cQp.t, bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_frac_valid_eta:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname),
    bluerock.lang.cpp.bi.cfractional.CFracValid0
      (λ q : bluerock.lang.cpp.algebra.cfrac.cQp.t, bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_timeless:
  bluerock.iris.extra.bi.derived_laws.nary.Timeless6 (@bluerock.lang.cpp.logic.heap_pred.aggregate.structR)
bluerock.auto.cpp.hints.layout.padding_valid_observe:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (cls : bluerock.lang.cpp.syntax.core.globname),
    bluerock.iris.extra.bi.observe.Observe bluerock.lang.cpp.logic.heap_pred.valid.validR
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_nonnull:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.iris.extra.bi.observe.Observe bluerock.lang.cpp.logic.heap_pred.null.nonnullR
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_valid_observe:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.iris.extra.bi.observe.Observe bluerock.lang.cpp.logic.heap_pred.valid.validR
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_as_fractional:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.bi.cfractional.AsCFractional (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls) q
bluerock.auto.cpp.hints.layout.padding_svalid_observe:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (cls : bluerock.lang.cpp.syntax.core.globname),
    bluerock.iris.extra.bi.observe.Observe bluerock.lang.cpp.logic.heap_pred.valid.svalidR
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_strict_valid_observe:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.iris.extra.bi.observe.Observe bluerock.lang.cpp.logic.heap_pred.valid.svalidR
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.lang.cpp.logic.heap_pred.aggregate.structR_type_ptr_observe:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (cls : bluerock.lang.cpp.syntax.core.name),
    bluerock.lang.cpp.bi.spec.typed.Typed cls (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.auto.cpp.hints.anyR.anyR_structR_defined_using:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.name) (q q' : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.auto.lazy_unfold.AutoUnlocking.DefinedUsing
      (bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q)
      (bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q')
bluerock.auto.cpp.pretty.my_pretty_internals.Internals.ParseObjectRep_structR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} (σ : bluerock.lang.cpp.semantics.genv.genv) 
    (c : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (fields : Corelib.Init.Datatypes.list
                                                                                                         bluerock.auto.cpp.pretty.my_pretty_internals.Internals.object_component),
    bluerock.auto.cpp.pretty.my_pretty_internals.Internals.ParseObjectRep (bluerock.lang.cpp.logic.heap_pred.aggregate.structR c q) fields
      (bluerock.auto.cpp.pretty.my_pretty_internals.Internals.OBJ_struct σ c q :: fields)
bluerock.auto.borrowR.borrowR.unlock:
  @bluerock.auto.borrowR.borrowR.body =
  λ (thread_info : iris.bi.monpred.biIndex) (_Σ : iris.base_logic.lib.iprop.gFunctors) (Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ) (σ : bluerock.lang.cpp.semantics.genv.genv) 
    (Field : Type) (EqDecision0 : stdpp.base.EqDecision Field) (H : stdpp.countable.Countable Field) (ToField0 : 
                                                                                                      bluerock.auto.borrowR.ToField Field) 
    (C : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (m : stdpp.gmap.gmap Field
                                                                                                    bluerock.lang.cpp.logic.rep_defs.Rep),
    (bluerock.auto.borrowR._borrowR m ∗ bluerock.lang.cpp.logic.heap_pred.aggregate.structR C q)%I
bluerock.auto.cpp.hints.layout.auto_close_paddingR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (st : bluerock.lang.cpp.syntax.decl.Struct),
    m ⊧ resolve
    → bluerock.auto.cpp.definitions.find_struct cls m = Corelib.Init.Datatypes.Some st
      → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
          [base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
          [base |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q]
bluerock.auto.cpp.hints.layout.auto_open_paddingR_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    m ⊧ resolve
    → bluerock.auto.cpp.definitions.find_struct cls m = Corelib.Init.Datatypes.Some st
      → q = 1%Qp
        → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
            [base |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q] [tele]
            bluerock.auto.core.hints.classes.cancelx.CoverAny [base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q]
bluerock.auto.cpp.hints.const.wp_const_named_struct_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit} (from to : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (nm : bluerock.lang.cpp.syntax.core.globname) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (Q : bluerock.iris.extra.base_logic.mpred.mpredI),
    bluerock.lang.cpp.syntax.translation_unit.types tu !! nm =[Vm?]=>
    Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
        [p |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR nm from] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
        [bluerock.lang.cpp.logic.const.wp_const tu from to p (bluerock.lang.cpp.syntax.core.Tnamed nm) Q]
bluerock.auto.cpp.hints.layout.implicit_destruct_tblockR_padding_C:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (cls : bluerock.lang.cpp.syntax.core.name) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.semantics.genv.glob_def resolve cls =
    Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → bluerock.lang.cpp.syntax.decl.s_trivially_destructible st
      → q = 1%Qp
        → bluerock.auto.core.hints.classes.cancelx.CancelX bluerock.auto.core.hints.classes.cancelx.MatchNormal
            [p |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q] [tele] bluerock.auto.core.hints.classes.cancelx.CoverAny
            [(|={↑bluerock.lang.cpp.logic.pred.pred_ns}=>
                p |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.syntax.core.Tnamed cls) q)%I]
bluerock.lang.cpp.logic.heap_pred.any.anyR_struct:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.name) (st : bluerock.lang.cpp.syntax.decl.Struct) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.semantics.genv.glob_def σ cls = Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
      ⊣⊢ ([∗ list] base ∈ bluerock.lang.cpp.syntax.decl.s_bases st, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base σ cls base.1
                                                                    |-> bluerock.lang.cpp.logic.heap_pred.anyR
                                                                          (bluerock.lang.cpp.syntax.core.Tnamed base.1) q) ∗
      ([∗ list] fld ∈ bluerock.lang.cpp.syntax.decl.s_fields st, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field σ
                                                                   (bluerock.lang.cpp.syntax.core.Field cls
                                                                      (bluerock.lang.cpp.syntax.decl.mem_name fld))
                                                                 |-> bluerock.lang.cpp.logic.heap_pred.anyR
                                                                       (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type fld q).2
                                                                       (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type fld q).1) ∗
      (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
      bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
bluerock.auto.cpp.hints.layout.close_class_anyR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    m ⊧ resolve
    → bluerock.auto.cpp.definitions.find_struct cls m = Corelib.Init.Datatypes.Some st
      → [∗] (Corelib.Lists.ListDef.map
               (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
                  base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
                  |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
               (bluerock.lang.cpp.syntax.decl.s_bases st) ++
             Corelib.Lists.ListDef.map
               (λ m0 : bluerock.lang.cpp.syntax.decl.Member,
                  base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                            (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m0))
                  |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).2
                        (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).1)
               (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
        base
        |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
        base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
        ⊢ base |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
bluerock.auto.cpp.hints.layout.any_class_fwd:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    m ⊧ resolve
    → bluerock.auto.cpp.definitions.find_struct cls m = Corelib.Init.Datatypes.Some st
      → base |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
        ⊢ [∗] (Corelib.Lists.ListDef.map
                 (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
                    base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
                    |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
                 (bluerock.lang.cpp.syntax.decl.s_bases st) ++
               Corelib.Lists.ListDef.map
                 (λ m0 : bluerock.lang.cpp.syntax.decl.Member,
                    base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                              (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m0))
                    |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).2
                          (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).1)
                 (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
        base
        |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
        base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
bluerock.auto.cpp.hints.layout.auto_close_paddingR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (st : bluerock.lang.cpp.syntax.decl.Struct),
    m ⊧ resolve
    → bluerock.auto.cpp.definitions.find_struct cls m = Corelib.Init.Datatypes.Some st
      → base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
        ⊢ [∗] (Corelib.Lists.ListDef.map
                 (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
                    base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
                    |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
                 (bluerock.lang.cpp.syntax.decl.s_bases st) ++
               Corelib.Lists.ListDef.map
                 (λ m0 : bluerock.lang.cpp.syntax.decl.Member,
                    base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                              (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m0))
                    |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).2
                          (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).1)
                 (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
          base
          |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) -∗
          base |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
bluerock.auto.cpp.hints.const.wp_const_named_struct:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    {tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit} (from to : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (nm : bluerock.lang.cpp.syntax.core.globname) (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (Q : bluerock.iris.extra.base_logic.mpred.mpredI),
    bluerock.lang.cpp.syntax.translation_unit.types tu !! nm =[Vm?]=>
    Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → p |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR nm from
      ⊢ Stdlib.Lists.List.fold_left
          (λ (Q0 : bluerock.iris.extra.base_logic.mpred.mpred) '(b, _),
             bluerock.lang.cpp.logic.const.wp_const tu from to (p ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base σ nm b)
               (bluerock.lang.cpp.syntax.core.Tnamed b) Q0)
          (bluerock.lang.cpp.syntax.decl.s_bases st)
          (Stdlib.Lists.List.fold_left
             (λ (Q0 : bluerock.iris.extra.base_logic.mpred.mpred) (m : bluerock.lang.cpp.syntax.decl.Member),
                if
                 bluerock.lang.cpp.syntax.decl.mem_mutable m
                 || bluerock.auto.cpp.hints.const.type_is_const (bluerock.lang.cpp.syntax.decl.mem_type m)
                then Q0
                else
                 bluerock.lang.cpp.logic.const.wp_const tu from to
                   (p ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field σ
                           (bluerock.lang.cpp.syntax.core.Field nm (bluerock.lang.cpp.syntax.decl.mem_name m)))
                   (bluerock.lang.cpp.syntax.decl.mem_type m) Q0)
             (bluerock.lang.cpp.syntax.decl.s_fields st)
             (p |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR nm to -∗
              if bluerock.lang.cpp.syntax.decl.has_vtable st
              then
               ∃ path : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.globname,
                 p |-> bluerock.lang.cpp.logic.heap_pred.simple.derivationR nm path from ∗
                 (p |-> bluerock.lang.cpp.logic.heap_pred.simple.derivationR nm path to -∗ Q)
              else Q)) -∗
        bluerock.lang.cpp.logic.const.wp_const tu from to p (bluerock.lang.cpp.syntax.core.Tnamed nm) Q
bluerock.auto.cpp.hints.layout.auto_open_paddingR:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.globname) (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (m : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    m ⊧ resolve
    → bluerock.auto.cpp.definitions.find_struct cls m = Corelib.Init.Datatypes.Some st
      → q = 1%Qp
        → base |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
          ⊢ ([∗] (Corelib.Lists.ListDef.map
                    (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
                       base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
                       |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
                    (bluerock.lang.cpp.syntax.decl.s_bases st) ++
                  Corelib.Lists.ListDef.map
                    (λ m0 : bluerock.lang.cpp.syntax.decl.Member,
                       base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                                 (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m0))
                       |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).2
                             (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m0 q).1)
                    (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
             base
             |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp)) ∗
          base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
bluerock.lang.cpp.logic.layout.implicit_destruct_struct:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.name) (st : bluerock.lang.cpp.syntax.decl.Struct) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.semantics.genv.glob_def σ cls = Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → bluerock.lang.cpp.syntax.decl.s_trivially_destructible st
      → q = 1%Qp
        → bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR (bluerock.lang.cpp.syntax.core.Tnamed cls)
          ⊢ ([∗ list] base ∈ bluerock.lang.cpp.syntax.decl.s_bases st, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base σ cls
                                                                         base.1
                                                                       |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                                                             (bluerock.lang.cpp.syntax.core.Tnamed base.1) q) ∗
            ([∗ list] fld ∈ bluerock.lang.cpp.syntax.decl.s_fields st, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field σ
                                                                         (bluerock.lang.cpp.syntax.core.Field cls
                                                                            (bluerock.lang.cpp.syntax.decl.mem_name fld))
                                                                       |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                                                             (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type fld q).2
                                                                             (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type fld q).1) ∗
            (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
            bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q ={↑bluerock.lang.cpp.logic.pred.pred_ns}=∗
            bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
bluerock.auto.cpp.hints.layout.implicit_destruct_tblockR_padding:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (cls : bluerock.lang.cpp.syntax.core.name) (st : bluerock.lang.cpp.syntax.decl.Struct) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.semantics.genv.glob_def resolve cls =
    Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → bluerock.lang.cpp.syntax.decl.s_trivially_destructible st
      → q = 1%Qp
        → p |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
          ⊢ [∗] (Corelib.Lists.ListDef.map
                   (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
                      p ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
                      |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
                   (bluerock.lang.cpp.syntax.decl.s_bases st) ++
                 Corelib.Lists.ListDef.map
                   (λ m : bluerock.lang.cpp.syntax.decl.Member,
                      p ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                             (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m))
                      |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).2
                            (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).1)
                   (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
            p
            |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ={↑bluerock.lang.cpp.logic.pred.pred_ns}=∗
            p |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR (bluerock.lang.cpp.syntax.core.Tnamed cls) q
bluerock.auto.cpp.hints.anyR.anyR_unfoldable:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    {tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit},
    tu ⊧ resolve
    → ∀ (cls : bluerock.lang.cpp.syntax.core.globname) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t) (su : bluerock.lang.cpp.syntax.decl.Struct +
                                                                                                         bluerock.lang.cpp.syntax.decl.Union),
        bluerock.auto.cpp.hints.anyR.find_aggregate tu cls =[Vm?]=> Corelib.Init.Datatypes.Some su
        → bluerock.auto.lazy_unfold.AutoUnlocking.Unfoldable
            (bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.syntax.core.Tnamed cls) q)
            match su with
            | Corelib.Init.Datatypes.inl s => bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q ∗
                (if bluerock.lang.cpp.syntax.decl.has_vtable s then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp%I) ∗
                ([∗ list] b ∈ bluerock.lang.cpp.syntax.decl.s_bases s, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls
                                                                         b.1
                                                                       |-> bluerock.lang.cpp.logic.heap_pred.anyR
                                                                             (bluerock.lang.cpp.syntax.core.Tnamed b.1) q) ∗
                ([∗ list] m ∈ bluerock.lang.cpp.syntax.decl.s_fields s, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                                                                          (bluerock.lang.cpp.syntax.core.Field cls
                                                                             (bluerock.lang.cpp.syntax.decl.mem_name m))
                                                                        |-> bluerock.lang.cpp.logic.heap_pred.anyR
                                                                              (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).2
                                                                              (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).1)
            | Corelib.Init.Datatypes.inr u =>
                ∃ what : Corelib.Init.Datatypes.option Corelib.Init.Datatypes.nat,
                  bluerock.lang.cpp.logic.heap_pred.aggregate.unionR cls q what ∗
                  match what with
                  | Corelib.Init.Datatypes.Some idx =>
                      ∃ m : bluerock.lang.cpp.syntax.decl.Member,
                        [| bluerock.lang.cpp.syntax.decl.u_fields u !! idx = Corelib.Init.Datatypes.Some m |] ∗
                        bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                          (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m))
                        |-> bluerock.lang.cpp.logic.heap_pred.anyR (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).2
                              (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).1
                  | Corelib.Init.Datatypes.None => emp
                  end
            end
bluerock.lang.cpp.logic.layout.struct_to_raw:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (cls : bluerock.lang.cpp.syntax.core.name) (st : bluerock.lang.cpp.syntax.decl.Struct) (rss : stdpp.gmap.gmap
                                                                                                    bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.FieldOrBase.t
                                                                                                    (Corelib.Init.Datatypes.list
                                                                                                       bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_byte)) 
    (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    bluerock.lang.cpp.semantics.genv.glob_def σ cls = Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st)
    → bluerock.lang.cpp.syntax.decl.s_layout st ∈ [bluerock.lang.cpp.syntax.decl.POD; bluerock.lang.cpp.syntax.decl.Standard]
      → bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q ∗
        ([∗ list] b ∈ bluerock.lang.cpp.syntax.decl.s_bases st, ∃ rs : Corelib.Init.Datatypes.list
                                                                         bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_byte,
                                                                  [| rss
                                                                     !! bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.FieldOrBase.Base
                                                                          b.1 =
                                                                     Corelib.Init.Datatypes.Some rs |] ∗
                                                                  bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base σ cls b.1
                                                                  |-> bluerock.lang.cpp.logic.raw.rawsR q rs) ∗
        ([∗ list] fld ∈ bluerock.lang.cpp.syntax.decl.s_fields st, ∃ rs : Corelib.Init.Datatypes.list
                                                                            bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_byte,
                                                                     [| rss
                                                                        !! bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.FieldOrBase.Field
                                                                             (bluerock.lang.cpp.syntax.decl.mem_name fld) =
                                                                        Corelib.Init.Datatypes.Some rs |] ∗
                                                                     bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field σ
                                                                       (bluerock.lang.cpp.syntax.core.Field cls
                                                                          (bluerock.lang.cpp.syntax.decl.mem_name fld))
                                                                     |-> bluerock.lang.cpp.logic.raw.rawsR q rs)
        ⊣⊢ bluerock.lang.cpp.logic.heap_pred.valid.type_ptrR (bluerock.lang.cpp.syntax.core.Tnamed cls) ∗
        ∃ rs : Corelib.Init.Datatypes.list bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_byte,
          bluerock.lang.cpp.logic.raw.rawsR q rs ∗
          [| bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.raw_bytes_of_struct σ cls rss rs |]
bluerock.auto.cpp.hints.layout.struct_def_layout:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (R : bluerock.lang.cpp.syntax.core.type
                                                                         → bluerock.lang.cpp.algebra.cfrac.cQp.t
                                                                           → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (cls : bluerock.lang.cpp.syntax.core.globname) (st : bluerock.lang.cpp.syntax.decl.Struct) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    [∗] (Corelib.Lists.ListDef.map
           (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
              base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
              |-> R (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
           (bluerock.lang.cpp.syntax.decl.s_bases st) ++
         Corelib.Lists.ListDef.map
           (λ m : bluerock.lang.cpp.syntax.decl.Member,
              base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                        (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m))
              |-> R (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).2
                    (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).1)
           (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
    base |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
    base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
    ⊣⊢ base
       |-> (([∗ list] base0 ∈ bluerock.lang.cpp.syntax.decl.s_bases st, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve
                                                                          cls base0.1
                                                                        |-> R (bluerock.lang.cpp.syntax.core.Tnamed base0.1) q) ∗
            ([∗ list] fld ∈ bluerock.lang.cpp.syntax.decl.s_fields st, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                                                                         (bluerock.lang.cpp.syntax.core.Field cls
                                                                            (bluerock.lang.cpp.syntax.decl.mem_name fld))
                                                                       |-> R (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type fld q).2
                                                                             (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type fld q).1) ∗
            (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
            bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q)
bluerock.auto.cpp.hints.layout.struct_def_padding:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {resolve : bluerock.lang.cpp.semantics.genv.genv} 
    (base : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (R : bluerock.lang.cpp.syntax.core.type
                                                                         → bluerock.lang.cpp.algebra.cfrac.cQp.t
                                                                           → bluerock.lang.cpp.logic.rep_defs.Rep) 
    (cls : bluerock.lang.cpp.syntax.core.globname) (st : bluerock.lang.cpp.syntax.decl.Struct) (q : bluerock.lang.cpp.algebra.cfrac.cQp.t),
    [∗] (Corelib.Lists.ListDef.map
           (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
              base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
              |-> R (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
           (bluerock.lang.cpp.syntax.decl.s_bases st) ++
         Corelib.Lists.ListDef.map
           (λ m : bluerock.lang.cpp.syntax.decl.Member,
              base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                        (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m))
              |-> R (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).2
                    (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).1)
           (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
    base |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp) ∗
    base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
    ⊣⊢ ([∗] (Corelib.Lists.ListDef.map
               (λ x : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo,
                  base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base resolve cls x.1
                  |-> R (bluerock.lang.cpp.syntax.core.Tnamed x.1) q)
               (bluerock.lang.cpp.syntax.decl.s_bases st) ++
             Corelib.Lists.ListDef.map
               (λ m : bluerock.lang.cpp.syntax.decl.Member,
                  base ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field resolve
                            (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m))
                  |-> R (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).2
                        (bluerock.lang.cpp.logic.heap_pred.everywhere.mut_type m q).1)
               (bluerock.lang.cpp.syntax.decl.s_fields st))%list ∗
        base
        |-> (if bluerock.lang.cpp.syntax.decl.has_vtable st then bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls [] q else emp)) ∗
    base |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls q
bluerock.lang.cpp.logic.func.wp_dtor_intro:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (d : bluerock.lang.cpp.syntax.decl.Dtor) (args : 
                                                                                                               Corelib.Init.Datatypes.list
                                                                                                               bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (Q : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr → bluerock.lang.cpp.logic.wp.epred),
    match bluerock.lang.cpp.syntax.decl.d_body d with
    | Corelib.Init.Datatypes.Some body =>
        match args with
        | [] => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: expected one argument"%bs
        | [thisp] =>
            match bluerock.lang.cpp.syntax.translation_unit.types tu !! bluerock.lang.cpp.syntax.decl.d_class d with
            | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gunion _) =>
                ▷ match body with
                  | bluerock.lang.cpp.syntax.decl.Defaulted => λ k : bluerock.lang.cpp.logic.wp.Kpred, k bluerock.lang.cpp.logic.wp.Normal
                  | bluerock.lang.cpp.syntax.decl.UserDefined body0 =>
                      bluerock.lang.cpp.logic.wp.WPE.wp tu [region: [this := thisp]; return {?: "void"}] body0
                  end
                    (bluerock.lang.cpp.logic.func.Kreturn_void
                       (thisp
                        |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                              (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class d)) 1$m ∗
                        (thisp
                         |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                               (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class d)) 1$m -∗
                         ▷ ∀ p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr,
                             p
                             |-> bluerock.lang.cpp.logic.heap_pred.primR "void" 1$m
                                   bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vvoid -∗
                             Q p)))
            | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct s) =>
                ▷ match body with
                  | bluerock.lang.cpp.syntax.decl.Defaulted => λ k : bluerock.lang.cpp.logic.wp.Kpred, k bluerock.lang.cpp.logic.wp.Normal
                  | bluerock.lang.cpp.syntax.decl.UserDefined body0 =>
                      bluerock.lang.cpp.logic.wp.WPE.wp tu [region: [this := thisp]; return {?: "void"}] body0
                  end
                    (bluerock.lang.cpp.logic.func.Kreturn_void
                       (thisp |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR (bluerock.lang.cpp.syntax.decl.d_class d) 1$m ∗
                        bluerock.lang.cpp.logic.func.wpd_members tu (bluerock.lang.cpp.syntax.decl.d_class d) thisp
                          (bluerock.lang.cpp.syntax.decl.s_fields s)
                          (bluerock.lang.cpp.logic.func.wp_revert_identity thisp tu (bluerock.lang.cpp.syntax.decl.d_class d)
                             (bluerock.lang.cpp.logic.func.wpd_bases tu (bluerock.lang.cpp.syntax.decl.d_class d) thisp
                                (Corelib.Lists.ListDef.map Corelib.Init.Datatypes.fst (bluerock.lang.cpp.syntax.decl.s_bases s))
                                (thisp
                                 |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                       (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class d)) 1$m -∗
                                 ▷ ∀ p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr,
                                     p
                                     |-> bluerock.lang.cpp.logic.heap_pred.primR "void" 1$m
                                           bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vvoid -∗
                                     Q p)))))
            | _ => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: not a structure or union"%bs
            end
        | thisp :: _ :: _ => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: expected one argument"%bs
        end
    | Corelib.Init.Datatypes.None => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: no body"%bs
    end ⊢ ::wpDtor Q
bluerock.lang.cpp.logic.func.wp_dtor_elim:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (d : bluerock.lang.cpp.syntax.decl.Dtor) (args : 
                                                                                                               Corelib.Init.Datatypes.list
                                                                                                               bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) 
    (Q : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr → bluerock.lang.cpp.logic.wp.epred),
    ::wpDtor Q
    ⊢ match bluerock.lang.cpp.syntax.decl.d_body d with
      | Corelib.Init.Datatypes.Some body =>
          match args with
          | [] => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: expected one argument"%bs
          | [thisp] =>
              match bluerock.lang.cpp.syntax.translation_unit.types tu !! bluerock.lang.cpp.syntax.decl.d_class d with
              | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gunion _) =>
                  ▷ match body with
                    | bluerock.lang.cpp.syntax.decl.Defaulted =>
                        λ k : bluerock.lang.cpp.logic.wp.Kpred, |={⊤}=> k bluerock.lang.cpp.logic.wp.Normal
                    | bluerock.lang.cpp.syntax.decl.UserDefined body0 =>
                        bluerock.lang.cpp.logic.wp.WPE.wp tu [region: [this := thisp]; return {?: "void"}] body0
                    end
                      (bluerock.lang.cpp.logic.func.Kreturn_void
                         (thisp
                          |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class d)) 1$m ∗
                          (thisp
                           |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                 (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class d)) 1$m ={⊤}=∗
                           ▷ ∀ p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr,
                               p
                               |-> bluerock.lang.cpp.logic.heap_pred.primR "void" 1$m
                                     bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vvoid -∗
                               Q p)))
              | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct s) =>
                  ▷ match body with
                    | bluerock.lang.cpp.syntax.decl.Defaulted =>
                        λ k : bluerock.lang.cpp.logic.wp.Kpred, |={⊤}=> k bluerock.lang.cpp.logic.wp.Normal
                    | bluerock.lang.cpp.syntax.decl.UserDefined body0 =>
                        bluerock.lang.cpp.logic.wp.WPE.wp tu [region: [this := thisp]; return {?: "void"}] body0
                    end
                      (bluerock.lang.cpp.logic.func.Kreturn_void
                         (thisp |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR (bluerock.lang.cpp.syntax.decl.d_class d) 1$m ∗
                          bluerock.lang.cpp.logic.func.wpd_members tu (bluerock.lang.cpp.syntax.decl.d_class d) thisp
                            (bluerock.lang.cpp.syntax.decl.s_fields s)
                            (bluerock.lang.cpp.logic.func.wp_revert_identity thisp tu (bluerock.lang.cpp.syntax.decl.d_class d)
                               (bluerock.lang.cpp.logic.func.wpd_bases tu (bluerock.lang.cpp.syntax.decl.d_class d) thisp
                                  (Corelib.Lists.ListDef.map Corelib.Init.Datatypes.fst (bluerock.lang.cpp.syntax.decl.s_bases s))
                                  (thisp
                                   |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                         (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class d)) 1$m ={⊤}=∗
                                   ▷ ∀ p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr,
                                       p
                                       |-> bluerock.lang.cpp.logic.heap_pred.primR "void" 1$m
                                             bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vvoid -∗
                                       Q p)))))
              | _ => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: not a structure or union"%bs
              end
          | thisp :: _ :: _ => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: expected one argument"%bs
          end
      | Corelib.Init.Datatypes.None => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: no body"%bs
      end
bluerock.lang.cpp.logic.func.wp_dtor.unlock:
  @bluerock.lang.cpp.logic.func.wp_dtor =
  λ (thread_info : iris.bi.monpred.biIndex) (_Σ : iris.base_logic.lib.iprop.gFunctors) (Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ) (σ : bluerock.lang.cpp.semantics.genv.genv) 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (dtor : bluerock.lang.cpp.syntax.decl.Dtor) 
    (args : Corelib.Init.Datatypes.list bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (Q : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr
                                                                                                     → bluerock.lang.cpp.logic.wp.epred),
    match bluerock.lang.cpp.syntax.decl.d_body dtor with
    | Corelib.Init.Datatypes.Some body =>
        match args with
        | [] => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: expected one argument"%bs
        | [thisp] =>
            match bluerock.lang.cpp.syntax.translation_unit.types tu !! bluerock.lang.cpp.syntax.decl.d_class dtor with
            | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gunion _) =>
                (▷ match body with
                   | bluerock.lang.cpp.syntax.decl.Defaulted =>
                       λ k : bluerock.lang.cpp.logic.wp.Kpred, |={⊤}=> k bluerock.lang.cpp.logic.wp.Normal
                   | bluerock.lang.cpp.syntax.decl.UserDefined body0 =>
                       bluerock.lang.cpp.logic.wp.WPE.wp tu [region: [this := thisp]; return {?: "void"}] body0
                   end
                     (bluerock.lang.cpp.logic.func.Kreturn_void
                        (thisp
                         |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                               (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class dtor)) 1$m ∗
                         (thisp
                          |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class dtor)) 1$m ={⊤}=∗
                          ▷ ∀ p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr,
                              p
                              |-> bluerock.lang.cpp.logic.heap_pred.primR "void" 1$m
                                    bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vvoid -∗
                              Q p))))%I
            | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct s) =>
                (▷ match body with
                   | bluerock.lang.cpp.syntax.decl.Defaulted =>
                       λ k : bluerock.lang.cpp.logic.wp.Kpred, |={⊤}=> k bluerock.lang.cpp.logic.wp.Normal
                   | bluerock.lang.cpp.syntax.decl.UserDefined body0 =>
                       bluerock.lang.cpp.logic.wp.WPE.wp tu [region: [this := thisp]; return {?: "void"}] body0
                   end
                     (bluerock.lang.cpp.logic.func.Kreturn_void
                        (thisp |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR (bluerock.lang.cpp.syntax.decl.d_class dtor) 1$m ∗
                         bluerock.lang.cpp.logic.func.wpd_members tu (bluerock.lang.cpp.syntax.decl.d_class dtor) thisp
                           (bluerock.lang.cpp.syntax.decl.s_fields s)
                           (bluerock.lang.cpp.logic.func.wp_revert_identity thisp tu (bluerock.lang.cpp.syntax.decl.d_class dtor)
                              (bluerock.lang.cpp.logic.func.wpd_bases tu (bluerock.lang.cpp.syntax.decl.d_class dtor) thisp
                                 (Corelib.Lists.ListDef.map Corelib.Init.Datatypes.fst (bluerock.lang.cpp.syntax.decl.s_bases s))
                                 (thisp
                                  |-> bluerock.lang.cpp.logic.heap_pred.block.tblockR
                                        (bluerock.lang.cpp.syntax.core.Tnamed (bluerock.lang.cpp.syntax.decl.d_class dtor)) 1$m ={⊤}=∗
                                  ▷ ∀ p : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr,
                                      p
                                      |-> bluerock.lang.cpp.logic.heap_pred.primR "void" 1$m
                                            bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.Vvoid -∗
                                      Q p))))))%I
            | _ => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: not a structure or union"%bs
            end
        | thisp :: _ :: _ => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: expected one argument"%bs
        end
    | Corelib.Init.Datatypes.None => bluerock.iris.extra.bi.errors.Errors.ERROR.body "wp_dtor: no body"%bs
    end
bluerock.lang.cpp.logic.const.wp_const_intro:
  ∀ {thread_info : iris.bi.monpred.biIndex} {_Σ : iris.base_logic.lib.iprop.gFunctors} {Σ : bluerock.lang.cpp.logic.mpred.LC.cpp_logic
                                                                                              thread_info _Σ} {σ : bluerock.lang.cpp.semantics.genv.genv} 
    (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit) (f t : bluerock.lang.cpp.algebra.cfrac.cQp.t) 
    (a : bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.ptr) (ty : bluerock.lang.cpp.syntax.core.decltype) (Q : bluerock.lang.cpp.logic.wp.epred),
    (let
     '(cv, rty) := bluerock.lang.cpp.syntax.types.decompose_type ty in
      if bluerock.lang.cpp.syntax.preliminary.q_const cv
      then |={⊤}=> Q
      else
       |={⊤}=>
         match rty with
         | bluerock.lang.cpp.syntax.core.Tref rty0 | bluerock.lang.cpp.syntax.core.Trv_ref rty0 =>
             ∃ v : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val,
               a
               |-> bluerock.lang.cpp.logic.heap_pred.primR
                     (bluerock.lang.cpp.syntax.core.Tref (bluerock.lang.cpp.syntax.types.erase_qualifiers rty0)) f v ∗
               (a
                |-> bluerock.lang.cpp.logic.heap_pred.primR
                      (bluerock.lang.cpp.syntax.core.Tref (bluerock.lang.cpp.syntax.types.erase_qualifiers rty0)) t v ={⊤}=∗
                Q)
         | bluerock.lang.cpp.syntax.core.Tarray ety sz =>
             Stdlib.Lists.List.fold_left
               (λ (Q0 : bluerock.lang.cpp.logic.wp.epred) (i : Corelib.Numbers.BinNums.N),
                  bluerock.lang.cpp.logic.const.wp_const tu f t (a .[ bluerock.lang.cpp.syntax.types.erase_qualifiers ety ! i ]) ety Q0)
               (bluerock.prelude.list_numbers.seqN 0 sz) (|={⊤}=> Q)
         | bluerock.lang.cpp.syntax.core.Tnamed cls =>
             match bluerock.lang.cpp.syntax.translation_unit.types tu !! cls with
             | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gunion u) =>
                 ∃ br : Corelib.Init.Datatypes.option Corelib.Init.Datatypes.nat,
                   a |-> bluerock.lang.cpp.logic.heap_pred.aggregate.unionR cls f br ∗
                   (a |-> bluerock.lang.cpp.logic.heap_pred.aggregate.unionR cls t br -∗
                    match br with
                    | Corelib.Init.Datatypes.Some br0 =>
                        match bluerock.lang.cpp.syntax.decl.u_fields u !! br0 with
                        | Corelib.Init.Datatypes.Some m =>
                            if bluerock.lang.cpp.syntax.decl.mem_mutable m
                            then |={⊤}=> Q
                            else
                             bluerock.lang.cpp.logic.const.wp_const tu f t
                               (a ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field σ
                                       (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m)))
                               (bluerock.lang.cpp.syntax.decl.mem_type m) (|={⊤}=> Q)
                        | Corelib.Init.Datatypes.None => bluerock.lang.cpp.logic.const.wp_const tu f t a ty (|={⊤}=> Q)
                        end
                    | Corelib.Init.Datatypes.None => |={⊤}=> Q
                    end)
             | Corelib.Init.Datatypes.Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct st) =>
                 Stdlib.Lists.List.fold_left
                   (λ (Q0 : bluerock.lang.cpp.logic.wp.epred) '(b, _),
                      bluerock.lang.cpp.logic.const.wp_const tu f t (a ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_base σ cls b)
                        (bluerock.lang.cpp.syntax.core.Tnamed b) Q0)
                   (bluerock.lang.cpp.syntax.decl.s_bases st)
                   (Stdlib.Lists.List.fold_left
                      (λ (Q0 : bluerock.lang.cpp.logic.wp.epred) (m : bluerock.lang.cpp.syntax.decl.Member),
                         if bluerock.lang.cpp.syntax.decl.mem_mutable m
                         then Q0
                         else
                          bluerock.lang.cpp.logic.const.wp_const tu f t
                            (a ,, bluerock.lang.cpp.semantics.values.PTRS_INTF_AXIOM.o_field σ
                                    (bluerock.lang.cpp.syntax.core.Field cls (bluerock.lang.cpp.syntax.decl.mem_name m)))
                            (bluerock.lang.cpp.syntax.decl.mem_type m) Q0)
                      (bluerock.lang.cpp.syntax.decl.s_fields st)
                      (a |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls f ∗
                       (a |-> bluerock.lang.cpp.logic.heap_pred.aggregate.structR cls t -∗
                        if bluerock.lang.cpp.syntax.decl.has_vtable st
                        then
                         ∃ path : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.globname,
                           a |-> bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls path f ∗
                           (a |-> bluerock.lang.cpp.logic.heap_pred.simple.derivationR cls path t ={⊤}=∗ Q)
                        else |={⊤}=> Q)))
             | _ => bluerock.lang.cpp.logic.const.wp_const tu f t a ty (|={⊤}=> Q)
             end
         | bluerock.lang.cpp.syntax.core.Tptr _ | bluerock.lang.cpp.syntax.core.Tnum _ _ | bluerock.lang.cpp.syntax.core.Tchar_ _ |
           "void"%cpp_type | bluerock.lang.cpp.syntax.core.Tenum _ | "bool"%cpp_type | bluerock.lang.cpp.syntax.core.Tmember_pointer _ _ |
           bluerock.lang.cpp.syntax.core.Tfloat_ _ | "nullptr_t"%cpp_type =>
             ∃ v : bluerock.lang.cpp.semantics.values.VALUES_INTF_AXIOM.val,
               a |-> bluerock.lang.cpp.logic.heap_pred.tptstoR (bluerock.lang.cpp.syntax.types.erase_qualifiers rty) f v ∗
               (a |-> bluerock.lang.cpp.logic.heap_pred.tptstoR (bluerock.lang.cpp.syntax.types.erase_qualifiers rty) t v ={⊤}=∗ Q)
         | bluerock.lang.cpp.syntax.core.Tfunction _ | bluerock.lang.cpp.syntax.core.Tarch _ _ =>
             bluerock.lang.cpp.logic.const.wp_const tu f t a ty (|={⊤}=> Q)
         | _ => False
         end)
    ⊢ bluerock.lang.cpp.logic.const.wp_const tu f t a ty Q

## Assistant 2

I will define a single‐argument “model” predicate 

  uint256R (q: cQp.t) (x:Z) : Rep

which asserts that at `this→data` you have a 4‐limb little‐endian array of 64-bit words whose unsigned value is `x mod 2^256`, and also the usual `structR` tag of the class.  Then the spec for 

    void uint256::add(const uint256& other)

says that we take full (1) ownership of `this` (so we can write), and only fractional ownership of `other` (we only read), and upon return `this` contains `x_this + x_other mod 2^256`, and all ownership is returned.

```gallina
(* Rep‐predicate for uint256: one Z model, not four. *)
Definition uint256R (q: cQp.t) (x: Z) : Rep :=
  let mask := (2^64)%Z in
  let l0 := (x mod mask)%Z in
  let l1 := (Z.div x mask mod mask)%Z in
  let l2 := (Z.div x (mask*mask) mod mask)%Z in
  let l3 := (Z.div x (mask*mask*mask) mod mask)%Z in
  (* at the data field we have a 4‐cell array of 64-bit limbs *)
  _field "::uint256::data" |-> bluerock.lang.cpp.logic.arr.arrayR
     "unsigned long long"%cpp_type
     (fun limb => primR "unsigned long long"%cpp_type q (Vint limb))
     [l0; l1; l2; l3]
  ** structR "uint256" q.

(* Spec of the add method *)
  cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (thisp: ptr) =>
     \arg{xother:Z}{qother:Qp} "other" (Vptr thisp) (* we will rebind othersp next *)
     \prepost{(xv:Z) (xother:Z) (q:Qp)}
       thisp |-> uint256R (cQp.mut 1) xv
     ** (othersp:ptr) |-> uint256R (cQp.mut q) xother
     \post thisp |-> uint256R (cQp.mut 1) ((xv + xother) mod (2^256)%Z)
   ).
```

Explanation:

-  We package the four 64-bit limbs into a single Gallina `Z` (the mathematical value modulo 2^256).
-  `uint256R q x` uses `arrayR` at the `data` field plus `structR` for class‐identity.
-  In the `add`‐spec we split off full ownership of `this` (so it can be written) and arbitrary fractional ownership `q` of `other` (only read).  `\prepost` on `this` returns its ownership unchanged, and `\post` on `other` returns unchanged fractional ownership.  The new `this` value is `(xv + xother) mod 2^256`.

## User 3

Below is the error I get when I give that to Coq. FIRST, explain why Coq gave that error and how it can be fixed. THEN, fix the error and GIVE ME BACK THE ENTIRE SOLUTION AGAIN, NOT JUST THE FIXED PART.

Toplevel input, characters 115-116:
>      \arg{xother:Z}{qother:Qp} "other" (Vptr thisp) (* we will rebind othersp next *)
>                              ^
Error: Syntax error: '&' or '|' expected after [term level 200] (in [term]).


## Assistant 3

Coq is complaining on 

    \arg{xother:Z}{qother:Qp} "other" (Vptr thisp)

because the quantifier‐binding syntax for `\arg` expects all of its binders to be in one pair of `{…}` and each binder in its own parentheses, e.g.:

    \arg{(othersp:ptr) (xother:Z) (q:Qp)} "other" (Vptr othersp)

—and not two successive `{…}`.  In addition, we really need to bind not only `xother` and `q` but also the pointer variable (`othersp`) itself.  

Here is the corrected, self‐contained solution.  I quantify `(othersp:ptr) (xother:Z) (q:Qp)` all together in one `\arg`.  

```gallina
(* Rep‐predicate for uint256: just one Z-model, not four separate limbs. *)
Definition uint256R (q: cQp.t) (x: Z) : Rep :=
  let mask := (2^64)%Z in
  let l0 := (x mod mask)%Z in
  let l1 := (Z.div x mask mod mask)%Z in
  let l2 := (Z.div x (mask*mask) mod mask)%Z in
  let l3 := (Z.div x (mask*mask*mask) mod mask)%Z in
  (* the four‐element little‐endian array in data[], plus the struct tag *)
  _field "::uint256::data" |-> bluerock.lang.cpp.logic.arr.arrayR
     "unsigned long long"%cpp_type
     (fun limb => primR "unsigned long long"%cpp_type q (Vint limb))
     [l0; l1; l2; l3]
  ** structR "uint256" q.

(* Separation‐logic spec for uint256::add(const uint256&). *)
  cpp.spec "uint256::add(const uint256&)" as uint256_add_spec with (fun (thisp: ptr) =>
     (* bind the actual C++ reference argument plus its model Z and fraction *)
     \arg{(othersp:ptr) (xother:Z) (q:Qp)} "other" (Vptr othersp)
     (* model for 'this' only Z, full ownership so we use \prepost *)
     \prepost{(xv:Z)} thisp |-> uint256R (cQp.mut 1) xv
     (* precondition also needs fractional read‐only ownership of 'other' *)
     \pre othersp |-> uint256R (cQp.mut q) xother
     (* postcondition: 'this' has been updated to xv+xother mod 2^256 *)
     \post thisp |-> uint256R (cQp.mut 1) ((xv + xother) mod (2^256)%Z)
   ).
```

