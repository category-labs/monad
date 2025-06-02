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



# Current Task
In the current Coq context, I have `block_state_cpp.module:translation_unit` which is a translation of the AST of block_state.cpp (and its includes, recursively) to Coq.
Write a gallina function `find_struct` that takes a `translation_unit` and an argumement `nm: name` and returns an `option _` which is a definition of the struct whose fully qualified name is `name`. Chose an appropriate type for the placeholder `_`.

## Results of some relevant queries
>>> Print translation_unit.
Record translation_unit : Type := Build_translation_unit
  { symbols : bluerock.lang.cpp.syntax.translation_unit.symbol_table;
    types : bluerock.lang.cpp.syntax.translation_unit.type_table;
    initializer : bluerock.lang.cpp.syntax.translation_unit.InitializerBlock;
    byte_order : bluerock.prelude.arith.types.endian }.

translation_unit has primitive projections with eta conversion.
Arguments bluerock.lang.cpp.syntax.translation_unit.Build_translation_unit symbols types initializer byte_order
Arguments bluerock.lang.cpp.syntax.translation_unit.symbols t
Arguments bluerock.lang.cpp.syntax.translation_unit.types t
Arguments bluerock.lang.cpp.syntax.translation_unit.initializer t
Arguments bluerock.lang.cpp.syntax.translation_unit.byte_order t

>>> Print name.
Notation bluerock.lang.cpp.syntax.core.name := bluerock.lang.cpp.syntax.core.name'

Inductive name' : Set :=
    Ninst : bluerock.lang.cpp.syntax.core.name
            → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.temp_arg → bluerock.lang.cpp.syntax.core.name
  | Nglobal : bluerock.lang.cpp.syntax.core.atomic_name_ bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.name
  | Ndependent : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.name
  | Nscoped : bluerock.lang.cpp.syntax.core.name
              → bluerock.lang.cpp.syntax.core.atomic_name_ bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.name
  | Nunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.core.name
  with temp_arg' : Set :=
    Atype : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.temp_arg
  | Avalue : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.temp_arg
  | Apack : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.temp_arg → bluerock.lang.cpp.syntax.core.temp_arg
  | Atemplate : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.temp_arg
  | Aunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.core.temp_arg
  with type' : Set :=
    Tparam : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.type
  | Tresult_param : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.type
  | Tresult_global : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.type
  | Tresult_unop : bluerock.lang.cpp.syntax.overloadable.RUnOp → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tresult_binop : bluerock.lang.cpp.syntax.overloadable.RBinOp
                    → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tresult_call : bluerock.lang.cpp.syntax.core.name
                   → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tresult_member_call : bluerock.lang.cpp.syntax.core.name
                          → bluerock.lang.cpp.syntax.core.type
                            → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tresult_parenlist : bluerock.lang.cpp.syntax.core.type
                        → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tresult_member : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.type
  | Tptr : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tref : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Trv_ref : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tnum : bluerock.lang.cpp.syntax.preliminary.int_rank → bluerock.prelude.arith.types.signed → bluerock.lang.cpp.syntax.core.type
  | Tchar_ : bluerock.lang.cpp.syntax.preliminary.char_type → bluerock.lang.cpp.syntax.core.type
  | Tvoid : bluerock.lang.cpp.syntax.core.type
  | Tarray : bluerock.lang.cpp.syntax.core.type → Corelib.Numbers.BinNums.N → bluerock.lang.cpp.syntax.core.type
  | Tincomplete_array : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tvariable_array : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type
  | Tnamed : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.type
  | Tenum : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.type
  | Tfunction : bluerock.lang.cpp.syntax.core.function_type_ bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tbool : bluerock.lang.cpp.syntax.core.type
  | Tmember_pointer : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tfloat_ : bluerock.lang.cpp.syntax.preliminary.float_type.t → bluerock.lang.cpp.syntax.core.type
  | Tqualified : bluerock.lang.cpp.syntax.preliminary.type_qualifiers
                 → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.type
  | Tnullptr : bluerock.lang.cpp.syntax.core.type
  | Tarch : Corelib.Init.Datatypes.option bluerock.prelude.arith.types.bitsize
            → Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.core.type
  | Tdecltype : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type
  | Texprtype : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type
  | Tunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.core.type
  with Expr' : Set :=
    Eparam : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_global : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_unop : bluerock.lang.cpp.syntax.overloadable.RUnOp → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_binop : bluerock.lang.cpp.syntax.overloadable.RBinOp
                        → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_call : bluerock.lang.cpp.syntax.core.name
                       → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_member_call : bluerock.lang.cpp.syntax.core.name
                              → bluerock.lang.cpp.syntax.core.Expr
                                → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_parenlist : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.type
                            → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eunresolved_member : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.Expr
  | Evar : bluerock.lang.cpp.syntax.preliminary.localname → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eenum_const : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.Expr
  | Eglobal : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eglobal_member : bluerock.lang.cpp.syntax.core.name → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Echar : Corelib.Numbers.BinNums.N → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Estring : bluerock.lang.cpp.syntax.literal_string.literal_string.t
              → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eint : Corelib.Numbers.BinNums.Z → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Ebool : Corelib.Init.Datatypes.bool → bluerock.lang.cpp.syntax.core.Expr
  | Eunop : bluerock.lang.cpp.syntax.preliminary.UnOp
            → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Ebinop : bluerock.lang.cpp.syntax.preliminary.BinOp
             → bluerock.lang.cpp.syntax.core.Expr
               → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Ederef : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eaddrof : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eassign : bluerock.lang.cpp.syntax.core.Expr
              → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eassign_op : bluerock.lang.cpp.syntax.preliminary.BinOp
                 → bluerock.lang.cpp.syntax.core.Expr
                   → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Epreinc : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Epostinc : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Epredec : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Epostdec : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eseqand : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eseqor : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Ecomma : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Ecall : bluerock.lang.cpp.syntax.core.Expr
            → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eexplicit_cast : bluerock.lang.cpp.syntax.core.cast_style.t
                     → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Ecast : bluerock.lang.cpp.syntax.core.Cast → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Emember : Corelib.Init.Datatypes.bool
              → bluerock.lang.cpp.syntax.core.Expr
                → bluerock.lang.cpp.syntax.core.atomic_name_ bluerock.lang.cpp.syntax.core.type
                  → Corelib.Init.Datatypes.bool → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Emember_ignore : Corelib.Init.Datatypes.bool
                     → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Emember_call : Corelib.Init.Datatypes.bool
                   → bluerock.lang.cpp.syntax.preliminary.MethodRef_ bluerock.lang.cpp.syntax.core.name bluerock.lang.cpp.syntax.core.type
                       bluerock.lang.cpp.syntax.core.Expr
                     → bluerock.lang.cpp.syntax.core.Expr
                       → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eoperator_call : bluerock.lang.cpp.syntax.preliminary.OverloadableOperator
                     → bluerock.lang.cpp.syntax.preliminary.operator_impl.t bluerock.lang.cpp.syntax.core.name
                         bluerock.lang.cpp.syntax.core.type
                       → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Esubscript : bluerock.lang.cpp.syntax.core.Expr
                 → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Esizeof : bluerock.lang.cpp.syntax.core.type + bluerock.lang.cpp.syntax.core.Expr
              → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Ealignof : bluerock.lang.cpp.syntax.core.type + bluerock.lang.cpp.syntax.core.Expr
               → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eoffsetof : bluerock.lang.cpp.syntax.core.type
                → bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Econstructor : bluerock.lang.cpp.syntax.core.name
                   → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr
                     → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Elambda : bluerock.lang.cpp.syntax.core.name
              → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eimplicit : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Eimplicit_init : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eif : bluerock.lang.cpp.syntax.core.Expr
          → bluerock.lang.cpp.syntax.core.Expr
            → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eif2 : Corelib.Numbers.BinNums.N
           → bluerock.lang.cpp.syntax.core.Expr
             → bluerock.lang.cpp.syntax.core.Expr
               → bluerock.lang.cpp.syntax.core.Expr
                 → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Ethis : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Enull : bluerock.lang.cpp.syntax.core.Expr
  | Einitlist : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr
                → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr
                  → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Einitlist_union : bluerock.lang.cpp.syntax.core.atomic_name_ bluerock.lang.cpp.syntax.core.type
                      → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr
                        → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Enew : bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.core.type
           → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr
             → bluerock.lang.cpp.syntax.preliminary.new_form
               → bluerock.lang.cpp.syntax.core.type
                 → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr
                   → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Edelete : Corelib.Init.Datatypes.bool
              → bluerock.lang.cpp.syntax.core.name
                → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eandclean : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Ematerialize_temp : bluerock.lang.cpp.syntax.core.Expr
                        → bluerock.lang.cpp.syntax.preliminary.ValCat → bluerock.lang.cpp.syntax.core.Expr
  | Eatomic : bluerock.lang.cpp.syntax.preliminary.AtomicOp
              → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.Expr
                → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Estmt : bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eva_arg : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Epseudo_destructor : Corelib.Init.Datatypes.bool
                         → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.Expr
  | Earrayloop_init : Corelib.Numbers.BinNums.N
                      → bluerock.lang.cpp.syntax.core.Expr
                        → Corelib.Numbers.BinNums.N
                          → Corelib.Numbers.BinNums.N
                            → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Earrayloop_index : Corelib.Numbers.BinNums.N → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eopaque_ref : Corelib.Numbers.BinNums.N → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  | Eunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr
  with Stmt' : Set :=
    Sseq : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sdecl : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.stmt.VarDecl → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sif : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.stmt.VarDecl
          → bluerock.lang.cpp.syntax.core.Expr
            → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sif_consteval : bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Swhile : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.stmt.VarDecl
             → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sfor : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.stmt.Stmt
           → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr
             → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr
               → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sdo : bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sswitch : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.stmt.VarDecl
              → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Scase : bluerock.lang.cpp.syntax.preliminary.SwitchBranch → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sdefault : bluerock.lang.cpp.syntax.stmt.Stmt
  | Sbreak : bluerock.lang.cpp.syntax.stmt.Stmt
  | Scontinue : bluerock.lang.cpp.syntax.stmt.Stmt
  | Sreturn : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sexpr : bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sattr : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.preliminary.ident
            → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sasm : Corelib.Strings.PrimString.string
           → Corelib.Init.Datatypes.bool
             → Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.preliminary.ident * bluerock.lang.cpp.syntax.core.Expr)
               → Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.preliminary.ident * bluerock.lang.cpp.syntax.core.Expr)
                 → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.stmt.Stmt
  | Slabeled : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.stmt.Stmt → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sgoto : bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.stmt.Stmt
  | Sunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.stmt.Stmt
  with VarDecl' : Set :=
    Dvar : bluerock.lang.cpp.syntax.preliminary.localname
           → bluerock.lang.cpp.syntax.core.type
             → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.VarDecl
  | Ddecompose : bluerock.lang.cpp.syntax.core.Expr
                 → bluerock.lang.cpp.syntax.preliminary.ident
                   → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.BindingDecl → bluerock.lang.cpp.syntax.stmt.VarDecl
  | Dinit : Corelib.Init.Datatypes.bool
            → bluerock.lang.cpp.syntax.core.name
              → bluerock.lang.cpp.syntax.core.type
                → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.stmt.VarDecl
  with BindingDecl' : Set :=
    Bvar : bluerock.lang.cpp.syntax.preliminary.localname
           → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.BindingDecl
  | Bbind : bluerock.lang.cpp.syntax.preliminary.localname
            → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.core.BindingDecl
  with Cast' : Set :=
    Cdependent : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cbitcast : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Clvaluebitcast : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cl2r : bluerock.lang.cpp.syntax.core.Cast
  | Cl2r_bitcast : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cnoop : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Carray2ptr : bluerock.lang.cpp.syntax.core.Cast
  | Cfun2ptr : bluerock.lang.cpp.syntax.core.Cast
  | Cint2ptr : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cptr2int : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cptr2bool : bluerock.lang.cpp.syntax.core.Cast
  | Cintegral : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cint2bool : bluerock.lang.cpp.syntax.core.Cast
  | Cfloat2int : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cint2float : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cfloat : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cnull2ptr : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cnull2memberptr : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cbuiltin2fun : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | C2void : bluerock.lang.cpp.syntax.core.Cast
  | Cctor : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cuser : bluerock.lang.cpp.syntax.core.Cast
  | Cdynamic : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cderived2base : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.type
                    → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cbase2derived : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.core.type
                    → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast
  | Cunsupported : bluerock.prelude.bytestring_core.BS.Bytestring_notations.bs
                   → bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.core.Cast.

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

# Contents of the current file

```coq
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import monad.proofs.misc.
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.tutorials.demo2.
Require Import monad.tutorials.demomisc.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import stdpp.list.
Import stdpp.decidable.
Import cQp_compat.
Open Scope cQp_scope.
Open Scope Z_scope.
Import linearity.
Import Verbose.
Ltac slauto := misc.slauto1.
Disable Notation take.
Disable Notation drop.
Disable Notation "`div`" (all).
Disable Notation intR.
Disable Notation uintR.
Import linearity.
Disable Notation atomic_name'.
Disable Notation atomic_name.
Open Scope pstring_scope.
Set Printing FullyQualifiedNames.
Require Import monad.asts.block_state_cpp. (* this defines module: translation_unit, the  AST of block_state.cpp (and all its transitive includes). block_state_cpp.v is autogenerated by cpp2v *)



```

 You cannot change the content above. Your response will always be inserted after the above content. Do not repeat the above content in your response.



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

Before defining `find_struct`, we need to know exactly how `struct`‐/`class`‐definitions are recorded in the `translation_unit` (in `symbols` or in `types`).  Let's look up:

 1. What is the definition of the two tables
    `bluerock.lang.cpp.syntax.translation_unit.symbol_table`
    and
    `bluerock.lang.cpp.syntax.translation_unit.type_table`?
 2. In which one are `struct` or `class` definitions stored, and under what form?

So I will query:

```coqquery
About bluerock.lang.cpp.syntax.translation_unit.symbol_table.
About bluerock.lang.cpp.syntax.translation_unit.type_table.
Search "struct" in bluerock.lang.cpp.syntax.translation_unit.
```

## User 2

>>> About bluerock.lang.cpp.syntax.translation_unit.symbol_table.
bluerock.lang.cpp.syntax.translation_unit.symbol_table : Type

bluerock.lang.cpp.syntax.translation_unit.symbol_table is not universe polymorphic
bluerock.lang.cpp.syntax.translation_unit.symbol_table is transparent
Expands to: Constant bluerock.lang.cpp.syntax.translation_unit.symbol_table
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 132, characters 11-23

>>> About bluerock.lang.cpp.syntax.translation_unit.type_table.
bluerock.lang.cpp.syntax.translation_unit.type_table : Type

bluerock.lang.cpp.syntax.translation_unit.type_table is not universe polymorphic
bluerock.lang.cpp.syntax.translation_unit.type_table is transparent
Expands to: Constant bluerock.lang.cpp.syntax.translation_unit.type_table
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 34, characters 11-21

>>> Search "struct" in bluerock.lang.cpp.syntax.translation_unit.
bluerock.lang.cpp.syntax.translation_unit.Odestructor:
  bluerock.lang.cpp.syntax.decl.Dtor → bluerock.lang.cpp.syntax.translation_unit.ObjValue
bluerock.lang.cpp.syntax.translation_unit.Gstruct: bluerock.lang.cpp.syntax.decl.Struct → bluerock.lang.cpp.syntax.translation_unit.GlobDecl
bluerock.lang.cpp.syntax.translation_unit.Oconstructor:
  bluerock.lang.cpp.syntax.decl.Ctor → bluerock.lang.cpp.syntax.translation_unit.ObjValue
bluerock.lang.cpp.syntax.translation_unit.is_trivially_destructible:
  bluerock.lang.cpp.syntax.translation_unit.translation_unit → bluerock.lang.cpp.syntax.core.type → Corelib.Init.Datatypes.bool

## Assistant 2

Before proceeding with the implementation, I need to see

 1. The definition of `symbol_table` so I know how to look up a name.
 2. The definition of `GlobDecl` and in particular the `Gstruct` constructor, plus the `Struct` type.

Thus, I will ask:

```coqquery
Print bluerock.lang.cpp.syntax.translation_unit.symbol_table.
About bluerock.lang.cpp.syntax.translation_unit.GlobDecl.
About bluerock.lang.cpp.syntax.translation_unit.Gstruct.
About bluerock.lang.cpp.syntax.decl.Struct.
Search "lookup" in bluerock.lang.cpp.syntax.translation_unit.
```

## User 3

>>> Print bluerock.lang.cpp.syntax.translation_unit.symbol_table.
bluerock.lang.cpp.syntax.translation_unit.symbol_table =
bluerock.lang.cpp.syntax.namemap.NM.t bluerock.lang.cpp.syntax.translation_unit.ObjValue
     : Type

>>> About bluerock.lang.cpp.syntax.translation_unit.GlobDecl.
Notation bluerock.lang.cpp.syntax.translation_unit.GlobDecl := bluerock.lang.cpp.syntax.translation_unit.GlobDecl'
Expands to: Notation bluerock.lang.cpp.syntax.translation_unit.GlobDecl
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 29, characters 0-31

bluerock.lang.cpp.syntax.translation_unit.GlobDecl' : Set

bluerock.lang.cpp.syntax.translation_unit.GlobDecl' is not universe polymorphic
Expands to: Inductive bluerock.lang.cpp.syntax.translation_unit.GlobDecl'
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 21, characters 8-17

>>> About bluerock.lang.cpp.syntax.translation_unit.Gstruct.
bluerock.lang.cpp.syntax.translation_unit.Gstruct :
bluerock.lang.cpp.syntax.decl.Struct → bluerock.lang.cpp.syntax.translation_unit.GlobDecl

bluerock.lang.cpp.syntax.translation_unit.Gstruct is not universe polymorphic
Expands to: Constructor bluerock.lang.cpp.syntax.translation_unit.Gstruct
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 24, characters 4-11

>>> About bluerock.lang.cpp.syntax.decl.Struct.
Notation bluerock.lang.cpp.syntax.decl.Struct := bluerock.lang.cpp.syntax.decl.Struct'
Expands to: Notation bluerock.lang.cpp.syntax.decl.Struct
Declared in library bluerock.lang.cpp.syntax.decl, line 132, characters 0-27

bluerock.lang.cpp.syntax.decl.Struct' : Set

bluerock.lang.cpp.syntax.decl.Struct' is not universe polymorphic
Expands to: Inductive bluerock.lang.cpp.syntax.decl.Struct'
Declared in library bluerock.lang.cpp.syntax.decl, line 101, characters 7-14

>>> Search "lookup" in bluerock.lang.cpp.syntax.translation_unit.
∅ (no results)

## Assistant 3

I need to see the definitions of `ObjValue`, the full inductive for `GlobDecl'`, and the lookup function in `NM`:

```coqquery
About bluerock.lang.cpp.syntax.translation_unit.ObjValue.
Print bluerock.lang.cpp.syntax.translation_unit.GlobDecl'.
Print bluerock.lang.cpp.syntax.decl.Struct'.
Search bluerock.lang.cpp.syntax.namemap "find".
```

## User 4

>>> About bluerock.lang.cpp.syntax.translation_unit.ObjValue.
Notation bluerock.lang.cpp.syntax.translation_unit.ObjValue := bluerock.lang.cpp.syntax.translation_unit.ObjValue'
Expands to: Notation bluerock.lang.cpp.syntax.translation_unit.ObjValue
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 95, characters 0-31

bluerock.lang.cpp.syntax.translation_unit.ObjValue' : Set

bluerock.lang.cpp.syntax.translation_unit.ObjValue' is not universe polymorphic
Expands to: Inductive bluerock.lang.cpp.syntax.translation_unit.ObjValue'
Declared in library bluerock.lang.cpp.syntax.translation_unit, line 89, characters 8-17

>>> Print bluerock.lang.cpp.syntax.translation_unit.GlobDecl'.
Variant GlobDecl' : Set :=
    Gtype : bluerock.lang.cpp.syntax.translation_unit.GlobDecl
  | Gunion : bluerock.lang.cpp.syntax.decl.Union → bluerock.lang.cpp.syntax.translation_unit.GlobDecl
  | Gstruct : bluerock.lang.cpp.syntax.decl.Struct → bluerock.lang.cpp.syntax.translation_unit.GlobDecl
  | Genum : bluerock.lang.cpp.syntax.core.type
            → Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.preliminary.ident → bluerock.lang.cpp.syntax.translation_unit.GlobDecl
  | Gconstant : bluerock.lang.cpp.syntax.core.type
                → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.Expr → bluerock.lang.cpp.syntax.translation_unit.GlobDecl
  | Gtypedef : bluerock.lang.cpp.syntax.core.type → bluerock.lang.cpp.syntax.translation_unit.GlobDecl
  | Gunsupported : Corelib.Strings.PrimString.string → bluerock.lang.cpp.syntax.translation_unit.GlobDecl.

Arguments bluerock.lang.cpp.syntax.translation_unit.Genum _%_cpp_type_scope _%_list_scope
Arguments bluerock.lang.cpp.syntax.translation_unit.Gconstant _%_cpp_type_scope init
Arguments bluerock.lang.cpp.syntax.translation_unit.Gtypedef _%_cpp_type_scope
Arguments bluerock.lang.cpp.syntax.translation_unit.Gunsupported _%_pstring_scope

>>> Print bluerock.lang.cpp.syntax.decl.Struct'.
Record Struct' : Set := Build_Struct
  { s_bases : Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.core.name * bluerock.lang.cpp.syntax.decl.LayoutInfo);
    s_fields : Corelib.Init.Datatypes.list bluerock.lang.cpp.syntax.decl.Member;
    s_virtuals : Corelib.Init.Datatypes.list
                   (bluerock.lang.cpp.syntax.core.obj_name * Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.obj_name);
    s_overrides : Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.core.obj_name * bluerock.lang.cpp.syntax.core.obj_name);
    s_dtor : bluerock.lang.cpp.syntax.core.obj_name;
    s_trivially_destructible : Corelib.Init.Datatypes.bool;
    s_delete : Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.core.obj_name;
    s_layout : bluerock.lang.cpp.syntax.decl.LayoutType;
    s_size : Corelib.Numbers.BinNums.N;
    s_alignment : Corelib.Numbers.BinNums.N }.

Arguments bluerock.lang.cpp.syntax.decl.Build_Struct (s_bases s_fields s_virtuals s_overrides)%_list_scope s_dtor%_cpp_name_scope
  s_trivially_destructible%_bool_scope s_delete s_layout (s_size s_alignment)%_N_scope
Arguments bluerock.lang.cpp.syntax.decl.s_bases s
Arguments bluerock.lang.cpp.syntax.decl.s_fields s
Arguments bluerock.lang.cpp.syntax.decl.s_virtuals s
Arguments bluerock.lang.cpp.syntax.decl.s_overrides s
Arguments bluerock.lang.cpp.syntax.decl.s_dtor s
Arguments bluerock.lang.cpp.syntax.decl.s_trivially_destructible s
Arguments bluerock.lang.cpp.syntax.decl.s_delete s
Arguments bluerock.lang.cpp.syntax.decl.s_layout s
Arguments bluerock.lang.cpp.syntax.decl.s_size s
Arguments bluerock.lang.cpp.syntax.decl.s_alignment s

>>> Search bluerock.lang.cpp.syntax.namemap "find".
Toplevel input, characters 7-39:
> Search bluerock.lang.cpp.syntax.namemap "find".
>        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The reference bluerock.lang.cpp.syntax.namemap was not found in the current environment.

## Assistant 4

We need to inspect `ObjValue'` and the lookup function in the `namemap` module. Then we can write `find_struct` by looking up `nm` in the `symbols`, matching on `Some (OVglob (Gstruct s))`, and returning `Some s`. 

First, show `ObjValue'` and the `lookup` in `namemap`:

```coqquery
Print bluerock.lang.cpp.syntax.translation_unit.ObjValue'.
Locate bluerock.lang.cpp.syntax.namemap.NM.t.
Search bluerock.lang.cpp.syntax.namemap.
```

## User 5

>>> Print bluerock.lang.cpp.syntax.translation_unit.ObjValue'.
Variant ObjValue' : Set :=
    Ovar : bluerock.lang.cpp.syntax.core.type
           → bluerock.lang.cpp.syntax.translation_unit.global_init.t → bluerock.lang.cpp.syntax.translation_unit.ObjValue
  | Ofunction : bluerock.lang.cpp.syntax.decl.Func → bluerock.lang.cpp.syntax.translation_unit.ObjValue
  | Omethod : bluerock.lang.cpp.syntax.decl.Method → bluerock.lang.cpp.syntax.translation_unit.ObjValue
  | Oconstructor : bluerock.lang.cpp.syntax.decl.Ctor → bluerock.lang.cpp.syntax.translation_unit.ObjValue
  | Odestructor : bluerock.lang.cpp.syntax.decl.Dtor → bluerock.lang.cpp.syntax.translation_unit.ObjValue.

Arguments bluerock.lang.cpp.syntax.translation_unit.Ovar _%_cpp_type_scope _

>>> Locate bluerock.lang.cpp.syntax.namemap.NM.t.
Constant bluerock.lang.cpp.syntax.namemap.NM.t (syntactically equal to bluerock.lang.cpp.syntax.namemap.internal.NameMap.t)
  (alias of bluerock.lang.cpp.syntax.namemap.internal.NameMap.t)

>>> Search bluerock.lang.cpp.syntax.namemap.
Toplevel input, characters 7-39:
> Search bluerock.lang.cpp.syntax.namemap.
>        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Error: The reference bluerock.lang.cpp.syntax.namemap was not found in the current environment.

## Assistant 5

I need to see the definition of the underlying map and its find function. In particular, the internal `NameMap`:

```coqquery
Print bluerock.lang.cpp.syntax.namemap.internal.NameMap.
```

## User 6

>>> Print bluerock.lang.cpp.syntax.namemap.internal.NameMap.
Module
internal.NameMap
:= Struct
     Module Compare
     Module Key
     Parameter eqL :
       ∀ a b : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Key.eq a b → a = b.
     Module E
     Module Raw
     Record bst (elt : Type) : Type := Bst
       { this : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t elt;
         is_bst : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.bst this }.
     Definition this :
       ∀ elt : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.bst elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t elt.
     Definition is_bst :
       ∀ (elt : Type) (b : bluerock.lang.cpp.syntax.namemap.internal.NameMap.bst elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.bst b.
     Definition t : Type → Type.
     Definition key : Type.
     Definition empty : ∀ elt : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt.
     Definition is_empty : ∀ elt : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Corelib.Init.Datatypes.bool.
     Definition add :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key
         → elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt.
     Definition remove :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt.
     Definition mem :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Corelib.Init.Datatypes.bool.
     Definition find :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Corelib.Init.Datatypes.option elt.
     Definition map :
       ∀ elt elt' : Type,
         (elt → elt') → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt'.
     Definition mapi :
       ∀ elt elt' : Type,
         (bluerock.lang.cpp.syntax.namemap.internal.NameMap.key → elt → elt')
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt'.
     Definition map2 :
       ∀ elt elt' elt'' : Type,
         (Corelib.Init.Datatypes.option elt → Corelib.Init.Datatypes.option elt' → Corelib.Init.Datatypes.option elt'')
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt
           → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt' → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt''.
     Definition elements :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt
         → Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt).
     Definition cardinal : ∀ elt : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Corelib.Init.Datatypes.nat.
     Definition fold :
       ∀ elt A : Type,
         (bluerock.lang.cpp.syntax.namemap.internal.NameMap.key → elt → A → A)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → A → A.
     Definition equal :
       ∀ elt : Type,
         (elt → elt → Corelib.Init.Datatypes.bool)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt
           → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Corelib.Init.Datatypes.bool.
     Definition MapsTo :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key → elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Prop.
     Definition In :
       ∀ elt : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.key → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Prop.
     Definition Empty : ∀ elt : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Prop.
     Definition eq_key :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt → Prop.
     Definition eq_key_elt :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt → Prop.
     Definition lt_key :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt → Prop.
     Parameter MapsTo_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
           x y
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e m.
     Parameter mem_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) x m
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.mem (elt:=elt) x m = Corelib.Init.Datatypes.true.
     Parameter mem_2 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.mem (elt:=elt) x m = Corelib.Init.Datatypes.true
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) x m.
     Parameter empty_1 :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Empty (elt:=elt) (bluerock.lang.cpp.syntax.namemap.internal.NameMap.empty elt).
     Parameter is_empty_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Empty (elt:=elt) m
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.is_empty (elt:=elt) m = Corelib.Init.Datatypes.true.
     Parameter is_empty_2 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.is_empty (elt:=elt) m = Corelib.Init.Datatypes.true
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.Empty (elt:=elt) m.
     Parameter add_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
           x y
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e (bluerock.lang.cpp.syntax.namemap.internal.NameMap.add x e m).
     Parameter add_2 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e e' : elt),
         ¬ (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
              bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
             x y
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e m
           → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e (bluerock.lang.cpp.syntax.namemap.internal.NameMap.add x e' m).
     Parameter add_3 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e e' : elt),
         ¬ (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
              bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
             x y
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e (bluerock.lang.cpp.syntax.namemap.internal.NameMap.add x e' m)
           → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e m.
     Parameter remove_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key),
         (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
           x y
         → ¬ bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) y
               (bluerock.lang.cpp.syntax.namemap.internal.NameMap.remove (elt:=elt) x m).
     Parameter remove_2 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         ¬ (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
              bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
             x y
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e m
           → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e
               (bluerock.lang.cpp.syntax.namemap.internal.NameMap.remove (elt:=elt) x m).
     Parameter remove_3 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x
                                                                                     y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.remove (elt:=elt) x m)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo y e m.
     Parameter find_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.find (elt:=elt) x m = Corelib.Init.Datatypes.Some e.
     Parameter find_2 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.find (elt:=elt) x m = Corelib.Init.Datatypes.Some e
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m.
     Parameter fold_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (A : Type) (i : A) (f : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key
                                                                                                            → elt → A → A),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.fold f m i =
         Stdlib.Lists.List.fold_left (λ (a : A) (p : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key * elt), f p.1 p.2 a)
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.elements (elt:=elt) m) i.
     Parameter elements_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m
         → Stdlib.Sorting.SetoidList.InA (bluerock.lang.cpp.syntax.namemap.internal.NameMap.eq_key_elt (elt:=elt)) (
             x, e) (bluerock.lang.cpp.syntax.namemap.internal.NameMap.elements (elt:=elt) m).
     Parameter elements_2 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt),
         Stdlib.Sorting.SetoidList.InA (bluerock.lang.cpp.syntax.namemap.internal.NameMap.eq_key_elt (elt:=elt)) (
           x, e) (bluerock.lang.cpp.syntax.namemap.internal.NameMap.elements (elt:=elt) m)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m.
     Parameter elements_3 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt),
         Stdlib.Sorting.Sorted.Sorted (bluerock.lang.cpp.syntax.namemap.internal.NameMap.lt_key (elt:=elt))
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.elements (elt:=elt) m).
     Parameter elements_3w :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt),
         Stdlib.Sorting.SetoidList.NoDupA (bluerock.lang.cpp.syntax.namemap.internal.NameMap.eq_key (elt:=elt))
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.elements (elt:=elt) m).
     Parameter cardinal_1 :
       ∀ (elt : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.cardinal (elt:=elt) m =
         stdpp.base.length (bluerock.lang.cpp.syntax.namemap.internal.NameMap.elements (elt:=elt) m).
     Definition Equal :
       ∀ elt : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Prop.
     Definition Equiv :
       ∀ elt : Type,
         (elt → elt → Prop)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Prop.
     Definition Equivb :
       ∀ elt : Type,
         (elt → elt → Corelib.Init.Datatypes.bool)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt → Prop.
     Parameter Equivb_Equivb :
       ∀ (elt : Type) (cmp : elt → elt → Corelib.Init.Datatypes.bool) (m m' : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Equivb cmp m m'
         ↔ bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.Proofs.Equivb cmp m m'.
     Parameter equal_1 :
       ∀ (elt : Type) (m m' : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (cmp : elt → elt → Corelib.Init.Datatypes.bool),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Equivb cmp m m'
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.equal cmp m m' = Corelib.Init.Datatypes.true.
     Parameter equal_2 :
       ∀ (elt : Type) (m m' : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (cmp : elt → elt → Corelib.Init.Datatypes.bool),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.equal cmp m m' = Corelib.Init.Datatypes.true
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.Equivb cmp m m'.
     Parameter map_1 :
       ∀ (elt elt' : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt) (f : elt → elt'),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x (f e) (bluerock.lang.cpp.syntax.namemap.internal.NameMap.map f m).
     Parameter map_2 :
       ∀ (elt elt' : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (f : elt → elt'),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt') x (bluerock.lang.cpp.syntax.namemap.internal.NameMap.map f m)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) x m.
     Parameter mapi_1 :
       ∀ (elt elt' : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (e : elt) (f : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key → elt → elt'),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x e m
         → ∃ y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
             (λ x0 y0 : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
                bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x0 y0 = Corelib.Init.Datatypes.Eq)
               y x
             ∧ bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo x (f y e)
                 (bluerock.lang.cpp.syntax.namemap.internal.NameMap.mapi f m).
     Parameter mapi_2 :
       ∀ (elt elt' : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (f : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key → elt → elt'),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt') x (bluerock.lang.cpp.syntax.namemap.internal.NameMap.mapi f m)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) x m.
     Parameter map2_1 :
       ∀ (elt elt' elt'' : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (m' : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t
                                                                                                       elt') (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (f : Corelib.Init.Datatypes.option elt → Corelib.Init.Datatypes.option elt' → Corelib.Init.Datatypes.option elt''),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) x m
         ∨ bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt') x m'
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.find (elt:=elt'') x
             (bluerock.lang.cpp.syntax.namemap.internal.NameMap.map2 f m m') =
           f (bluerock.lang.cpp.syntax.namemap.internal.NameMap.find (elt:=elt) x m)
             (bluerock.lang.cpp.syntax.namemap.internal.NameMap.find (elt:=elt') x m').
     Parameter map2_2 :
       ∀ (elt elt' elt'' : Type) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t elt) (m' : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t
                                                                                                       elt') (x : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) 
         (f : Corelib.Init.Datatypes.option elt → Corelib.Init.Datatypes.option elt' → Corelib.Init.Datatypes.option elt''),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt'') x (bluerock.lang.cpp.syntax.namemap.internal.NameMap.map2 f m m')
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt) x m
           ∨ bluerock.lang.cpp.syntax.namemap.internal.NameMap.In (elt:=elt') x m'.
     Definition raw_empty : ∀ A : Type, stdpp.base.Empty (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A).
     Definition raw_insert :
       ∀ A : Type,
         stdpp.base.Insert bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A).
     Definition raw_delete :
       ∀ A : Type,
         stdpp.base.Delete bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A).
     Definition raw_lookup :
       ∀ A : Type,
         stdpp.base.Lookup bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A).
     Definition raw_mapfold :
       ∀ A : Type,
         stdpp.fin_maps.MapFold bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A).
     Definition raw_singleton :
       ∀ A : Type,
         stdpp.base.SingletonM bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A).
     Definition raw_map : stdpp.base.FMap bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t.
     Definition raw_merge : stdpp.base.Merge bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t.
     Definition raw_omap : stdpp.base.OMap bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t.
     Definition map_empty : ∀ A : Type, stdpp.base.Empty (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_insert :
       ∀ A : Type,
         stdpp.base.Insert bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_delete :
       ∀ A : Type,
         stdpp.base.Delete bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_lookup :
       ∀ A : Type,
         stdpp.base.Lookup bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_mapfold :
       ∀ A : Type,
         stdpp.fin_maps.MapFold bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_singleton :
       ∀ A : Type,
         stdpp.base.SingletonM bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_partial_alter :
       ∀ A : Type,
         stdpp.base.PartialAlter bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t A
           (bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A).
     Definition map_map : stdpp.base.FMap bluerock.lang.cpp.syntax.namemap.internal.NameMap.t.
     Definition map_merge : stdpp.base.Merge bluerock.lang.cpp.syntax.namemap.internal.NameMap.t.
     Definition key_lt_dec :
       stdpp.base.RelDecision
         (λ x y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x y = Corelib.Init.Datatypes.Lt).
     Definition key_eq_dec :
       stdpp.base.RelDecision
         (λ x y : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t,
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.compare x y = Corelib.Init.Datatypes.Eq).
     Definition check_canon :
       ∀ A : Type,
         Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t
         → Corelib.Init.Datatypes.option bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t
           → bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A → Corelib.Init.Datatypes.bool.
     Parameter check_canonP :
       ∀ (A : Type) (t : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A) (min
                                                                                     max : Corelib.Init.Datatypes.option
                                                                                             bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.check_canon min max t
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.bst t
           ∧ match min with
             | Corelib.Init.Datatypes.Some bot => bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.gt_tree bot t
             | Corelib.Init.Datatypes.None => True
             end
             ∧ match max with
               | Corelib.Init.Datatypes.Some top => bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.lt_tree top t
               | Corelib.Init.Datatypes.None => True
               end.
     Parameter check_canon_ok :
       ∀ (A : Type) (t : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.check_canon Corelib.Init.Datatypes.None Corelib.Init.Datatypes.None t
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.bst t.
     Definition build :
       ∀ (A : Type) (t : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A),
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.check_canon Corelib.Init.Datatypes.None Corelib.Init.Datatypes.None t
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A.
     Definition from_raw_or :
       ∀ A : Type,
         bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A
         → (() → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A) → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A.
     Definition from_raw :
       ∀ A : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.Raw.t A → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A.
     Definition map_canon :
       ∀ A : Type, bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t A.
     Parameter map_to_list_elements :
       ∀ (A : Type) (k : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t) (v : A) (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t
                                                                                                     A),
         m !! k = Corelib.Init.Datatypes.Some v
         → ∃ xs ys : Corelib.Init.Datatypes.list (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t * A),
             stdpp.fin_maps.map_to_list m = (xs ++ (k, v) :: ys)%list.
     Definition find_any :
       ∀ T : Type,
         (bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t → T → Corelib.Init.Datatypes.bool)
         → bluerock.lang.cpp.syntax.namemap.internal.NameMap.t T → Corelib.Init.Datatypes.bool.
     Parameter find_any_ok :
       ∀ (T : Type) (b : bluerock.lang.cpp.syntax.namemap.internal.NameMap.Compare.t → T → Corelib.Init.Datatypes.bool) 
         (m : bluerock.lang.cpp.syntax.namemap.internal.NameMap.t T),
         if bluerock.lang.cpp.syntax.namemap.internal.NameMap.find_any b m
         then
          ∃ (k : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) (v : T),
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo k v m ∧ b k v = Corelib.Init.Datatypes.true
         else
          ∀ (k : bluerock.lang.cpp.syntax.namemap.internal.NameMap.key) (v : T),
            bluerock.lang.cpp.syntax.namemap.internal.NameMap.MapsTo k v m → b k v = Corelib.Init.Datatypes.false.
   End

## Assistant 6

Here is a direct definition of `find_struct` by looking up in the (abstract) type‐table and matching on the `Gstruct` case:

```gallina
Definition find_struct
  (tu : bluerock.lang.cpp.syntax.translation_unit.translation_unit)
  (nm : bluerock.lang.cpp.syntax.core.name)
  : option bluerock.lang.cpp.syntax.decl.Struct :=
  match bluerock.lang.cpp.syntax.namemap.internal.NameMap.find
          (elt := bluerock.lang.cpp.syntax.translation_unit.GlobDecl)
          nm (bluerock.lang.cpp.syntax.translation_unit.types tu) with
  | Some (bluerock.lang.cpp.syntax.translation_unit.Gstruct s) => Some s
  | _ => None
  end.
```

