# General Background
This is a Coq programming task. First, some general guidelines about Coq programming tasks.

## Admitting holes (defer less critical/important parts)
Complex Coq programs are often written in multiple steps. 
Coq allows us to "admit" helper functions temporarily so that they can be defined later.
However, in that case, you need to come up with the type of the helper function. 
For example, you admit a helper function to convert a Z to a String.string, as follows"

```coq
Definition Ztostring (z: Z) : String.string. Admitted. (* TODO: FILL IN LATER *)
```
This mechanism allows you to get the higher-level details right before implementing the low-level obvious details.
Do not forget the "TODO: FILL IN LATER" comment, as this will be used to find the holes to fill in later. Also ensure there is just 1 space after `Admitted.` and before the comment as above.

## Error Messages
You are talking to an automated bot that will process your responses. If the Coq program you emit has errors, this bot will respond with the errors emitted by Coq.
Here are some general tips to avoid errors:
1) Use qualified names to avoid conflicts
2) Do not make any assumptions about the open notation scopes. For example, if you mean `Z.add 1 2`, write `(1+2)%Z` instead.

## Coq Vernacular Queries instead of Hallucinations
If you are not sure about the exact name of a definition/fixpoint/inductive in the standard library or the libraries availble to you can issue Coq queries to get more information about the available context. Some of the widely used queries are Search/About/Check/Locate. Here are some examples of search:

Search (nat -> nat). (* search the library for items of type nat -> nat *)

Search (nat -> list ?a -> list ?a). (* unification variables can be used to constrain occurrences: e.g. here the 2 occurrences of ?a must match the same term *)

About Nat.add (* show documentation for an item *)

Check (Nat.add 1 1). (* check type of a term *)

Locate nat. (* print the possible fully qualified name(s) of `nat`. unless the user defined their own `nat` type, this will print `Corelib.Init.Datatypes.nat` . this will print multiple items if there are several items whose fully qualified names have `nat` as the leaf, e.g. `A.nat`, `Corelib.Init.Datatypes.nat`. It would also print shorter names for each fully qualified name. The shorter name depends on the set and order of Imports in the current file. When writing Coq code, you should refer to the located item by a name not any shorter than the shorter name mentioned here: the longer the better as that is robust to moving code around where the order of imports are different. *)

Use the queries judiciously. Be very careful with `Search`: it can return too many items unless you chose a fairly discriminative query to rule out what you dont want.

Queries other than `Locate` need enough references to definitions/inductives to be sufficiently qualified depending on the set of `Import`s. For example, you may need to say `A.foo` instead of just `foo` if you havent `Import`ed A. You can can use `Locate` to figure out the missing qualifications. No query allows you to search by substrings of leaf names. For example, there is no way to search by `na` to find `nat`.

## Mutual Inductives
If you want do define a function that recurses on inductive data, you typically use the `Fixpoint` keyword. If the inductive type is mutually indutive with other types, often the needed recursion is also mutually recursive. In such cases, you need to define your function using mutual Fixpoints. Below is an exampe:

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

## Common mistakes

In Coq, string escaping works wierdly. 
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
