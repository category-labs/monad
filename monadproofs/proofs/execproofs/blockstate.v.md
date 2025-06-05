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
Write a gallina function `lookup_function` that takes a `translation_unit` and an argumement `nm: name` and returns an `option _` which is a definition of the function/method whose fully qualified name is `nm`. Chose an appropriate type for the placeholder `_`.
Note that the AST treats classes as structs as well.

## Results of some relevant queries
>>> Print translation_unit.
Record translation_unit : Type := Build_translation_unit
  { symbols : symbol_table;
    types : type_table;
    initializer : InitializerBlock;
    byte_order : endian }.

translation_unit has primitive projections with eta conversion.
Arguments Build_translation_unit symbols types initializer byte_order
Arguments symbols t
Arguments types t
Arguments initializer t
Arguments byte_order t

>>> Print name.
Notation name := name'

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
  | Emember_call : bool
                   → MethodRef_ name type Expr
                     → Expr → list Expr → Expr
  | Eoperator_call : OverloadableOperator
                     → operator_impl.t name type → list Expr → Expr
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
  | Enew : name * type
           → list Expr
             → new_form → type → option Expr → option Expr → Expr
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
  | Sasm : string
           → bool
             → list (ident * Expr)
               → list (ident * Expr) → list ident → Stmt
  | Slabeled : ident → Stmt → Stmt
  | Sgoto : ident → Stmt
  | Sunsupported : string → Stmt
  with VarDecl' : Set :=
    Dvar : localname → type → option Expr → VarDecl
  | Ddecompose : Expr → ident → list BindingDecl → VarDecl
  | Dinit : bool → name → type → option Expr → VarDecl
  with BindingDecl' : Set :=
    Bvar : localname → type → Expr → BindingDecl
  | Bbind : localname → type → Expr → BindingDecl
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
Arguments Tresult_member_call on%_cpp_name_scope 
  _%_cpp_type_scope _%_list_scope
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
Arguments Eunresolved_member_call on%_cpp_name_scope
  _%_CPP_expr_scope _%_list_scope
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
Arguments Emember arrow%_bool_scope obj%_CPP_expr_scope 
  f mut%_bool_scope t%_cpp_type_scope
Arguments Emember_ignore arrow%_bool_scope (obj res)%_CPP_expr_scope
Arguments Emember_call arrow%_bool_scope method 
  obj%_CPP_expr_scope args%_list_scope
Arguments Eoperator_call _ _ _%_list_scope
Arguments Esubscript (e1 e2)%_CPP_expr_scope t%_cpp_type_scope
Arguments Esizeof _ t%_cpp_type_scope
Arguments Ealignof _ t%_cpp_type_scope
Arguments Eoffsetof gn%_cpp_type_scope _%_pstring_scope
  t%_cpp_type_scope
Arguments Econstructor on%_cpp_name_scope args%_list_scope
  t%_cpp_type_scope
Arguments Elambda _%_cpp_name_scope captures%_list_scope
Arguments Eimplicit e%_CPP_expr_scope
Arguments Eimplicit_init t%_cpp_type_scope
Arguments Eif (e1 e2 e3)%_CPP_expr_scope t%_cpp_type_scope
Arguments Eif2 n%_N_scope (common cond thn els)%_CPP_expr_scope
  _%_cpp_type_scope
Arguments Ethis t%_cpp_type_scope
Arguments Einitlist args%_list_scope default t%_cpp_type_scope
Arguments Einitlist_union _ _ t%_cpp_type_scope
Arguments Enew new_fn new_args%_list_scope pass_align
  alloc_ty%_cpp_type_scope array_size init
Arguments Edelete is_array%_bool_scope del_fn%_cpp_name_scope
  arg%_CPP_expr_scope deleted_type%_cpp_type_scope
Arguments Eandclean e%_CPP_expr_scope
Arguments Ematerialize_temp e%_CPP_expr_scope vc
Arguments Eatomic op%_pstring_scope args%_list_scope
  t%_cpp_type_scope
Arguments Estmt _%_CPP_stmt_scope _%_cpp_type_scope
Arguments Eva_arg e%_CPP_expr_scope t%_cpp_type_scope
Arguments Epseudo_destructor is_arrow%_bool_scope 
  t%_cpp_type_scope e%_CPP_expr_scope
Arguments Earrayloop_init oname%_N_scope src%_CPP_expr_scope
  (level length)%_N_scope init%_CPP_expr_scope 
  t%_cpp_type_scope
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
Arguments Sasm _%_pstring_scope volatile%_bool_scope
  (inputs outputs clobbers)%_list_scope
Arguments Slabeled _%_pstring_scope _%_CPP_stmt_scope
Arguments Sgoto _%_pstring_scope
Arguments Sunsupported _%_pstring_scope
Arguments Dvar name%_pstring_scope _%_cpp_type_scope init
Arguments Ddecompose _%_CPP_expr_scope anon_var%_pstring_scope
  _%_list_scope
Arguments Dinit thread_safe%_bool_scope name%_cpp_name_scope
  _%_cpp_type_scope init
Arguments Bvar name%_pstring_scope _%_cpp_type_scope
  init%_CPP_expr_scope
Arguments Bbind name%_pstring_scope _%_cpp_type_scope
  init%_CPP_expr_scope
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

# Contents of the current file

```coq
Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.block_state_cpp. (* this defines module: translation_unit, the  AST of block_state.cpp (and all its transitive includes). block_state_cpp.v is autogenerated by cpp2v *)
Require Import monad.proofs.exec_specs.
Disable Notation atomic_name'.
Require Import Lens.Elpi.Elpi.
#[local] Open Scope lens_scope.
Require Import monad.proofs.libspecs.



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

Before proceeding, we need to inspect the definition of `symbol_table` to understand how functions are stored and how to look them up by `name`.  Let's query for the definition of `symbol_table` and its main lookup operation.  

```coqquery
Locate symbol_table.
Print symbol_table.
Search symbol_table.
```

## User 2

>>> Locate symbol_table.
Constant bluerock.lang.cpp.syntax.translation_unit.symbol_table

>>> Print symbol_table.
symbol_table = NM.t ObjValue
     : Type

>>> Search symbol_table.
sym_table_le: symbol_table → symbol_table → Prop
sym_table_le_alt: symbol_table → symbol_table → Prop
symbols: translation_unit → symbol_table
complete_translation_unit: type_table → symbol_table → Prop
complete_symbol_table: type_table → symbol_table → Prop
PreOrder_instance_5: PreOrder sym_table_le
PreOrder_instance_4: PreOrder sym_table_le_alt
sym_table_le_dec: ∀ a b : symbol_table, Decision (sym_table_le a b)
Build_translation_unit:
  symbol_table
  → type_table → InitializerBlock → endian → translation_unit
sym_table_le_equiv:
  ∀ te1 te2 : symbol_table,
    sym_table_le te1 te2 ↔ sym_table_le_alt te1 te2
denoteModule_denoteSymbol:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (n : obj_name) (m : translation_unit) (o : ObjValue),
    symbols m !! n = Some o → denoteModule m ⊢ denoteSymbol m n o
denoteModule_valid:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (n : obj_name) (m : translation_unit),
    symbols m !! n ≠ None → denoteModule m ⊢ valid_ptr (_global n)
global_valid_ptr:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (m : translation_unit) (nm : obj_name),
    ssrbool.isSome (symbols m !! nm) =[Vm?]=> true
    → denoteModule m ⊢ valid_ptr (_global nm)
denoteModule_strict_valid:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (n : obj_name) (m : translation_unit),
    is_strict_valid <$> symbols m !! n = Some true
    → denoteModule m ⊢ strict_valid_ptr (_global n)
wp_gvar_B:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (m : translation_unit) (nm : obj_name) (ty : type) 
    (ρ : region) (Q : ptr → FreeTemps → mpredI),
    ssrbool.isSome (symbols m !! nm) =[Vm?]=> true
    → Bwd (::wpL ρ (Eglobal nm ty))
wp.check_global_function_ok:
  ∀ (tu : translation_unit) (nm : name) (ty : type),
    wp.check_global_function tu nm ty = true
    → ∃ (obj : ObjValue) (f : function_type_ type),
        symbols tu !! nm = Some obj
        ∧ (∀ (a : type) (b : global_init.t), obj ≠ Ovar a b)
          ∧ type_of_value obj = Tfunction f ∧ type_of_value obj = ty
wp_gvar:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (m : translation_unit) (nm : obj_name) (ty : type) 
    (ρ : region) (Q : ptr → FreeTemps → mpredI),
    ssrbool.isSome (symbols m !! nm) =[Vm?]=> true
    → Q (_global nm) 1%free ⊢ ::wpL ρ (Eglobal nm ty)
global_valid_ptr_C:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (m : translation_unit) (nm : obj_name),
    ssrbool.isSome (symbols m !! nm) =[Vm?]=> true
    → CancelX MatchNormal [denoteModule m] [tele] CoverAny
        [valid_ptr (_global nm)]
new_delete.check_alloc_call_ok:
  ∀ {σ : genv} (tu : translation_unit) [pass_align : bool] 
    [aty : type] [fty : TM.Compare.t * type] 
    [es : list Expr] [ct : type] [targs : list decltype *
                                          function_arity] 
    [sz al : N] [implicits : list Expr] [throws : bool],
    tu ⊧ σ
    → new_delete.check_alloc_call tu pass_align aty fty es =
      Some (ct, targs, sz, al, implicits, throws)
      → size_of σ aty = Some sz
        ∧ align_of aty = Some al
          ∧ implicits = new_implicits pass_align sz al
            ∧ ct = normalize_type fty.2
              ∧ args_for <$> as_function ct = Some targs
                ∧ ft_return <$> as_function ct =
                  Some "void*"%cpp_type
                  ∧ can_throw <$> symbols tu !! fty.1 =
                    Some
                      (if throws
                       then exception_spec.MayThrow
                       else exception_spec.NoThrow)
wp_operand_new:
  ∀ {thread_info : biIndex} {_Σ : gFunctors} 
    {Σ : cpp_logic thread_info _Σ} {σ : genv} 
    (ρ : region) (tu : translation_unit) (oinit : option Expr) 
    (new_fn : obj_name * type) (pass_align : bool) 
    (new_args : list Expr) (aty : type) (Q : 
                                         val → FreeTemps → mpredI) 
    (targs : list decltype * function_arity),
    let nfty := normalize_type new_fn.2 in
    args_for <$> as_function nfty = Some targs
    → ∀ alloc_sz alloc_al : N,
        size_of σ aty = Some alloc_sz
        → align_of aty = Some alloc_al
          → (let implicit_args :=
               new_implicits pass_align alloc_sz alloc_al in
             (::wpArgs ρ) (implicit_args ++ new_args)
               (λ (_ vs : list ptr) (ifree free : FreeTemps),
                  ▷ wp_fptr (types tu) nfty (_global new_fn.1) vs
                      (λ res : ptr,
                         interp tu ifree
                           (operand_receive "void*" res
                              (λ storage_val : val,
                                 ∃ storage_ptr : ptr,
                                   [| storage_val = Vptr storage_ptr |] ∗
                                   (if
                                     bool_decide
                                       (storage_ptr = nullptr)
                                    then
                                     [| can_throw <$>
                                        symbols tu !! new_fn.1 =
                                        Some exception_spec.NoThrow |] ∗
                                    Q (Vptr storage_ptr) free
                                    else
                                     storage_ptr
                                     |-> alignedR
                                           (if pass_align
                                            then alloc_al
                                            else
                                            STDCPP_DEFAULT_NEW_ALIGNMENT) ∗
                                    storage_ptr
                                    |-> blockR alloc_sz 1$m ∗
                                    ∀ obj_ptr : ptr,
                                      provides_storage storage_ptr
                                        obj_ptr aty -∗
                                      wp_opt_initialize ρ tu oinit
                                        aty obj_ptr
                                        (λ free' : FreeTemps,
                                           obj_ptr
                                           |-> 
                                           new_token.R 1
                                            {|
                                            new_token.alloc_ty := aty;
                                            new_token.storage_ptr :=
                                            storage_ptr;
                                            new_token.overhead := 0
                                            |} -∗
                                           Q (Vptr obj_ptr)
                                            (free' >*> free)%free)))))))
            ⊢ ::wpOperand
                ρ
                (Enew new_fn new_args
                   (new_form.Allocating pass_align) aty None oinit)

 Remember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.


## Assistant 2

I need to see what `ObjValue` contains (in particular, where function‐values live), and what lookup notation `symbols m !! n` uses.  Let's query:

```coqquery
Locate ObjValue.
Print ObjValue.
```

## User 3

>>> Locate ObjValue.
Notation bluerock.lang.cpp.syntax.translation_unit.ObjValue

>>> Print ObjValue.
Notation ObjValue := ObjValue'

Variant ObjValue' : Set :=
    Ovar : type → global_init.t → ObjValue
  | Ofunction : Func → ObjValue
  | Omethod : Method → ObjValue
  | Oconstructor : Ctor → ObjValue
  | Odestructor : Dtor → ObjValue.

Arguments Ovar _%_cpp_type_scope _

 Remember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.


## Assistant 3

We need to see what `obj_name` is (the key into the `symbol_table`), and confirm it is definitional or a synonym of `name`.  

```coqquery
Locate obj_name.
Print obj_name.
```

## User 4

>>> Locate obj_name.
Notation bluerock.lang.cpp.syntax.core.obj_name

>>> Print obj_name.
Notation obj_name := obj_name'

obj_name' = name
     : Set

 Remember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.


## Assistant 4

To determine what to return, let’s inspect the definitions of `Func` and `Method`.  

```coqquery
Locate Func.
Print Func'.
Locate Method.
Print Method'.
```

## User 5

>>> Locate Func.
Notation bluerock.lang.cpp.syntax.decl.Func
Constructor bluerock.lang.cpp.syntax.preliminary.operator_impl.Func
  (shorter name to refer to it in current context is operator_impl.Func)

>>> Print Func'.
Record Func' : Set := Build_Func
  { f_return : type;
    f_params : list (ident * type);
    f_cc : calling_conv;
    f_arity : function_arity;
    f_exception : exception_spec.t;
    f_body : option FunctionBody }.

Arguments Build_Func f_return%_cpp_type_scope 
  f_params%_list_scope f_cc f_arity f_exception 
  f_body
Arguments f_return f
Arguments f_params f
Arguments f_cc f
Arguments f_arity f
Arguments f_exception f
Arguments f_body f

>>> Locate Method.
Notation bluerock.lang.cpp.syntax.decl.Method

>>> Print Method'.
Record Method' : Set := Build_Method
  { m_return : type;
    m_class : name;
    m_this_qual : type_qualifiers;
    m_params : list (ident * type);
    m_cc : calling_conv;
    m_arity : function_arity;
    m_exception : exception_spec.t;
    m_body : option (OrDefault Stmt) }.

Arguments Build_Method m_return%_cpp_type_scope
  m_class%_cpp_name_scope m_this_qual%_cpp_type_scope
  m_params%_list_scope m_cc m_arity m_exception 
  m_body
Arguments m_return m
Arguments m_class m
Arguments m_this_qual m
Arguments m_params m
Arguments m_cc m
Arguments m_arity m
Arguments m_exception m
Arguments m_body m

 Remember: If your solution has holes or has temporary oversimplifications, YOU MUST MARK THOSE PLACES WITH the (* TOFIXLATER *) comment.


## Assistant 5

I’ll return either a `Func` or a `Method` in a Coq `sum`.  No essential implementation holes remain.

```gallina
Definition lookup_function
           (tu : translation_unit) (nm : name)
  : option (sum Func Method) :=
  match symbols tu !! nm with
  | Some (Ofunction f) => Some (inl f)
  | Some (Omethod m)   => Some (inr m)
  | _                  => None
  end.
```

