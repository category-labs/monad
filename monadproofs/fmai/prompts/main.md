This is a task about proving correctness of a C++ function in a separation logic we have setup in Coq for reasoning about C++ programs. This includes Coq definitions of C++ syntax and an axiomatic weakest precondition semantics.

# Separtion Logic
First, some details about the separation logic.
You already know about Prop, the type of logical propositions in Coq.
For example. True -> False, True /\ False, forall n:nat, n=n, exists n:nat, n=n are propositions in Coq of type Prop.

Assertions in separation logic can also talk about the state of the world and assert ownership.
In Coq, we have defined the type `mpred` of separation logic assertions.
given `a:N`, the separation logic assertion `a_addr |-> primR Tu32 (cQp.mut 1) (Vint a)`
asserts that `a_addr` is a pointer (abstract memory location) which stores a primitive value (`primR`) `Vint a` of the primitive type  Tu32 which stands for unsigned 32 bit integer.
The argument `cQp.mut 1` of type `cQp.t` signifies the ownership fraction and constness.
`cQp.mut` signifies that the location is mutable (not marked as `const` in C++).
The 1:Qp in `cQp.mut 1` says that the `a_addr |-> primR Tu32 (cQp.mut 1) (Vint a)` has complete (fraction 1) ownership of the location. So nobody else can be reading/writing that location concurrently. `Qp` is a type of positive rational numbers in Coq. Unlike in other programming languages, in Coq, the type `Q` (rational numbers), just like the type `Z` (integers), has infinite precision: there are no rounding errors.

In `(Vint a)`, `Vint` has type  `Z->val`
val is the type of values stored at C++ "pointers" (abstract memory locations):

```coq
  Inductive val : Set :=
  | Vint (_ : Z)
  | Vchar (_ : N)
    (* ^ value used for non-integral character types, e.g.
         [char], [wchar], etc, but *not* [unsigned char] and [signed char]

         The values here are *always* unsigned. When arithmetic is performed
         the semantics will convert the unsigned value into the appropriate
         equivalent on the target platform based on the signedness of the type.
     *)
  | Vptr (_ : ptr)
  | Vraw (_ : raw_byte)
  | Vundef
  .
```


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
It is similar to implication (A->B) in classical logic. In addition, it also says that the ownership footprint of B is included in the ownership footprint of A. Here are some examples of valid entailments:
```coq
a_addr |-> primR Tu32 (cQp.mut 1) (Vint 1) |-- Exists a, a_addr |-> primR Tu32 (cQp.mut 1) (Vint a)
a_addr |-> primR Tu32 (cQp.mut 1) (Vint 1) |-- a_addr |-> primR Tu32 (cQp.mut (1/2)) (Vint 1)
P ** Q |-- P
```
In contrast, `a_addr |-> primR Tu32 (cQp.mut 1) (Vint 1) |-- a_addr |-> primR Tu32 (cQp.mut (1/2)) (Vint 2)`
does not hold and we can in fact prove
`(a_addr |-> primR Tu32 (cQp.mut 1) (Vint 1) |-- a_addr |-> primR Tu32 (cQp.mut (1/2)) (Vint 2)) -> False.`


## Rep Predicates
Now lets look at some interesting examples using `**`.
Recall that given `a:N`, the separation logic assertion `a_addr |-> primR Tu32 (cQp.mut 1) (Vint a)`
asserts that `a_addr` is a pointer (abstract memory location) which stores a primitive value (`primR`) `Vint a` of the primitive type Tu32 which stands for unsigned 32 bit integer.
Lets dig a little deeper into this `|->` infix notation. It is an overloaded notation used in 2 similar cases:
when the left side is an absolute memory location, or when the left side is a relative offset, e.g. a field offset in a struct or the offset of the nth item in an array.
The right side of `|->` is something of type `Rep`, which is similar to `mpred` except that the ownership/assertions are relative to a base address. The example above was for primitive types. The Reps for composite types look slightly more complex.

As an example, consider the following struct:

```c++
struct Point {
    int x;
    int y;
};
```

Analogous to `primR` for primitive types, we can define `PointR` to represent how an object of type `Point` is layed out in memory:

```coq
  Definition PointR (q: cQp.t) (x y: Z): Rep :=
    structR `::Point` q
    _field `::Point::x` |-> primR Ti32 q (Vint x)
      ** _field `::Point::y` |-> primR Ti32 q (Vint y).
```
You can ignore the first conjunct `structR ``::Node`` q` for now. It is just some standard boilerplate telling the logic that the object has type `Point`.
The above definition says that at the offset of the field `x` of `struct Point`, a
primitive value (`primR`) the value `Vint x` of the primitive type Ti32 (signed 32 bit integer) is stored.
To avoid ambiguity, when we refer to C++ names in Coq, we use fully qualified names: `::Point::x` not `x`.
The next clause (separated by `**`) asserts the same for the field `y`.

Because C++ guarantees that the memory locations of the fields `x` and `y` of `struct Point` are disjoint, it is sensible to combine the two conjuncts in the definition of `PointR` using `**`.
Using `PointR` we can write the postcondition of the command block below as `p |-> PointR 1 0 0`:

```c++
Point p;
p.x=0;
p.y=0;
```

`PointR` is called a representation predicate. The second and third arguments of `PointR`, `x:Z` and `y:Z` are considered the model arguments of `PointR`. They represent in Coq the data that is stored in a `Point` object.
To be more systematic, we could have equivalently defined `PointR` as follows, where the model arguments are bundled up into 1, just like in C++:
```coq
  Definition PointR' (q: cQp.t) (xy: Z*Z): Rep :=
    structR `::Point` q
    _field `::Point::x` |-> primR Ti32 q (fst x)
      ** _field `::Point::y` |-> primR Ti32 q (snd y).
```
This form makes it clearer that for the C++ `Point` struct, the model type in Coq is `Z*Z`.
However, we often use the curried form (`PointR`) instead.


Now, as a more complex example, let us look at separation logic assertions about memory storing linked lists. Here is the struct definition:

```c++
struct Node {
    Node(Node *next, int data) : next_(next), data_(data) {}

    Node *next_;
    int data_;
};

typedef Node *List;

```
The type `Node` is similar in that it has 2 fields (names are different). The main difference is that type of the `next_` field is a pointer and not an integer.
Similar to `PointR`, we can define `NodeR` as follows:

```coq
  Definition NodeR (q: cQp.t) (data: Z) (nextPtr: ptr): Rep :=
    structR ``::Node`` q
    ** _field `::Node::data_` |-> primR Ti32                       (cQp.mut q) (Vint data)
    ** _field `::Node::next_` |-> primR (Tptr (Tnamed `::Node`)) (cQp.mut q) (Vptr nextPtr).
```
In Coq, we have abstractly defined `ptr` as the type of abstract memory locations in C++.
Above, the clause for the field `next_` looks similar the the cause for `data_`.
Instead of `Vint` we use `Vptr`.
As shown above (definition of Coq Inductive type `val`), `Vptr` injects a `ptr` into the `val` type.
Also the type argument (1st argument) of `primR` is different.
The type `Node` in C++ is represented as (Tnamed `::Node`) in Coq
and the type `Node *` in C++ is represented as `(Tptr (Tnamed `::Node`))` in Coq.
Now that we already introduces the `ptr` type in Coq, we can note that
The type `Rep` is morally equivalent to `ptr->mpred`: given `p:ptr` and `R:Rep`,
we can obtain the `mpred` `p|->R` which should be thought of morally as `R p`.
(`Rep` is actually a subset of the type `ptr->mpred`: it only includes functions that compute equivalen `mpred`s on equivalent `ptr`s.)


Now we can define `ListR`, the Coq representation predicate of linked lists in C++ (`typedef Node *List;`)

```coq
  Fixpoint ListR (q : cQp.t) (l : list Z) : Rep :=
    match l with
    | [] => nullR
    | hd :: tl => Exists (p : ptr), NodeR q hd p ** pureR (p |-> ListR q tl)
    end.
```
Above, we picked the Coq type `list Z` is the model type of C++ linked lists as defined by `typedef Node *List;`.
`ListR` defines how a Coq list is represented in memory.
The `nil` (`[]`) branch of the match says `nullR`. The main thing to know about `nullR` is that for any `p:ptr`
`p|->nullR` implies `p=nullptr`. More formally, `Forall (p:ptr), p|->nullR |-- [| p=nullptr|]`
Thus, that first branch of the match says that an empty list is represented by `nullptr`.
The second branch (`cons`) case is more interesting:
if some memory location represents a Coq list `hd::tl` then that location must store a `struct Node`
whose data field is `hd` and the pointer field is some `p` such that the rest of the list (`tl`) is
stored at `p`. `pureR` has type `mpred->Rep`. `pureR` can be morally thought of
`fun (P:mpred) (_:ptr) => P`.
Intuitively, the sublist (`tl`) can be stored at a location that is completely unrelated to the outer list (`hd::tl`).

`ListR` can be used in writing specifications (correctness theorems) of linked list functions. For example, consider the following 2 C++ functions:

```c++
List reverse(List cur) {
  List prev = nullptr;
  List next = nullptr;
  while (cur != nullptr) {
    next = cur->next_;
    cur->next_ = prev;
    prev = cur;
    cur = next;
  }
  return prev;
}

unsigned long length(List l) {
  unsigned long i = 0;
  while (l != nullptr) {
    i++;
    l = l->next_;
  }
  return i;
}
```
The precondition of the `reverse` function is (for any `l:list Z`):
```coq
ListR 1 l
```

and the postcondition is
```coq
ListR 1 (List.rev l)
```

A precondition and postcondition of the `length` function is
```coq
ListR q l
```
for any `q: cQp.t` and `l:list Z`. The other postcondition of the `length` function is
that the return value is equal to `Vint (Z.of_nat (length l))`.
Because the length function on reads the list and does not change any of the nodes that are a
part of the list, any fractional ownership `q` works. This allows read-only concurrency.
We can use the following lemma to split ownership and pass it to different threads who can each read the linked list without modifying it.
```coq
Lemma fractional_listR (q1 q2: Qp):
ListR (cQp.mut (q1+q2)) l -|- ListR (cQp.mut q1) l ** ListR (cQp.mut q2) l
```
Note that `A -|- B := A |-- B /\ B |-- A`
Before modifying a list, all fractions have to be combined to `cQp.mut 1` using the `<-` direction
of the lemma `fractional_listR`.


Below, we will see how to formally write these function specifications (pre and postconditions)
as theorems in Coq.


# C++ Semantics

## Syntax
Now lets discuss our machinery to reason about C++ programs in the above separation logic.
We have the cpp2v framework to convert abstract syntax tress of C++ programs to Coq (Gallina).
For example, consider the following gcd program in C++:
```c++
#define uint unsigned int

uint
gcd(uint a, uint b) {
    while (b != 0) {
        uint temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}
```

Its AST converted by our cpp2v tool to Coq is:
```coq
    (Dfunction  "_Z3gcdjj"
      (Build_Func Tuint
        (("a", Tuint) :: ("b", Tuint) :: nil) CC_C Ar_Definite
        (Some (Impl
            (Sseq (
                (Swhile None
                  (Ebinop Bneq
                    (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint)
                    (Ecast Cintegral (Eint 0%Z Tint) Prvalue Tuint) Tbool)
                  (Sseq (
                      (Sdecl (
                          (Dvar "temp" Tuint
                            (Some
                              (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint))) :: nil)) ::
                      (Sexpr
                        (Eassign (Evar "b" Tuint)
                          (Ebinop Bmod
                            (Ecast Cl2r (Evar "a" Tuint) Prvalue Tuint)
                            (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint) Tuint) Tuint)) ::
                      (Sexpr
                        (Eassign (Evar "a" Tuint)
                          (Ecast Cl2r (Evar "temp" Tuint) Prvalue Tuint) Tuint)) :: nil))) ::
                (Sreturn_val
                  (Ecast Cl2r (Evar "a" Tuint) Prvalue Tuint)) :: nil)))))) :: nil) Little.
```
In particular, the body of the function is the following subterm:
```coq
(Sseq (
	(Swhile None
	  (Ebinop Bneq
		(Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint)
		(Ecast Cintegral (Eint 0%Z Tint) Prvalue Tuint) Tbool)
	  (Sseq (
		  (Sdecl (
			  (Dvar "temp" Tuint
				(Some
				  (Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint))) :: nil)) ::
		  (Sexpr
			(Eassign (Evar "b" Tuint)
			  (Ebinop Bmod
				(Ecast Cl2r (Evar "a" Tuint) Prvalue Tuint)
				(Ecast Cl2r (Evar "b" Tuint) Prvalue Tuint) Tuint) Tuint)) ::
		  (Sexpr
			(Eassign (Evar "a" Tuint)
			  (Ecast Cl2r (Evar "temp" Tuint) Prvalue Tuint) Tuint)) :: nil))) ::
	(Sreturn_val
	  (Ecast Cl2r (Evar "a" Tuint) Prvalue Tuint)) :: nil))
```

To help understand the above AST in Coq, here is the type of C++ statements in Coq:

```coq
Inductive Stmt' {obj_name type Expr : Set} : Set :=
| Sseq    (_ : list Stmt')
| Sdecl   (_ : list (VarDecl' obj_name type Expr))

| Sif     (_ : option (VarDecl' obj_name type Expr)) (_ : Expr) (_ _ : Stmt')
| Swhile  (_ : option (VarDecl' obj_name type Expr)) (_ : Expr) (_ : Stmt')
| Sfor    (_ : option Stmt') (_ : option Expr) (_ : option Expr) (_ : Stmt')
| Sdo     (_ : Stmt') (_ : Expr)

| Sswitch (_ : option (VarDecl' obj_name type Expr)) (_ : Expr) (_ : Stmt')
| Scase   (_ : SwitchBranch)
| Sdefault

| Sbreak
| Scontinue

| Sreturn (_ : option Expr)

| Sexpr   (_ : Expr)

| Sattr (_ : list ident) (_ : Stmt')

| Sasm (_ : bs) (volatile : bool)
       (inputs : list (ident * Expr))
       (outputs : list (ident * Expr))
       (clobbers : list ident)

| Slabeled (_ : ident) (_ : Stmt')
| Sgoto (_ : ident)
```

For example, a sequence of statements separated by ; in C++ is constructed by Sseq constructor above.
Its argument is the list of statements. `Swhile` represents the while commad. Its second command
is the boolean expression determining whether the while loop should continue. The third argument
is the body of the loop. The first argument captures the variables that are declared in

## Semantics

We also have a separation logic to reason about C++ programs.
We have defined axiomatic weakest precondition semantics for all C++ commands and operations.
Given a postcondition `Q` in separation logic, `::wpS ρ c Q` denotes the weakest precondition
so that the command `c` can execute successfully and produce the postcondition `Q`.
The usual spec "Hoare triple" P{c}Q in textbooks can be defined uding ``::wpS` as `P |-- ::wpS ρ c Q`.
(we are in a richer setting of separation logic, which can reason about ownership, unlike separation logic.)
ρ is the environment, which is a function mapping local variables to "pointers" (asbstract memory addresses, not actual numbers). For example, the environment we get while reasoning about the body of the above C++ gcd function is:
`[region: "b" @ b_addr; "a" @ a_addr; return {?: Tu32}]`.
It says that the local  variable named "b" is at the location b_addr. It will typically be a location on the stack but that is an implementation detail of the compiler and we abstract over such details in our logic.
Similarly, `"a" @ a_addr` says that the local  variable named "a" is at the location a_addr.

The postcondition Q is actually of type `Kpred`, not `mpred` because Q can make assertions specific to
the way the command `c` finished, e.g. by returning a value, a C++ `break`, a C++ `continue`, or returning nothing. Morally, `Kpred` can be understood as the function type `ReturnType -> mpred`, where:
```coq
Inductive ReturnType : Set :=
| Normal
| Break
| Continue
| ReturnVal (_ : ptr)
| ReturnVoid
.
```
In the case the function returns some value, even a primitive/scalar value like int32, the `ReturnType`
of that case is represented as `ReturnVal p` where p is the location where the returned value is temporarily
stored before being passed to the caller.
(P is an abstract pointer which typicall is the register EAX, but that is an implementation detail of the compiler).

Kpred  is not exactly `ReturnType -> mpred` because it also stores proofs that the function respects
some properties: for example, on equivalent return values, the output mpreds should be equivalent.
We have a handy definition `Kreturn` for cases where the command (could be a list of commands using `Kseq`)
must return a value:

```coq
  Definition Kreturn `{Σ : cpp_logic, σ : genv} (Q : ptr -> mpred) : Kpred :=
  KP $ funI rt =>
  match rt with
  | Normal | ReturnVoid => Forall p : ptr, p |-> primR Tvoid (cQp.mut 1) Vvoid -* Q p
  | ReturnVal p => Q p
  | _ => False
  end.
```

For example, if a C++ function `int foo()` returns `2`, its postcondition should be
`Kreturn (fun v : ptr, v |-> primR Tu32 (cQp.mut 1) (Vint 2))`

Note that `Kreturn` takes only one explicit argument `Q`.


## Function Correctness Statements (specs)
Now, lets look at some correctness statements (specs) of some functions.
For the C++ GCD function above, the correctness statement is:

```coq
Theorem gcd_correct:
  forall (a_addr b_addr : ptr) (a b : Z),
  0 ≤ a ≤ 2 ^ 32 - 1 ->
  0 ≤ b ≤ 2 ^ 32 - 1 ->
  (□ denoteModule module ** □ type_ptr Tu32 a_addr ** □ type_ptr Tu32 b_addr) **
  a_addr |-> primR Tu32 (cQp.mut 1) (Vint a) ** b_addr |-> primR Tu32 (cQp.mut 1) (Vint b)
|-- ::wpS
      [region: "b" @ b_addr; "a" @ a_addr; return {?: Tu32}]
	  gcd_body
      (Kreturn
         (fun v : ptr =>
          (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
          (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0) ** v |-> primR Tu32 (cQp.mut 1) (Vint (Z.gcd a b))))
```

Here, `gcd_body` is the function body of GCD:
```coq
  Definition gcd_body : Stmt :=  Sseq
    [Swhile None
       (Ebinop Bneq (Ecast Cl2r (Evar "b" Tu32) Prvalue Tu32) (Ecast Cintegral (Eint 0 Ti32) Prvalue Tu32) Tbool)
       (Sseq
          [Sdecl [Dvar "temp" Tu32 (Some (Ecast Cl2r (Evar "b" Tu32) Prvalue Tu32))];
           Sexpr
             (Eassign (Evar "b" Tu32)
                (Ebinop Bmod (Ecast Cl2r (Evar "a" Tu32) Prvalue Tu32) (Ecast Cl2r (Evar "b" Tu32) Prvalue Tu32)
                   Tu32) Tu32); Sexpr (Eassign (Evar "a" Tu32) (Ecast Cl2r (Evar "temp" Tu32) Prvalue Tu32) Tu32)]);
     Sreturn (Some (Ecast Cl2r (Evar "a" Tu32) Prvalue Tu32))].

```

# Proof state format

Below you will be asked to help forulate in Coq the next step in correctness proofs of C++ functions. You be able to see goal state at that point.
For example, consider the goal at the point:
```coq
Lemma xxx: forall x:Z, x = 1 -> x+x=2.
Proof.
  intros.
``
Coq (e.g. coqtop) displays it as:

```coq
  x : Z
  H : x = 1
  ============================
  x + x = 2
```
We will show this goal as:

```coq
<pure_hypotheses>
H : (x = 1)
x : Z
</pure_hypotheses>
<pure_goal>
(x + x = 2)
</pure_goal>
```
The adjective pure highlights that these items are of type `Prop` and are not separation logic assertions.
The pure_goal in C++ function correctness proofs are typically separation logic entailments of the form: `A1 ** A2 ** A3 ** A4 ... An |-- B`.
For example, consider the theorem `gcd_correct` shown above. After `intros`, the goal in in the proof of that looks:

```coq
<pure_hypotheses>
x3 : (0 ≤ x1 ≤ 2 ^ 32 - 1)
x2 : (0 ≤ x0 ≤ 2 ^ 32 - 1)
x1 : Z
x0 : Z
x : ptr
a_addr : ptr
</pure_hypotheses>
<pure_goal>
  (□ denoteModule module ** □ type_ptr Tu32 a_addr ** □ type_ptr Tu32 b_addr) **
  a_addr |-> primR Tu32 (cQp.mut 1) (Vint a) ** b_addr |-> primR Tu32 (cQp.mut 1) (Vint b)
|-- ::wpS
      [region: "b" @ b_addr; "a" @ a_addr; return {?: Tu32}]
	  gcd_body
      (Kreturn
         (fun v : ptr =>
          (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
          (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0) ** v |-> primR Tu32 (cQp.mut 1) (Vint (Z.gcd a b))))
</pure_goal>
```

In such goals, the pure goal can become huge and it may become hard to parse the LHS of `|--`.
So, inspired by iris IPM, we further split the pure_goal into spatial hypotheses (items separated by `**` in the LHS of `|--`)
and spatial goal (RHS of `|--`).
More precisely, suppose the pure_goal is  `A1 ** A2 ** A3 ** A4 ... An |-- B`.
We call `B` the spatial goal.
We call each `Ai` a spatial hypothesis and print each Ai in a separate line.
Just for ease of reference, ee also give names to each spatial hypothesis but these have no significance in Coq: e.g., unlike pure hypotheses, these names cannot appear in the goal.
Also, we omit/modify arguments to "::wpS".
Instead of `::wpS env codeAst post`, we write `weakest_pre prettyPrintedCodeAst post`.
`prettyPrintedCodeAst` will be a C++ like pretty printing of the codeAst (of Inductive type `Stmt`).
We drop the `env` argument and instead maintain a convention that any variable `v` is mapped to location `v_addr`.
This was already true for the environments we saw above, e.g. `[region: "b" @ b_addr; "a" @ a_addr; return {?: Tu32}]`.

With the above simplifications, goal above will be printed more readably as:

```coq
<pure_hypotheses>
POST : (ptr -> mpred)
a_addr : ptr
b_addr : ptr
a : Z
b : Z
_ : (0 ≤ a ≤ 2 ^ 32 - 1)
_ : (0 ≤ b ≤ 2 ^ 32 - 1)
</pure_hypotheses>
<spatial_hypotheses>
s1 : (type_ptr Tu32 b_addr)
s2 : (type_ptr Tu32 a_addr)
s3 : (denoteModule module)
s4 : (b_addr |-> primR Tu32 (cQp.mut 1) (Vint b))
s5 : (a_addr |-> primR Tu32 (cQp.mut 1) (Vint a))
</spatial_hypotheses>
<spatial_goal>
weakest_pre
  {
    while ((b) != (0))
      {
        unsigned int temp = (b);
        b = (a) % (b);
        a = (temp);
      }
    return (a);
  }
(Kreturn
   (fun v : ptr =>
    (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
    (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0) **
    v |-> primR Tu32 (cQp.mut 1) (Vint (Z.gcd a b))))
</spatial_goal>
```

In the beginning of a proof spatial and pure hypotheses denote the precondition of the function. These typically include the ownership of the arguments and pure assumptions about the values stored there.



# Loop invariant example
A main challenge in proving correctness of non-concurrent C++ code is finding loop invariants.
Lets us use the gcd example to illustrate that.
Just before entering the loop during in the `weakest_pre` reasoning, the goal looks like:
```coq
<pure_hypotheses>
POST : (ptr -> mpred)
a_addr : ptr
b_addr : ptr
a : Z
b : Z
_ : (0 ≤ a ≤ 2 ^ 32 - 1)
_ : (0 ≤ b ≤ 2 ^ 32 - 1)
</pure_hypotheses>
<spatial_hypotheses>
s1 : (type_ptr Tu32 b_addr)
s2 : (type_ptr Tu32 a_addr)
s3 : (denoteModule module)
s4 : (b_addr |-> primR Tu32 (cQp.mut 1) (Vint b))
s5 : (a_addr |-> primR Tu32 (cQp.mut 1) (Vint a))
</spatial_hypotheses>
<spatial_goal>
weakest_pre
  {
    while ((b) != (0))
      {
        unsigned int temp = (b);
        b = (a) % (b);
        a = (temp);
      }
    return (a);
  }
(Kreturn
   (fun v : ptr =>
    (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
    (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0) **
    v |-> primR Tu32 (cQp.mut 1) (Vint (Z.gcd a b))))
</spatial_goal>
```
Currently, the spatial hypotheses denote the resources and what was true just before entering the loop.
Typically, to prove a loop, one has to generalize the hypotheses so that they hold at
the beginning of *all* subsequent iterations of the loop.
The generalized set of hypotheses is called the loop invariant.

Note that it also important that the loop invariant is strong enough to prove the function postcondition
when the loop terminates.
If this loop is at the end of the function, the loop invariant should imply the postcondition.
In this case, the postcondition is:
```coq
(Kreturn
   (fun v : ptr =>
    (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
    (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0) **
    v |-> primR Tu32 (cQp.mut 1) (Vint (Z.gcd a b))))
```
Some conjuncts in the postcondition just require returning back the ownership of location storing the function call arguments and stack-allocated variables declared before the loop. This prevents the function from storing this ownership in some data-structure that lives beyond this function call.
The values stored at those locations are existentially quantified (using `Exist`) and unconstrained.
In these cases, there are 2 such conjuncts, respectively for the function arguments `a` and `b`:
```
    (Exists v0 : val, a_addr |-> primR Tu32 (cQp.mut 1) v0) **
    (Exists v0 : val, b_addr |-> primR Tu32 (cQp.mut 1) v0)
```
The loop invariant we need to provide in a proof in Coq must be a separation logic assertion of type `mpred`.
As mentioned before, it should represent the spatial and pure hypotheses that hold at the beginning of *every* iteration of the loop. If the loop invariant has multiple hypotheses, you can combine them by `**`.
Also, recall that pure hypotheses `P:Prop` can be represented as mpred as `[| P |]`.
If some spatial or pure hypothesis does not change during the loop execution, we do not need to mention it in the loop invariant. It would be automatically included.

We typically need to use existential quantification (using `Exist`) to allow the variables to change their values from their initial values at the beginning of the loop.
But then we  must add constraints about the existentially quantified new values to ensure that when the loop terminates, the postcondition is satisified.

It is helpful to look at the code and see what variables are being updated in the loop body. Here, we can ignore
the variables that are declared in the loop body, e.g. `temp`.
```c++
    while ((b) != (0))
      {
        unsigned int temp = (b);
        b = (a) % (b);
        a = (temp);
      }
    return (a);
```
Looking at the loop body, it is clear that the loop updates the variables `a` and `b`.
Using the naming environment (first argument of `::wpS`) convention mentioned above, we know that
the `a` corresponds to the memory location `a_addr` and b to `b_addr`.
Looking in the spatial hypotheses for hypotheses of the form `a_addr |-> ..` and `b_addr |-> `, we find:
```coq
s4 : (b_addr |-> primR Tu32 (cQp.mut 1) (Vint b))
s5 : (a_addr |-> primR Tu32 (cQp.mut 1) (Vint a))
```
Because these variables are changing in the loop, the `val` stored at their addresses (last argument of `primR`) must be generalized over. Even though the values are being changed in the loop body, the value remains an integer (e.g. does not become a `Vptr`).
So an appropriate generalization is
```coq
Exists a' : Z, Exists b' : Z,
 a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
 b_addr |-> primR Tu32 (cQp.mut 1) (Vint b')
```
This is a loop invariant as it certainly holds at the beginning of each iteration.
But it is too weak to prove the postcondition when the loop exits.
We need to think about how to strenghthen it.
A usual step is to look at the pure hypotheses about the old values of the generalized variables and see if the pure
hypothesis holds for the new values as well. In this case, we generalize over `a:Z` and `b:Z`.
There were 2 pure hypotheses about them:
```coq
_ : (0 ≤ a ≤ 2 ^ 32 - 1)
_ : (0 ≤ b ≤ 2 ^ 32 - 1)
```
These properties are preserved when the C++ variables `a` and `b` are updated: `a` gets the old value of `b` which was in range.
`b` gets `a mod b` which is also in the range due to properties of `mod`.
So we carry them over to the existentially
quantified values in the candidate loop invariant to get a stronger candidate loop invariant
```coq
Exists a' : Z, Exists b' : Z,
 a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
 b_addr |-> primR Tu32 (cQp.mut 1) (Vint b') **
 [| 0 <= a' <= 2 ^ 32 - 1 |] ** [| 0 <= b' <= 2 ^ 32 - 1 |]
```
Is this enough? It says nothing that would allow us to say that when the loop terminates (and then the function returns `a`), `a` is the `gcd` of the original inputs to the function. We know that `b` is 0 when the loop terminates.
We know that `gcd a 0=a`.
So when the loop terminates, we need to show that the `gcd` of the values of `a` and `b` at that time is the same as that of the original values. A reasonable guess therefore is that the loop body ensures that the `gcd` of the new values of `a` and `b` are the same as that of the original input, giving us the final loop invariant:

```coq
Exists a' : Z, Exists b' : Z,
 [| 0 <= a' <= 2 ^ 32 - 1 |] ** [| 0 <= b' <= 2 ^ 32 - 1 |] **
 a_addr |-> primR Tu32 (cQp.mut 1) (Vint a') **
 b_addr |-> primR Tu32 (cQp.mut 1) (Vint b') **
 [| Z.gcd a' b' = Z.gcd a b |]
```
Using this loop invariant, I was able to finish the proof using the sketch above.
The main challenge was to prove that the loop body preserves the loop invariant,
which followed from the following Coq lemmas:

```coq
Z.gcd_mod : ∀ a b : Z, b ≠ 0 → Z.gcd (a `mod` b) b = Z.gcd b a
Z.gcd_0_r_nonneg : ∀ a : Z, 0 ≤ a → Z.gcd a 0 = a
```

# Proof script format

You will the background above to tell me the next step in a correctness proof of a C++ function.
Below, you will be presented with a heavily documented proof script in which you have to tell me the next step.
The proof script follows some rules to make it easy to understand.
Read the comments in the proof script carefully as they explain how the proof state evolves.
At the beginning of each proof sentence, exactly one goal is focused.
If a goal splits the current goal into multiple subgoals, we immediately focus the first goal with `{`.
Each `{` is followed by a comment documenting the tree address of its subgoal.
A tree address is a list of pairs. [] denotes the root of the proof: when the goal was not split.
If `tad` is a tree address of a subgoal, and that subgoal was further split into `n` subgoals, the tree addresses
of those resultant subgoals would be `(0,n)::tad`,  `(1,n)::tad` ... `(n-1,n)::tad`.
Here is an illustrating goal splitting and tree address:

```coq
Lemma example (x:Z) (p: x=1): (x=1 /\ x=x) /\ (x+x=2 /\ x*x=1).
Proof.
  split.
  {(*(0,2)::[]*)
    split.
    {(*(0,2)::(0,2)::[]*)
      subst.
      lia.
    }
    {(*(1,2)::(0,2)::[]*)
      subst.
      lia.
    }
  }
  {(*(1,2)::[]*)
    split.
    {(*(0,2)::(1,2)::[]*)
      subst.
      lia.
    }
    {(*(1,2)::(1,2)::[]*)
      subst.
      lia.
    }
  }
Qed.
```
## Tactics
The proof script uses some tactics not in Coq standard library.
The main one is `slauto` which is a tactic which can:
- simplify weakest precodition expressions in a syntax directed way based on the C++ AST
- perform separation logic reasoning, e.g. cancelling resources on the left and right side of `|--`
- introduce `Forall` in the RHS of `|--` and destruct `Exists` in the LHS.
- instantiate `Exists (v:_), ...` in RHS if it can compute an instantiation that is guaranteed to not make the goal unprovable.


# Current proof task.
Below is a proof script included in a ```coq ``` code block. You need to help me with the next step which would happen exactly where the unfinished proof script ends.
After the proof script, I will show you the proof state at the end of the unfinished proof script and some guidelines about what the next step could/must look like.
