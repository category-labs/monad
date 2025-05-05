Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Import linearity.
Disable Notation atomic_name'.




Fixpoint listsum (l: list nat) : nat :=
  match l with
  | [] => 0
  | h::tl => h + listsum tl
  end.

(*
Module bad.
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
  *)  
Inductive Tree (T:Type) : Type :=
| node : T -> list (Tree T) (* children *) -> Tree T
| empty : Tree T.

Arguments node {_} _ _. (* make the T argument implicit *)
Arguments empty {_}.


Fixpoint sum (t: Tree nat) : nat :=
  match t with
  | empty => 0
  | node nodeVal children => nodeVal + list_sum (List.map sum children)
  end.

Section foo.
  Variables (nodeVal : nat) (children: list (Tree nat)).
  Goal sum (node nodeVal children) = 0.
    simpl. unfold map. simpl.
  
Module foo.
Fixpoint sum (t: Tree nat) : nat :=
  match t with
  | empty => 0
  | node nodeVal children => nodeVal + list_sum (List.map sum (List.rev children))
  end.
End foo.
Print Nat.divmod.

Print Nat.sub.
Fixpoint div (x y: nat) {struct x} : nat :=
  match y with
  | 0 => 0
  | S y => 1+ div (x - S y) y
  end.

Fixpoint divmod (x y q u : nat) {struct x} : nat * nat :=
  match x with
  | 0 => (q, u)
  | S x' => match u with
            | 0 => divmod x' y (S q) y
            | S u' => divmod x' y q u'
            end
  end.

Fixpoint add (n m : nat) {struct n} : nat :=
  match n with
  | 0 => m
  | S p => S (add p m)
  end.
Print Nat.gcd.                                                    
Fixpoint gcd (n m: nat) : nat :=
  match n with
  | 0 => m
  | S p => gcd (m `mod` (S p)) n
  end.
Section foo.
  Context (m p: nat).
  Eval simpl in (gcd (S p) m).
(* Error: Cannot guess decreasing argument of fix. *)    

Fixpoint sum (t: Tree nat) : nat :=
  match t with
  | empty => 0
  | node nodeVal children => nodeVal + list_sum (List.map sum children)
  end.
    
Module Fail.
  Axiom map: forall {A B:Type}, (A-> B) -> list A -> list B.
  Fixpoint sum (t: Tree nat) : nat :=
    match t with
    | empty => 0
    | node nodeVal children => nodeVal + list_sum (map sum children)
    end.

  

