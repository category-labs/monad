 (*specs/proofs of /root/fv-workspace/monad/proofs/demo2.cpp *)

Require Import monad.tutorials.demo2.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.proofs.misc.
Require Import monad.tutorials.demomisc.
Require Import monad.tutorials.atomic_specs.
Require Import monad.tutorials.demoprf.
From AAC_tactics Require Import AAC.
From AAC_tactics Require Import Instances.
Import Instances.Z.
Import cQp_compat.
Import Verbose.
Import linearity.

Section with_Sigma.
  Context `{Sigma:cpp_logic}  {CU: genv}.
  Context  {MODd : demo2.module ⊧ CU}.

(*
Hint Resolve learn_atomic_val : br_opacity.
*)  
  Open Scope Z_scope.
  Set Nested Proofs Allowed.

  (**  *Arrays
    _global "x" |-> primR "int" q 5
   *)
  Definition gcdl_spec_core : WpSpec mpredI val val :=
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)}
             numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "length" (Vint (length l))
      \post [Vint (fold_left Z.gcd l 0)] emp.
  (* [c45,49] *)
  
  Example arrayR3 (p:ptr) (n1 n2 n3: Z) (q: Qp):
    p |-> arrayR uint (fun i:Z => primR uint q i) [n1;n2;n3]
      -|- ( valid_ptr (p .[ uint ! 3 ])
              ** p |-> primR uint q n1
              ** p .[ uint ! 1 ] |-> primR uint q n2
              ** p .[ uint ! 2 ] |-> primR uint q n3).
  Proof.
    repeat rewrite arrayR_cons.
    repeat rewrite arrayR_nil.
    iSplit; go;
    repeat rewrite o_sub_sub;
    closed.norm closed.numeric_types; go.
  Qed.

  Example fold_left_gcd (n1 n2 n3: Z) :
    fold_left Z.gcd [n1;n2;n3] 0 =  Z.gcd (Z.gcd (Z.gcd 0 n1) n2) n3.
  Proof. reflexivity. Qed.
  
    
  cpp.spec "gcdl(unsigned int*, unsigned int)" as gcdl_spec with (gcdl_spec_core).

  (** * 2+ ways to split an arrays

   +---+---+---+---+---+---+
   | q | q | q | q | q | q |
   +---+---+---+---+---+---+

  +---+---+---+---+---+---+       +---+---+---+---+---+---+
   |q/2|q/2|q/2|q/2|q/2|q/2|      |q/2|q/2|q/2|q/2|q/2|q/2|
   +---+---+---+---+---+---+      +---+---+---+---+---+---+

   *)
  Lemma fractionalSplitArrayR (numsp:ptr) (l: list Z) (q:Qp):
    numsp |-> arrayR uint (fun i:Z => primR uint q i) l |--
      numsp |-> arrayR uint (fun i:Z => primR uint (q/2) i) l
      ** numsp |-> arrayR uint (fun i:Z => primR uint (q/2) i) l.
  Proof.
    rewrite -> cfractional_split_half with (R := fun q => arrayR uint (fun i:Z => primR uint q i) l);
      [| exact _].
    rewrite _at_sep.
    f_equiv; f_equiv; f_equiv;
      simpl; rewrite cqpp2; auto.
  Qed.

  (** subarray partitioning: when threads concurrently read/write to disjoint segments.
     demonstrated in next example, which also illustrates the power of commutativity
   +---+---+---+---+---+---+
   | q | q | q | q | q | q |
   +---+---+---+---+---+---+


   +---+---+---+                   +---+---+---+
   | q | q | q |                    | q | q | q |
   +---+---+---+                    +---+---+---+

   *)
  Lemma arrayR_split {T} ty (base:ptr) (i:nat) xs (R: T-> Rep):
    (i <= length xs)%nat ->
       base |-> arrayR ty R xs
         |-- base |-> arrayR ty R (firstn i xs)
             ** base .[ ty ! i ] |-> arrayR ty R (skipn i xs).
  Proof.
    intros.
    rewrite arrayR_split; eauto. go. 
  Qed.

  (* [c204,218; c436,436] same spec, faster impl*)
  cpp.spec "parallel_gcdl(unsigned int*, unsigned int)"
    as parallel_gcdl_spec with (gcdl_spec_core).
  
  Hint Rewrite @fold_left_app: syntactic.
  Existing Instance UNSAFE_read_prim_cancel.
  
  
      Compute (Z.quot (-5) 4).
      Compute (Z.div (-5) 4).
      Set Default Goal Selector "!".
  cpp.spec (Nscoped 
              "parallel_gcdl(unsigned int*, unsigned int)::@0" Ndtor)  as lam2destr  inline.

  Lemma pgcdl_proof: denoteModule module
                       ** (thread_class_specs "parallel_gcdl(unsigned int*, unsigned int)::@0")
                       ** gcd_spec
                       ** gcdl_spec
                       |-- parallel_gcdl_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    name_locals.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. go.
    rename a into lam.
    aggregateRepPieces lam.
    go.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l/ 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    nat2ZNLdup.
    name_locals.
    progress closed.norm closed.numeric_types.
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia;
      go... (* array ownership spit into 2 pieces. [g1335,1409] [g1433,1443] [g1433,1443; g1497,1515],
             [g1556,1563],  [g1556,1563; g1335,1409] [g1556,1563; g1335,1409; g1294,1330; c335,342] *)
    revertAdrs constr:([numsp; resultl_addr]);
      repeat rewrite bi.wand_curry;
      intantiateWand.
    (*
    iExists (resultl_addr |-> uninitR "unsigned int" 1%Qp **
               numsp |-> arrayR "unsigned int" (λ i : Z, primR "unsigned int" q i) (firstn (length l / 2) l))
     *)
    instWithPEvar taskPost.
    go.
    iSplitL "".
    { verify_spec'.
      go.
      iExists _. eagerUnifyU.
      autorewrite with syntactic. go.
      erefl.
    }
    unhideAllFromWork.
    autorewrite with syntactic. go. 
    iExists _. eagerUnifyU. 
    autorewrite with syntactic. go.
    wapply @arrayR_combinep. eagerUnifyU.
    autorewrite with syntactic. go... (* lemma below*)
    (* [g1766,1844] [g1766,1844; g1910,1927]  *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split_gcd.
    auto.
  Qed.
  
  (** o:=Z.gcd
((((((i o a1) o a2) o a3) o a4) o a5) o a6)

(((i o a1) o a2 ) o a3 )        (((i o a4) o a5 ) o a6 )
                    \               /
                      \           /
                   left_result   right_result
                          \       /
                            \   /
                        (left_result o right_result)
*)

  Lemma fold_split_gcd  (l: list Z) (pl: forall a, In a l -> 0 <= a)
       (ls: nat):
    Z.gcd
      (fold_left Z.gcd (firstn ls l) 0)
      (fold_left Z.gcd (skipn ls l) 0)
   = fold_left Z.gcd l 0.
  Proof using. symmetry. apply misc.fold_split_gcd; auto. Qed.

  (** Quiz [c680,698] *)

  #[ignore_errors]
  cpp.spec "fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)" as fold_left_spec with (
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \arg{fptr} "f" (Vptr fptr)
      \arg{initv} "init" (Vint initv)
      \pre{fm: Z->Z->Z} fptr |->
          cpp_specR (tFunction "unsigned int" ["unsigned int"%cpp_type; "unsigned int"%cpp_type])
            (
              \arg{av:Z} "a" (Vint av)
                \arg{bv:Z} "b" (Vint bv)
                \post [Vint (fm av bv)] emp
            )
      \post [Vint (fold_left fm l initv)] emp).

  #[ignore_errors]
  cpp.spec "parallel_fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)" as par_fold_left_spec with (
      \arg{numsp:ptr} "nums" (Vptr numsp)
      \prepost{(l: list Z) (q:Qp)} numsp |-> arrayR uint (fun i:Z => primR uint q i) l
      \arg "size" (Vint (length l))
      \arg{fptr} "f" (Vptr fptr)
      \pre{fm: Z->Z->Z} fptr |->
          cpp_specR (tFunction "unsigned int" ["unsigned int"%cpp_type; "unsigned int"%cpp_type])
            (
              \arg{av:Z} "a" (Vint av)
                \arg{bv:Z} "b" (Vint bv)
                \post [Vint (fm av bv)] emp
            )
      \pre [| Associative (=) fm |]
      \arg{initv} "init" (Vint initv)
      \pre [| LeftId (=) initv fm |]
      \pre [| RightId (=) initv fm |]
      \post [Vint (fold_left fm l initv)] emp).
  
  Lemma fold_split {A:Type} (f: A->A->A)(asoc: Associative (=) f)
    (id: A) (lid: LeftId (=) id f) (rid: RightId (=) id f) (l: list A) (lSplitSize: nat):
    fold_left f l id =
      f (fold_left f (firstn lSplitSize l) id)
        (fold_left f (skipn  lSplitSize l) id).
  Proof.
    rewrite <- (take_drop lSplitSize) at 1.
    rewrite fold_left_app.
    rewrite fold_id2.
    aac_reflexivity.
  Qed.
  (* generality: dont need to prove again and again, for each f  *)

  (* Rep vs mpred *)
  (** Structs: Node [c1032,1036] *)

  Example addOffset (p: ptr) (o: offset) : ptr := p ,, o.
  Example array2Offset : offset := (.["int" ! 2]).
  Example fieldOffset : offset := _field "Node::data_".
  
  Definition NodeR  (q: cQp.t) (data: Z) (nextLoc: ptr): Rep :=
    _field "Node::data_" |-> primR "int" q (Vint data)
    ** _field "Node::next_" |-> primR "Node*" q (Vptr nextLoc)
    ** structR "Node" q.

  Definition NodeRf  (q: cQp.t) (data: Z) (nextLoc: ptr) : ptr -> mpred :=
    fun (nodebase: ptr) =>
    (* nodebase.data_ *)  
    nodebase,, _field "Node::data_" |-> primR "int" q (Vint data)
    ** nodebase,, _field "Node::next_" |-> primR "Node*" q (Vptr nextLoc)
    ** nodebase |-> structR "Node" q.

  cpp.spec "incdata(Node *)"  as incd_spec with (
     \arg{np} "n" (Vptr np)
     \pre{data nextLoc} NodeRf 1 data nextLoc np (* shorthand. unfold in prf *)
     \pre [| data < 2^31 -1 |]
     \post NodeRf 1 (1+data) nextLoc np
      ).

  cpp.spec "incdata(Node *)"  as incd_spec_idiomatic with (
      \arg{np} "n" (Vptr np)
      (* _global "x" |-> primR "int" 1 45 *)
     \pre{data nextLoc} np |-> NodeR 1 data nextLoc
     \pre [| data < 2^31 -1 |]
     \post np |-> NodeR 1 (1+data) nextLoc
      ).

  Lemma eqv (data:Z) (nextLoc:ptr) (nodebase:ptr) q :
    nodebase |-> NodeR q data nextLoc
    -|- NodeRf q data nextLoc nodebase.
  Proof. unfold NodeR, NodeRf. iSplit; go. Qed.
  
  Lemma incd_proof: denoteModule module |-- incd_spec.
  Proof using MODd. verify_spec. unfold NodeRf. slauto. Qed.
  
  (** Structs: LinkedList *)

  Fixpoint ListR (q : cQp.t) (l : list Z) : Rep :=
    match l with
    | [] => nullR
    | hd :: tl =>
        Exists (tlLoc: ptr),
          NodeR q hd tlLoc
          ** pureR (tlLoc |-> ListR q tl)
    end.

  Example listRUnfold (q:Qp) (head:ptr): head |-> ListR q [4;5;6] |--
    Exists node5loc node6loc,
       head |-> NodeR q 4 node5loc
       ** node5loc |-> NodeR q 5 node6loc
       ** node6loc |-> NodeR q 6 nullptr
       (* ** [| node5loc <> node6loc <> head|] *).
  Proof using. work. unfold NodeR.  go. Qed.

  Example nullReq (p: ptr): p |-> nullR |-- [| p = nullptr |].
  Proof. go. Qed.

  cpp.spec "reverse(Node*)" as reverse_spec with
    (\arg{lp} "l" (Vptr lp)
     \pre{l: list Z} lp |-> ListR 1 l
     \post{r}[Vptr r] r |-> ListR 1 (List.rev l)).

  (** why trust [List.rev] *)
  Search List.rev.
  Check rev_app_distr.

  Definition sort (l:list Z) : list Z. Proof. Admitted.
  
  cpp.spec "sort(Node*)" as sort_spec with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r] r |-> ListR 1 (sort l)).

  Fixpoint sorted (l: list Z) : Prop :=
    match l with
    | [] => True
    | h::tl => sorted tl /\ forall t, t ∈ tl -> h <= t 
    end.
  
  cpp.spec "sort(Node*)" as sort_spec2 with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r]
        Exists ls, r |-> ListR 1 ls ** [| sorted ls |]).
  
  (**  extensional spec
     - simpler than writing a 
     - the postcondition is too weak. why? *)






















  cpp.spec "sort(Node*)" as sort_spec3 with
    (\arg{lp} "l" (Vptr lp)
     \pre{l} lp |-> ListR 1 l
     \post{r}[Vptr r] Exists ls, r |-> ListR (1) ls ** [| sorted ls /\ l ≡ₚ ls|]).



  (** 
last session::
- pass assertions to a new thread when starting it
- get back its postcondition at t.join()

  ┌──────────────────────────┐
  │  Parent owns P:mpred     │
  └──────────────────────────┘
           |
           | Split resources:  P -|- Pₖ ** C
           v
  ┌──────────────┬──────────────┐
  │ Pₖ (Parent)  │  C (Child)   │
  └──────────────┴──────────────┘
           |                |
           |     <-?->      |
     Parent Thread       Child Thread (new)
         runs with Pₖ        runs with C
  ┌──────────────┬──────────────┐
  │ Pₖ' (Parent) │  C'(Child)   │ child done executing
  └──────────────┴──────────────┘
           |                |
Parent: Child.join 
  ┌──────────────────────────┐
  │ Parent owns Pk' ** C'    │
  └──────────────────────────┘


- not enough [c2989,2989]
*)








  
(** *cinv : concurrent invariants *)
  

  Notation cinvr invId q R:=
        (as_Rep (fun this:ptr => cinv invId q (this |-> R))).

  (*
  Definition cinvr (invId: gname) (q:Qp) (R:Rep) :Rep  :=
    as_Rep (fun this:ptr => cinv invId q (this |-> R)).
   *)
  
Example boxedResource (P:mpred) (invId: gname): mpred := cinv invId 1 P.
  
Lemma splitInv (P:mpred) (invId: gname) (q:Qp):
  cinv invId q P |-- cinv invId (q/2) P ** cinv invId (q/2) P.
Proof using.
  apply splitcinvq.
Qed.
Lemma splitInv2  (invId: gname) (q:Qp):
  let P := _global "x" |-> primR "int" 1 5 in
  cinv invId q P |-- cinv invId (q/2) P ** cinv invId (q/2) P.
Proof.   apply splitcinvq. Qed.

  cpp.spec "bar()" as bar_spec with (
      \prepost{q invId} cinv q invId (_global "z" |-> anyR "int" 1)
      \post emp
    ).
  
  Lemma bar_prf : denoteModule module |-- bar_spec.
  Proof with (fold cQpc).
    verify_spec.
    go... (* [g262,284] [g262,284; g195,218] *)
  Abort.

  Opaque coPset_difference.
  Opaque atomicR.
    
  Ltac slauto := (slautot ltac:(autorewrite with syntactic; try solveRefereceTo)); try iPureIntro.
    
  (*[c3638,3665] *)
  cpp.spec "setU(int)" as setU_spec with (
    \prepost{q invId} cinv q invId (∃ uv:Z, _global "u" |-> atomicR "int" 1 uv)
    \arg{uvnew} "value" (Vint uvnew)
    \post emp). 

  cpp.spec "setThenGetU(int)" as setGetU_spec_wrong with (
      \prepost{q invId} cinv q invId (∃ uv:Z, _global "u" |-> atomicR "int" 1 uv)
      \arg{uvnew} "value" (Vint uvnew)
      \post [Vint uvnew] emp
        ).
  (** [c4032,4043] why is the above spec unprovable? *)
  
  Lemma setGetU_prf:
    denoteModule module
      ** int_store_spec
      ** int_load_spec
    |-- setGetU_spec_wrong.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec... (* [g340,371] [g551,558] *)
    slauto.
    repeat (iExists _); callAtomicCommit.
    repeat openCinvq.
    removeLater... (* [g590,627] cinv gone*)
    work.
    rename uv into uvcur... (* [g671,676]*)
    
    work using fwd_later_exist, fwd_later_sep;
      repeat removeLater;
      iApply fupd_mask_intro;[set_solver |];
      iIntrosDestructs... (* [g749,780; g642,675] [g749,751; g671,676] *)
    Existing Instance learn_atomic_val.
    go... (* w post [g704,709; c4067,4072] [g749,755]  must close*)
    closeCinvqs... (* [g676,708] [g673,711; g613,651] [g613,652; g539,573] [g539,573]*)
    work... (* lost that and got [g534,582] [g546,548; g580,582], [c4067,4072] *)
    iModIntro.
    Existing Instance learn_atomic_val_UNSAFE.
    go.
    repeat (iExists _); callAtomicCommit.
    repeat openCinvq.
    removeLater... (* [c4098,4104] [g664,666; g698,700]*)
    go.
    iApply fupd_mask_intro;[set_solver |];
      iIntrosDestructs.
    go.
    go...
    closeCinvqs.
    go.
    iModIntro.
    go.
  Abort.

  (* correct: spec: *)
  cpp.spec "setThenGetU(int)" as setGetU_spec with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv)
      \arg{uv} "value" (Vint uv)
      \post{any:Z} [Vint any] emp
      ).

  Lemma setGetU_prf: denoteModule module ** int_store_spec  ** int_load_spec |-- setGetU_spec.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go... go.
    closeCinvqs.
    go.
    iModIntro.
    go.
    callAtomicCommitCinv.
    go... go.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.

cpp.spec "setThenGetU(int)" as setGetU_spec2 with (
   \prepost{q invId}
     cinv q invId
       (∃ uv:Z, _global "u" |-> atomicR "int" 1 uv
                ** [| isPrime uv |])
   \arg{uvnew:Z} "uvnew" (Vint uvnew)
   \post{any:Z} [Vint any] emp
      ).
  (** why is the above spec unprovable (for the code) *)

  
  Lemma setGetU_prf_prime: denoteModule module ** int_store_spec  ** int_load_spec |-- setGetU_spec2.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto.
    callAtomicCommitCinv.
    go... go.
    rename a into uvBeforeWrite.
    (* close inv at the end of u.exchange *)
    closeCinvqs... (* [g651,653 ; g604,609] [g651,653 ; g604,609; g690,701] *)
    go. 
  Abort.
  
  cpp.spec "setThenGetU(int)" as setGetU_spec_prime with (
      \prepost{q invId} cinv q invId (∃ zv:Z, _global "u" |-> atomicR "int" 1 zv ** [| isPrime zv |])
      \arg{uvnew} "uvnew" (Vint uvnew)
      \pre [| isPrime uvnew |] 
      \post{any:Z} [Vint any (* not uvnew *)] [| isPrime any |]
      ).

  Lemma setGetU_prf_prime: denoteModule module ** int_store_spec  ** int_load_spec |-- setGetU_spec_prime.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    slauto...
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go...
    callAtomicCommitCinv.
    go.
    rename a into uvAtLoad.
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.
  
  Lemma duplPrime (i:Z) :
    ([| isPrime i |]:mpred) |-- [| isPrime i |] ** [| isPrime i |] .
  Proof using. go. Qed.
    
  Lemma duplPrime2 (i:Z) (this:ptr) :
    let p := this ,, _field "v" |-> atomicR "int" 1 i ** [| isPrime i |] in
    p |-- p ** [| isPrime i |].
  Proof using. go. Qed.

  (** * heart of concurrency proofs
main challenge:
sequential proofs: loop invariants
concurrency proofs: cinv

cinv more difficult:
- loopinv:  beginning/end of loop body
- concurrency invariants: always hold. all code points in all methods

7 conditions, 20 functions in codebase. weeks tweaking the cinv so that the proofs of all 20 functions go though

next .. examples of more interesting cinv
   *)
  
Definition LockR (q: Qp) (invId: gname) (lockProtectedResource: mpred) : Rep :=
  structR "::SpinLock" q
  ** cinvr invId q
      (∃ locked:bool,
      _field "::SpinLock::locked" |-> atomicR "bool" 1 (Vbool locked)
      ** if locked then emp else pureR lockProtectedResource).

Lemma lockReq (l:ptr) (q: Qp) (invId: gname)
  (lockProtectedResource: mpred):
  l |-> LockR q invId lockProtectedResource
  -|-
  l |-> structR "SpinLock" q
  ** cinv invId q
       (∃ locked : bool,
           l ,, _field "SpinLock::locked"
             |-> atomicR "bool" 1%Qp (Vbool locked) **
             (if locked then emp else lockProtectedResource)).
  Proof using.
    unfold LockR.
    rewrite _at_sep.
    f_equiv.
    unfold cinvq.
    rewrite _at_as_Rep.
    f_equiv.
    apply cinv_proper.
    iSplit; go; ren_hyp locked bool;
      destruct locked; go.
   Qed.

  cpp.spec "SpinLock::SpinLock()" as lock_constr_spec with
    (fun this:ptr =>
       \pre{lockProtectedResource:mpred} lockProtectedResource
       \post Exists invId, this |-> LockR 1 invId lockProtectedResource
     ).
  
  cpp.spec "SpinLock::lock()" as lock_spec with
    (fun this:ptr =>
       \prepost{q invId lockProtectedResource}
           this |-> LockR q invId lockProtectedResource
       \post lockProtectedResource (* non-atomics *)
    ).
  
  cpp.spec "SpinLock::unlock()" as unlock_spec with
    (fun this:ptr =>
       \prepost{q invId lockProtectedResource}
           this |-> LockR q  invId lockProtectedResource
       \pre lockProtectedResource
       \post emp
     ).

Definition ConcLListR (q:Qp) (invId: gname) (base:ptr) : mpred :=
  base |-> structR "ConcLList" q 
  ** base,, _field "ConcLList::lock"
     |-> LockR q invId
           (∃ (l:list Z), base,, _field "ConcLList::head" |-> ListR 1 l).
  
  (** * BlockState analog: *)

  Definition ucinv (q:Qp) (invId: gname): mpred
    := cinv invId q (∃ uv:Z, _global "u" |-> atomicR "int" (1/2) uv
                             ** [| isPrime uv |]).
  (** only half in cinv *)


  Definition uAuthR (invId: gname) (uv: Z): mpred
    := ucinv (1/2) invId
       ** _global "u" |-> atomicR "int" (1/2) uv.

  (* no fraction argument in uAuthR:
     p1: ucinv (1/4) invId ** _global "u" |-> atomicR "int" (1/4) uv.
     p2: ucinv (1/4) invId ** _global "u" |-> atomicR "int" (1/4) uv.
   *)
  
  Definition uFragR (q:Qp) (invId: gname) : mpred
    := ucinv (q/2) invId.
  (* different from fractional ownership:
          [_global "u" |-> atomicR "int" q 3],
          [_global "x" |-> primR "int" q 3] *)

  Lemma uFragRsplit q invId :
    uFragR q invId |--    uFragR (q/2) invId
                       ** uFragR (q/2) invId.
  Proof.
    unfold uFragR,ucinv.
    rewrite splitcinvq.
    go.
  Qed.

  Hint Resolve atomicrC : br_opacity.
  Existing Instance lcinvqg_unsafe.
  Hint Resolve cinvqC : br_opacity.
  
  Lemma init (initv:Z) E:
    _global "u" |-> atomicR "int" 1 initv ** [| isPrime initv |]
      |-- |={E}=> Exists invId, uAuthR invId initv ** uFragR 1 invId.
  Proof.
    unfold uAuthR, uFragR, ucinv. go.
    match goal with
      |- context[cinvq ?ns _ _ ?P] => wapply (cinvq_alloc_no_shared_pages _ ns P)
    end.
    iFrame.
    rewrite <- bi.later_intro.
    go.
    iModIntro.
    go.
  Qed.
            
  cpp.spec "setU(int)" as setU_spec2 with (
      \pre{(uv:Z) invId} uAuthR invId uv
      \arg{newvalue} "value" (Vint newvalue)
      \post uAuthR invId newvalue
      ).
  
  cpp.spec "getU()" as getU_spec2 with (
      \prepost{invId q} uFragR invId q
      \post{any:Z} [Vint any] [| isPrime any|]
      ).

  cpp.spec "getU()" as getU_spec_auth with (
      \prepost{invId uval} uAuthR invId uval
      \post [Vint uval] [| isPrime uval|]
      ).

  cpp.spec "setThenGetU(int)" as setThenGet_spec2 with (
      \pre{(oldvalue:Z) invId} uAuthR invId oldvalue
      \arg{uvnew:Z} "value" (Vint uvnew)
      \pre [| isPrime uvnew |]
      \post [Vint uvnew] uAuthR invId uvnew
      ).

  
  Lemma setGetU_prf2: denoteModule module ** int_store_spec  ** int_load_spec |-- setThenGet_spec2.
  Proof using MODd with (fold cQpc; normalize_ptrs).
    verify_spec'.
    unfold uAuthR, ucinv. work... (* [g440,476; g492,533; c4032,4043] *)
    slauto.
    normalize_ptrs.
    callAtomicCommitCinv.
    rename a into uvinv... (* [g567,608] [g615,653; g331,343] *)
    (* [atomicR_combine] *)
    (* [g600,608;g648,653] *)
    work using atomicR_combineF.
    rewrite <- mut_mut_add.  rewrite Qp.half_half... (* [g681,717; g604,641] *)
    go... (* [g633,638]*)
    closeCinvqs... (* [g552,557] *)
    go... (* [g474,479] [g497,499; g535,537] [g497,499; g535,537; g474,479] *)
    iModIntro...  (* code may run [c4077,4086; g441,479] but because of inv, private owned *)
    go.
    callAtomicCommitCinv.
    rename a into uvAtLoad... (* [g652,657; g697,705] *)
    (* same trick again: [atomicR_combine]
     *)
    wapply atomicR_combine. eagerUnifyU. iFrame.
    iIntros "[? a]". iRevert "a".
    rewrite <- only_provable_wand_forall_2.
    iIntros. 
    applyToSomeHyp (Vint_inj).
    subst uvAtLoad.
    rewrite <- mut_mut_add.  rewrite Qp.half_half...
    go...
    closeCinvqs.
    go.
    iModIntro.
    go.
  Qed.

  Lemma as_Rep_meaning (f: ptr -> mpred) (base:ptr) :
    (base |-> as_Rep f)  -|- f base.
  Proof using. iSplit; go. Qed.
  

      
    Opaque atomicR.
  
      Ltac finishOpeningCinv :=
      work using fwd_later_exist, fwd_later_sep;
        repeat removeLater;
        iApply fupd_mask_intro;[set_solver |]; (* openRest *)
      iIntrosDestructs.
      
  Lemma lock_lock_prf: denoteModule module ** exchange_spec |-- lock_spec.
  Proof using MODd.
    verify_spec'.
    go.
    wp_while (fun _ => emp).
    rewrite lockReq.
    go.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go. destruct a; go.
  Qed.
      
  Lemma unlock_prf: denoteModule module ** store_spec |-- unlock_spec.
  Proof using MODd.
    verify_spec'.
    rewrite lockReq.
    go.
    iExists _.
    callAtomicCommitCinv.
    go.
    closeCinvqs.
    go.
    iModIntro.
    go.
    lose_resources.
  Qed.

  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof using.
    rewrite <- demoprf.gcd_proof.
    apply denoteModule_weaken.
    apply module_le_true.
    exact _.
  Qed.

  (* move this proof to the end? without discussing loopinv, this cannot be explained *)
  Lemma gcdl_proof: denoteModule module |-- gcdl_spec.
  Proof using MODd with (fold cQpc).
    verify_spec.
    slauto.
    wp_for (fun _ => Exists iv:nat,
        i_addr |-> primR uint 1 iv
        ** [| iv <= length l |]%nat
        ** result_addr |-> primR uint 1 ((fold_left Z.gcd (firstn iv l) 0))).
    go. iExists 0%nat. go.
    wp_if.
    {
      slauto.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork...
      slauto. (* call to gcd. we have already proved it's spec *)
      wapply gcd_proof. work. (* gcd_spec is now in context *)
      go. (* loop body finished, reistablish loopinv *)
      iExists (1+iv)%nat.
      slauto.
      simpl.
      go.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.

  
  (* move this proof to the end? without discussing loopinv, this cannot be explained *)
  Lemma fold_left_prf : denoteModule module |-- fold_left_spec.
  Proof using MODd.
    verify_spec'.
    slauto.
    wp_for (fun _ => Exists iv:nat,
        i_addr |-> primR uint 1 iv
        ** [| iv <= length l |]%nat
        ** result_addr |-> primR uint 1 ((fold_left fm (firstn iv l) initv))).
    unfold cQpc.
    go.
    Set Printing Coercions.
    rewrite <- (bi.exist_intro 0%nat).
    go.
    wp_if.
    {
      slauto.
      Set Printing Implicit.
      eapplyToSomeHyp @arrayR_cell2.
      forward_reason.
      rewrite -> autogenhypr.
      hideRhs.
      go.
      unhideAllFromWork.
      slauto. (* loop body finished, reistablish loopinv *)
      iExists (1+iv)%nat.
      slauto.
      rewrite -> autogenhypr.
      go.
    }
    {
      slauto.
      assert (iv=length l) as Heq by lia.
      subst.
      autorewrite with syntactic.
      go.
    }
  Qed.
  
  cpp.spec (Nscoped 
              "parallel_fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)::@0"
              Ndtor)  as lam3destr  inline.
  Lemma pfl_proof: denoteModule module
                   ** (thread_class_specs "parallel_fold_left(unsigned int*, unsigned int, unsigned int(*)(unsigned int,unsigned int), unsigned int)::@0")
                       |-- par_fold_left_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    wapply fold_left_prf; work.
    name_locals.
    wapplyObserve  obsUintArrayR.
    eagerUnifyU. work.
    go.
    rename a into lam.
    aggregateRepPieces lam.
    hideP ps.
    Opaque Nat.div.
    assert ( (length l/ 2 <= length l)%nat) as Hle.
    {
      rewrite <- Nat.div2_div.
      apply Nat.le_div2_diag_l.
    }
    nat2ZNLdup.
    rewrite (primr_split nums_addr).
    name_locals.
    rewrite (primr_split mid_addr).
    simpl in *.
    closed.norm closed.numeric_types.
    rewrite -> arrayR_split with (i:=((length l)/2)%nat) (xs:=l) by lia;
      go... (* array ownership spit into 2 pieces *)
    revertAdrs constr:([numsp; resultl_addr; nums_addr; mid_addr]).
    repeat rewrite bi.wand_curry.
    intantiateWand.
    instWithPEvar taskPost.
    go.
    iSplitL "".
    { verify_spec'.
      go.
      iExists _, fm. eagerUnifyU.
      autorewrite with syntactic. go.
      erefl.
    }
    unhideAllFromWork.
    autorewrite with syntactic. go. 
    iExists _, fm. eagerUnifyU. 
    autorewrite with syntactic. go.
    wapply @arrayR_combinep. eagerUnifyU.
    autorewrite with syntactic. go...
    (* c++ semantics computes, postcond requires *)
    icancel (cancel_at p);[| go].
    do 2 f_equiv.
    symmetry.
    apply fold_split; auto.
  Qed.

  cpp.spec "testgcdl()" as testspec with (
    \pre emp
    \post [Vint 6] emp).

  Lemma testgcdl_prf: denoteModule module ** parallel_gcdl_spec |-- testspec.
  Proof using.
    verify_spec'.
    slauto.
  Qed.
  
#[global] Instance learnLockEq: LearnEq3 (LockR):= ltac:(solve_learnable).
End with_Sigma.

#[global] Opaque LockR.
