(**
basic emacs tutorial:
you can your mouse to click on the menu bar above. most of the key bindings are also available via the menu bar

C-x s (press CTRL, then press x, then release CTRL then press s): save current file
C-x C-s (press CTRL, then press x, then press s then releas all): save all files
C-s: search
C-x/C-c/C-v: cut/copy/paste
C-x c: exit
C-x leftarrow: open next buffer(file) in the same frame
C-x C-leftarrow: open next buffer(file) in the same frame, ignoring pesky debug coq/magit buffers
C-x k: kill/close current file
C-x 0: kill current frame so that some adjacent frame will become bigger

C-c o: split the frame horizontally and below, open the file whose pathname the cursor is inside, e.g.
        /root/fv-workspace/monad/proofs/demo.cpp

if the cursor is inside full pathname of a file, e.g. demomisc.v

Coq-specifc key bindings:

C-rightarrow : check the file until the cursor. the checked part is always highlighted in green. if the cursor
is below the current green region, the green region will slowly grow till the cursor.
if the cursor is in the proof script, at the end, the goal at that point will be shown in the RHS window.
the cursor can be in the green region, in which case, Coq will rewind.

C-c M-i (press CTRL, then c, release CTRL, press Meta/Alt, press i, release all): recompile dependencies of current file (only those that changed or whose deps changed) and then reload coq for this file and check this file until cursor.
If you change demo.cpp, you must press this key binding so that the dune build system will regenerate the AST of monad/proofs/demo.cpp into monad/proofs/demo.v, compile demo.v to demo.vo and then Coq in this file.

M-i: jump to defnition. for this to work, the green region should at least cover all the `Require Import` lines. Ideally, the end of the green region should be just above the cursor.
 There are some known cases where jump to defn doesnt work, but ask on #formal-verification anyway if it is not working for you

*)


Require Import monad.tutorials.demo. (* monad/tutorials/demo.v, the AST of monad/tutorials/demo.cpp, produced by the cpp2v tool
(https://github.com/bluerock-io/BRiCk/blob/master/rocq-bluerock-cpp2v/README.md) *)

Require Import monad.proofs.misc. (* monad/proofs/misc.v *)
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.
Require Import bluerock.auto.cpp.tactics4.
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

(** ** Questions/comment timing recommendation *)

(** turn on zoom recording *)

(** ** why formal verification:
- highest level of assurance:
PLDI 2011: Finding and Understanding Bugs in C Compilers
CompCert C compiler

first step: write specs
 *)
Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
  Context  {MODd : demo.module ⊧ CU}.
  Coercion cQpc : Qp >-> cQp.t.

  Open Scope Z_scope.
  Set Nested Proofs Allowed.


  (* /root/fv-workspace/monad/proofs/demo.cpp *)
  cpp.spec "foo()" as foo_spec with (
        \pre{xv:Z} _global "x" |-> primR uint (cQp.mut (1/2)) xv (* forall xv .. *)
        \pre _global "y" |-> anyR uint (cQp.mut 1)
        \post _global "y" |-> primR uint (cQp.mut 1) (xv+1)
              ** _global "x" |-> primR uint (cQp.mut (1/2))  xv
      ).
  Print foo_spec.
  (* fractions ∈ (0,1], write needs 1, read any*)

  (* what is wrong with the spec above? *)

   
  Example anyR_if : _global "y" |-> uninitR uint 1
                   \\// (Exists xv:Z, _global "y" |-> primR uint 1 xv)
                 |--  _global "y" |-> anyR uint 1.
  
  Proof. rewrite bi.or_alt. go.
         ren_hyp t bool.
         destruct t; go. Qed.

  Remove Hints plogic.learnable_primR : br_opacity.

  Set Printing Width 100.
  (* The game of proof: gory details *)
  Lemma prf: denoteModule demo.module |-- foo_spec.
  Proof with (fold cQpc).
    verify_spec...
    (* ignore numbers here, focus on the bluish highlight *)
    (* meaning of goal view: [g289,367] [g437,696; c123,146]
[g713,796] [g437,696; c123,146]*)
    (* now symbolically execute code one AST node at a time *)
    do 4 run1; step... (* writing to y: demands full(1) ownership [g435,468;c129,131] [g435,468; g318,352;c129,131] *)
    (* cancel highlighted. 1BTC *)
    iFrame... (* y gone from wallet [g278,398]*)
    iIntros... (*[g361,397] write done: receive postcond of write. uniswap *)
    do 3 run1...
    (* eval f operand (argument) of + : [g524,549;c140,141] *)
    step... (* cant read uninit location [g399,401; g479,480; g527,528; g719,720] [g392,395; g487,488; g526,527]*)
                                                                                 
    iExists xv; (* instantiate v with xv, q with 1 *)
    work; [iExists (1/2:cQp.t); work|]... (* free transaction [g544,555; c142,143]  2nd op of + *)
    do 2 step... (* free! [g512,516; c141,142] *)
    step;
    unfold trim;
      step.
    iFrame... (* [g479,512;c138,140] [g403,439; g479,512;c138,140] *)
    Check anyR_if.
    rewrite -> (primR_anyR _ _ 0)... (* cancel [g403,437; g477,510;c138,140] *)
    iFrame...
    iIntros... (* write finished  [g439,454] *)
    do 10 step... (* code finished. post.  cancel y [g658,698; g481,522] *)
    iFrame...
  Abort. (* bug in spec *)

  (* summarize: rule of the game
how we lose:
- at end : postcond mismatch
- during symbolic code exec: wallet is too weak/underfunded to meet \pre of a c++ command/expression
   *)
  cpp.spec "foo()" as foo_spec2 with (
        \pre{xv:Z} _global "x" |-> primR uint (1/2) xv (* forall xv .. *)
        \post _global "x" |-> primR uint (1/2)  xv
    ).

  Lemma prf: denoteModule module |-- foo_spec2.
  Proof using.
    verify_spec'.
    go.
  Abort. (* game over even before executing the code fully *)
  
  Hint Resolve plogic.learnable_primR : br_opacity.

  cpp.spec "foo()" as foo_spec_correct with (
        \prepost{(xv:Z) (q:Qp)} _global "x" |-> primR uint q xv
        \pre{yv:Z} _global "y" |-> primR uint 1 yv
        \post _global "y" |-> primR uint 1 ((xv+1) `mod` (2^32))
      ).

  Lemma prf: denoteModule demo.module |-- foo_spec_correct.
  Proof.
    verify_spec.
    slauto.
  Qed.

  cpp.spec "sfoo()" as sfoo_spec with (
    \pre{xv:Z} _global "a" |-> primR "int" 1 xv
    \pre{yv:Z} _global "b" |-> primR "int" 1 yv
    \post _global "b" |-> primR "int" 1 ((xv+1))%Z ** _global "a" |-> primR "int" 1 xv
      ).

  (* what is wrong with the spec above? *)

  Lemma sprf: denoteModule demo.module |-- sfoo_spec.
  Proof.
    verify_spec'.
    slauto.
    provePure.
  Abort.
  
  cpp.spec "sfoo()" as sfoo_spec_correct with (
    \prepost{xv:Z} _global "a" |-> primR "int" 1 xv
    \pre [| (- 2 ^ (32 - 1) -1  ≤ xv ≤ 2 ^ (32 - 1) - 2) |]
    \pre{yv:Z} _global "b" |-> primR "int" 1 yv
    \post _global "b" |-> primR "int" 1 ((xv+1))
      ).

  Lemma sprf: denoteModule demo.module |-- sfoo_spec_correct.
  Proof.
    verify_spec'.
    slauto.
  Qed.

  (** *Under the hood: *)

  (** Pre and post conditions of specs are elements of type [mpred] *)

  Require Import stdpp.decidable.
  Import Znumtheory.
  Example isPrime (bv: Z): Prop := prime bv.
  Lemma proof: isPrime 3.
  Proof.  apply prime_3. Qed.
  
  (* `mpred` (memory predicates): they can implicitly
             talk about the current state of memory and ownership of memory locations.
        memory --> "state of the world"
   *)
  Example assertion1 (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.

  Example embed (P:Prop) : mpred := [| P |].
  Example pureAssertion (bv:Z) : mpred := [| bv=0|].

  (** postcond of a function that guarantees to set variable b to a prime number:
     note the nondeterminism *)
  Example as2 :mpred := Exists (bv:Z),
      _global "b" |-> primR "int" 1 bv
      ** [| Znumtheory.prime bv |].

  Example conjP (P Q: Prop) := P /\ Q.
  Example conjmpred (P Q: mpred) : mpred := P ** Q.

  (** -> is logical implication, aka => in math textbooks *)
  Lemma propDupl (P:Prop) : P -> P /\ P. Proof. tauto. Qed.

  (** - analogous property doesnt hold in `mpred`.
      - ownership is like bitcoin: cannot doublespend*)
  Lemma doesNotHold1 (xv:Z):
    let own: mpred := _global "x" |-> primR "int" 1 xv in
    own |-- own ** own.
  Abort.

  (* knowledge can be freely duplicated, resources cannot *)
  Lemma propEmbedDupl (n:Z) :
    let o : mpred :=   [| isPrime n |] in o |-- o ** o.
  Proof. go. Qed.
          
  Example as11 (bv:Z) :mpred :=  _global "b" |-> primR "int" 1 bv.
  (** |-> : points_to *)
  (** left of |-> must be a memory location, of type [ptr] *)
  Example memLoc: ptr := _global "b".

  (** right of |-> must be a "memory representation", of type [Rep].
      Reps:
      - defines how some "mathematical" Coq object is laid out in memory
      - specify the amount of ownership

     The cpp2v logic axiomatizes representations of primitives:
             int/char/long/int*/...
   *)
  
  Example intRep (q:Qp) (x:Z) : Rep := primR "int" q x.

  Example UnboundedIntR (q:Qp) (x:Z) : Rep. Abort.
  (* [c3701,3779] *)
  
  Check primR.
  Print val. (* primitive values in C++. vs struct objects/arrays *)
  Example as3 (bv:Z): mpred := _global "b" |-> primR "int" 1 (Vint bv).
  Example as3elide (bv:Z): mpred := _global "b" |-> primR "int" 1 bv.
  Set Printing Coercions.
  Print as3elide.
  Unset Printing Coercions.

  Example ptrRep (q:Qp) (mloc: ptr) : Rep := primR "int*" q (Vptr mloc).
  (* [c198,206] *)

  cpp.spec "fooptr()" as ptrspec with
      (\pre _global "ptr" |-> anyR "int*" 1
       \post _global "ptr" |-> primR "int*" 1 (Vptr (_global "a")) 
      ).
  (* [c209,241] *)

  Lemma foopptr: denoteModule module |-- ptrspec.
  Proof.
    verify_spec'.
    slauto.
  Qed.
  (** "all" theorem statements in Coq have type Prop *)
  Example stm (L R : mpred): Prop := L |-- R.
  
  cpp.spec "twice(unsigned int)" as twice_weak_spec with (
     \arg "x" (Vint 1)
     \post [Vint 2] emp
      ).
  cpp.spec "twice(unsigned int)" as twice_weak_spec2 with (
     \arg{xv:Z} "x" (Vint xv)
     \post{xvfinal} [Vint xvfinal] [| xvfinal `mod` 2 = 0 |]
      ).
  
  cpp.spec "twice(unsigned int)" as twice_spec with (
     \arg{xv:Z} "x" (Vint xv)
     \post [Vint ((xv*2) `mod` (2^32))] emp
      ).
  (* no ownership received/returned *)

  Lemma twice_proof: denoteModule module |-- twice_spec.
  Proof using.
    verify_spec'.
    ego.
  Qed.
  
  Lemma twice2_proof: denoteModule module |-- twice_weak_spec.
  Proof using.
    verify_spec'.
    ego.
  Qed.

  cpp.spec "doubleInPlace(unsigned int &)" as doubleInPlace_spec with (
     \arg{xloc:ptr} "x" (Vptr xloc)
     \pre{xv:Z} xloc |-> primR "unsigned int" (cQp.mut 1) (Vint xv)
     \post xloc |-> primR "unsigned int" (cQp.mut 1) (Vint ((xv*2) `mod` (2^32)))
      ).
  
  Lemma moreThanLogicalImpl :
    _global "x" |-> primR "int" (1/3) 0 |--
    _global "x" |-> primR "int" (1/2) 0.
  Abort. (* not provable *)
  
  Print ptrspec.
  Example specstar : WpSpec mpredI val val :=
    \pre _global "x" |-> primR "int" (1/3) 0
    \pre _global "y" |-> primR "int" (1/3) 0
    \post emp.
  
  Example specstarEquiv : WpSpec mpredI val val :=
    \pre _global "x" |-> primR "int" (1/3) 0
         ** _global "y" |-> primR "int" (1/3) 0
    \post emp.

  (** ** functions that take arguments *)
  
  (* now ownership received/returned *)
  cpp.spec "gcd(unsigned int, unsigned int)" as gcd_spec with (
     \arg{av:Z} "a" (Vint av) (* forall av, ... *)
     \arg{bv:Z} "b" (Vint bv)
     \post [Vint (Z.gcd av bv)] emp
      ).

  (**  we pass most args by reference ... *)
  cpp.spec "gcd(const unsigned int&, const unsigned int&, unsigned int&)"
    as gcd2_spec with (
    \arg{ap:ptr} "a" (Vptr ap)
    \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
    \arg{bp:ptr} "b" (Vptr bp)
    \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
    \arg{resultp:ptr} "gcd_result" (Vptr resultp)
    \pre resultp |-> anyR uint 1
    \post resultp |-> primR uint 1 (Z.gcd av bv)
      ).
  (* [g1,1; c375,385] *)

  (** \prepost  in sequential code, ..., but in concurrent code ...*)

  Lemma primr_split_half (p:ptr) ty (q:Qp) v :
    p|-> primR ty q v -|-
      (p |-> primR ty (q/2) v) ** p |-> primR ty (q/2) v.
  Proof. apply primr_split. Qed.
  
  (** parallel_gcd_lcm in demo.cpp *)
  (** diagram *)
  
  
  (** *Demo: read-read concurrency using fractional permissions *)

  (*
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

*)  

  cpp.spec "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)"
   as par_gcd_lcm_spec with (
   \arg{ap} "a" (Vptr ap)
   \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
   \arg{bp} "b" (Vptr bp)
   \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
   \arg{gcd_resultp} "gcd_result" (Vptr gcd_resultp)
   \pre gcd_resultp |-> anyR uint 1
   \arg{lcm_resultp} "lcm_result" (Vptr lcm_resultp)
   \pre lcm_resultp |-> anyR uint 1
   \pre[| 0<bv \/ 0<av |] (* why is this needed? *)
   \post gcd_resultp |-> primR uint 1 (Z.gcd av bv) ** lcm_resultp |->
         (if decide (av*bv < 2^32)
          then primR uint 1 (Z.lcm av bv)
          else Exists garbage, primR uint 1 garbage)
      ). (* [c1290,1312] *)
  
  Definition ThreadR (lamStructName: core.name) (P Q : mpred) : Rep. Proof. Admitted.
  Definition ThreadStartedR (lamStructName: core.name) (Q : mpred) : Rep. Proof. Admitted.
  Definition ThreadDoneR (lamStructName: core.name) : Rep. Proof. Admitted.
  Definition taskOpName : atomic_name := (Nop function_qualifiers.Nc OOCall) [].

  
  Definition ThreadConstructor (lamStructName: core.name) (this:ptr): WpSpec mpredI val val :=
    \arg{lambdap:ptr} "lambda" (Vptr lambdap)
    \prepost{lamStructObjOwnership} lambdap |-> lamStructObjOwnership
    \pre{taskPre taskPost}
      specify {| info_name :=  (Nscoped lamStructName taskOpName);
                info_type := tMethod lamStructName QC "void" [] |}
           (fun (this:ptr) =>
              \prepost this |-> lamStructObjOwnership
                \pre taskPre
                \post taskPost)
    
    \post this |-> ThreadR lamStructName taskPre taskPost. (* [c1231,1285] *)

  Definition start (lamStructName: core.name) (this:ptr)
       :WpSpec mpredI val val :=
    \pre{taskPre taskPost} this |-> ThreadR lamStructName taskPre taskPost
    \pre taskPre (* NOT a prepost *)
    \post this |-> ThreadStartedR lamStructName taskPost. (* [c570,582] *)

  Definition join (lamStructName: core.name) (this:ptr)
       : WpSpec mpredI val val :=
    \pre{taskPost} this |-> ThreadStartedR lamStructName taskPost
    \post taskPost ** this |-> ThreadDoneR lamStructName.

    Definition ThreadDtor (lamStructName: core.name) (this:ptr)
       : WpSpec mpredI val val :=
    \pre this |-> ThreadDoneR lamStructName
    \post emp.

    (** protocol enforced, concurrency clarified: cannot split ThreadR *)

  Definition thread_constructor (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nctor [Tref (Tconst (Tnamed lamStructTyName))]);
      info_type :=
        tCtor (Ninst "Thread" [Atype (Tnamed lamStructTyName)])
          [Tref (Tconst (Tnamed lamStructTyName))]
    |}
    (ThreadConstructor lamStructTyName).

  Definition thread_destructor (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) Ndtor;
      info_type :=
        tDtor (Ninst "Thread" [Atype (Tnamed lamStructTyName)])
    |}
    (ThreadDtor lamStructTyName).
  
  Definition thread_start (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "start" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (start lamStructTyName).

  Definition thread_fork_join (lamStructTyName: core.name) :=
  specify
    {|
      info_name :=
        Nscoped (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) (Nfunction function_qualifiers.N "join" []);
      info_type :=
        tMethod (Ninst "Thread" [Atype (Tnamed lamStructTyName)]) QM "void" []
    |}
    (join lamStructTyName).
  
  Definition thread_class_specs lamStructName :=
    thread_constructor lamStructName **
    thread_start lamStructName **
    thread_fork_join lamStructName **
    thread_destructor lamStructName.
   
  Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : forall ty P Q, Observe (reference_toR (Tnamed (Ninst "Thread" [Atype (Tnamed ty)]))) (ThreadR ty P Q).
  Proof. Admitted.
  #[global] Instance : forall ty Q, Observe (reference_toR (Tnamed (Ninst "Thread" [Atype (Tnamed ty)]))) (ThreadStartedR ty Q).
  Proof. Admitted.
  #[global] Instance : forall ty, Observe (reference_toR (Tnamed (Ninst "Thread" [Atype (Tnamed ty)]))) (ThreadDoneR ty).
  Proof. Admitted.
  #[global] Instance : forall ty , LearnEq2 (ThreadR ty) := ltac:(solve_learnable).
  #[global] Instance : forall ty , LearnEq1 (ThreadStartedR ty) := ltac:(solve_learnable).

  (* TODO: delete?*)
  #[global] Instance obss (pp:ptr) ty P Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp)
                                             (pp |-> ThreadR ty P Q). 
  Proof. Admitted.

  #[global] Instance obsss (pp:ptr) ty Q: Observe (reference_to (Tnamed (Ninst "Thread" [Atype (Tnamed ty)])) pp)
                                             (pp |-> ThreadStartedR ty Q). 
  Proof. Admitted.
  


  Lemma par: denoteModule module
             |-- par_gcd_lcm_spec.
  Proof using MODd.
    verify_spec.
    go.
    (* missing spec of Thread Constructor *)
  Abort.

  Set Nested Proofs Allowed.

  cpp.spec (Nscoped 
              "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr inline.
  
  Lemma par: denoteModule module
               ** (thread_class_specs "parallel_gcd_lcm(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0")
               ** gcd2_spec (* proven later in this file *)
             |-- par_gcd_lcm_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    slauto.
    rename a into lam...
    (* call to [ThreadConstructor] just happened  [c1384,1463]*)
    aggregateRepPieces lam. go.
    iExists (     gcd_resultp |-> anyR uint 1
               ** ap |-> primR uint (qa/2) av
               ** bp |-> primR uint (qb/2) bv)...
    instWithPEvar taskPost... (* taskPost: infer it automatically, optimally *)
    slauto; iSplitL ""...
    (* scroll up: remaining precond of [ThreadConstructor] *)
    { verify_spec'.
      go... (* any postcond choice must be implied by currently available context => it is the strongest postcond *)
      erefl.
      (* inferring both \pre and \post: no optimality guarantee *)
    }
    unhideAllFromWork.
    iIntrosDestructs.
    subst taskPost... (* now we have the postcond of Thread constructor *)
    
    do 11 run1... (* [g2350,2357; c1469,1479]. *)
    Remove Hints primR_split_C: br_opacity.
    step... (* preconditions of [start]*)
    do 2 step... (* lost gcd_resultp. *)
    rewrite (primr_split ap);
    rewrite (primr_split bp)...
    run1... (* got only TheadStartedR back,lost ownership gcd_resultp, 1/2 of a,b. 1/2 suffices for a,b. next: operands of * *)
    Hint Resolve primR_split_C: br_opacity.

    name_locals.
    do 7 run1... (* call to [join] [g2408,2415; c1558,1567] *)
    run1... (* back: gcd_resultp ownership, updated value. other halfs:imp!. *)
    do 4 run1;
    do 1 (step;[slauto|]); step; step;[slauto|]... (*/ [g2257,2261; c1591,1592] *)
    step...
    pose proof (Z.gcd_eq_0 av bv);
    pose proof (Z.gcd_nonneg av bv);
    go. (* code finished, remaining postcond:  *)
    case_decide.
    2:{ (* overflow case*) go. }
    {
       (* uint *: % 2^32 *)
      icancel (cancel_at lcm_resultp);[| go]. 
      do 2 f_equiv. (* L is what c++ semantics computed, R is what the postcondition requires *)
      Arith.remove_useless_mod_a.
      unfold Z.lcm.
      rewrite -> Z.lcm_equiv1 by arith.
      rewrite -> Z.abs_eq by (apply Z_div_nonneg_nonneg; try arith).
      rewrite Z.quot_div_nonneg; arith.
    }
  Qed.

  (** Summary so far:

- start thread: partitioning resources
- fractional permissions: split for concurrent reads
- many more ways to split, e.g. write/write, write/read concurrency
- enforce complex protocols:
      - one thread can only increment a counter, another can only decrement

*)

  
(** * Exercises *)

  (** ** Exercise 1: explain the bug parallel_gcd_lcm_wrong and how it breaks the proofs.
Details:  in demo.cpp (in same directory as this file), we have another function, parallel_gcd_lcm_wrong.
This functions is also included below as a comment for your convenience.
the only change is that t1.join() is moved down.
Explain why we cannot prove even a weaker spec for it. Below, in `Lemma parwrong`,  we try to prove the weaker spec.
Look at the goal state just before `Abort.` and explain where the proof is stuck.
Does this bug parallel_gcd_lcm_wrong have undefined behaviour? if so, which one?

void parallel_gcd_lcm_wrong(const uint &a, const uint &b, uint &gcd_result, uint &lcm_result) {
    Thread t1([&gcd_result, &a, &b]() {
        gcd(a,b, gcd_result);
    });
    t1.start();
    uint product=a*b;
    lcm_result=product/gcd_result;
    t1.join();
}
   *)
  cpp.spec "parallel_gcd_lcm_wrong(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)"
   as par_gcd_lcm_wrong_spec with (
   \arg{ap} "a" (Vptr ap)
   \prepost{(qa:Qp) (av:Z)} ap |-> primR uint qa av
   \arg{bp} "b" (Vptr bp)
   \prepost{(qb:Qp) (bv:Z)} bp |-> primR uint qb bv
   \arg{gcd_resultp} "gcd_result" (Vptr gcd_resultp)
   \prepost gcd_resultp |-> anyR uint 1
   \arg{lcm_resultp} "lcm_result" (Vptr lcm_resultp)
   \prepost lcm_resultp |-> anyR uint 1
   \pre[| 0<bv \/ 0<av |]
   \post emp
      ).

  cpp.spec (Nscoped 
              "parallel_gcd_lcm_wrong(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0" Ndtor)  as lamdestr2 inline.
  
  Lemma par_wrong: denoteModule module
               ** (thread_class_specs "parallel_gcd_lcm_wrong(const unsigned int&, const unsigned int&, unsigned int&, unsigned int&)::@0")
               ** gcd2_spec (* proven later in this file *)
             |-- par_gcd_lcm_wrong_spec.
  Proof using MODd with (fold cQpc).
    unfold thread_class_specs.
    verify_spec'.
    slauto.
    rename a into lam...
    (* call to [ThreadConstructor] just happened  [c1384,1463]*)
    aggregateRepPieces lam. go.
    iExists (     gcd_resultp |-> anyR uint 1
               ** ap |-> primR uint (qa/2) av
               ** bp |-> primR uint (qb/2) bv)...
    instWithPEvar taskPost... (* taskPost: infer it automatically, optimally *)
    slauto; iSplitL ""...
    { verify_spec'.
      go... 
      erefl.
    }
    unhideAllFromWork.
    iIntrosDestructs.
    subst taskPost...
    slauto.
  Abort.


  (** ** Exercise2 prove the spec of parallel_gcd_lcm2, which passes most args by value
Details: The spec is already written bewlow, and  the proof (`Lemma  par_gcd_lcm2_proof`)
is already done, except for 1 hole, marked below.
This hole represents the resources that will be given to the child thread when it starts.
If you fill this hole correctly, the rest of the proof will go through without any change.
Hint: in this case, the arguments `a` and `b` are captured in the lambda by value, not by reference.
So, the lambda (struct) has its own copy of `a` and `b` and does not
actually read those variables from  parallel_gcd_lcm2.
As beflore, gcd_result is captured by reference, and the lambda directly writes to the gcd_result in parallel_gcd_lcm2


uint parallel_gcd_lcm2(uint a, uint b, uint &gcd_result) {
    Thread t1([&gcd_result, a, b]() {
          gcd_result=gcd(a,b);
       });
    t1.start();
    uint product=a*b;// pretend this is expensive, e.g. 1000 bit numbers
    t1.join();
    return product/gcd_result;
}

   *)

  cpp.spec "parallel_gcd_lcm2(unsigned int, unsigned int, unsigned int&)"
   as par_gcd_lcm2_spec with (
   \arg{av} "a" (Vint av)
   \arg{bv} "b" (Vint bv)
   \arg{gcd_resultp} "gcd_result" (Vptr gcd_resultp)
   \pre gcd_resultp |-> anyR uint 1
   \pre[| 0<bv \/ 0<av |] (* why is this needed? *)
   \post [Vint (if decide (av*bv < 2^32) then (Z.lcm av bv) else (((av * bv) `mod` 2^32) `quot` Z.gcd av bv))] 
           gcd_resultp |-> primR uint 1 (Z.gcd av bv)).

  cpp.spec (Nscoped 
              "parallel_gcd_lcm2(unsigned int, unsigned int, unsigned int&)::@0" Ndtor)  as lamdestr3 inline.

  Lemma par_gcd_lcm2_proof: denoteModule module
               ** (thread_class_specs "parallel_gcd_lcm2(unsigned int, unsigned int, unsigned int&)::@0")
               ** gcd_spec (* proven later in this file *)
               |-- par_gcd_lcm2_spec.
  Proof using MODd.
    unfold thread_class_specs.
    verify_spec'.
    slauto.
    rename a into lam...
    (* call to [ThreadConstructor] just happened  [c1384,1463]*)
    aggregateRepPieces lam. go.
    (* For exercise 2, replace emp in the line below with the approppriate instantiation of taskPre, which denotes the resources that will be given to the child thread(t1). Once you fill it in correctly, the rest of the proof will go through without any change. You can also look at the proof state just after the "go..." 8 lines below to figure out the resources neede by the lambda function and then come back here to update taskPre*)
    iExists (gcd_resultp |-> anyR uint 1). 
    
    instWithPEvar taskPost... (* taskPost: infer it automatically, optimally *)
    slauto; iSplitL ""...
    (* prove the spec of the lambda function, with \pre as the taskPre chosen above ** the ownership of the fields of the lambdd struct (captured variables) *)
    { verify_spec'.
      go... (* any postcond choice must be implied by currently available context => it is the strongest postcond *)
      erefl.
    }
    unhideAllFromWork.
    iIntrosDestructs.
    subst taskPost... (* now we have the postcond of Thread constructor *)

    slauto.
    pose proof (Z.gcd_eq_0 av bv);
      pose proof (Z.gcd_nonneg av bv).
    slauto.
    case_decide.
    2:{ (* overflow case*) go. }
    {
      icancel (cancel_at p);[| go]. 
      do 2 f_equiv. (* L is what c++ semantics computed, R is what the postcondition requires *)
      Arith.remove_useless_mod_a.
      unfold Z.lcm.
      rewrite -> Z.lcm_equiv1 by arith.
      rewrite -> Z.abs_eq by (apply Z_div_nonneg_nonneg; try arith).
      rewrite Z.quot_div_nonneg; arith.
    }

   Qed.
    
(** End exerciss *)
  
  (** another source of complexity in proofs: loops
*)
  Lemma gcd_proof: denoteModule module |-- gcd_spec.
  Proof with (fold cQpc).
    verify_spec.
    slauto...
    rename av into av_init.
    rename bv into bv_init.
    wp_while  (fun _ =>
             (Exists av' bv' : Z,
                 [| 0 ≤ av' ≤ 2 ^ 32 - 1 |]
                 **[| 0 ≤ bv' ≤ 2 ^ 32 - 1 |]
                 ** a_addr |-> primR Tu32 1 (Vint av')
                 ** b_addr |-> primR Tu32 1 (Vint bv')
                 ** [| Z.gcd av' bv' = Z.gcd av_init bv_init |]))...
    slauto.
    ren a_addr av'.
    ren b_addr bv'. (* context is now generalized to be the loopinv: av --> av', but H *)
    wp_if; intros.
    { (* loop cond true: exec body:  *)
      do 10 run1.
      (* reached end of loop body, asked to: 1) return FULL ownership of temp 2) reistablish loopinv *)
      (* av'0 := bv', bv'0:= av' `mod` bv' *)
      slauto. (* gcd of new values of a b = gcd of original a b *)
      aac_rewrite Z.gcd_mod; arith.
    }

    { (* loop condition is false =>  bv'=0  and loop terminates*)
      slauto...
      (* C++ computes av' as return value but postcondition requires... *)
      (* H comes from the loopinv *)
      match goal with
        | H: _ |- _ =>
            aac_rewriteh Z.gcd_0_r_nonneg in H;[| assumption]
      end.
      subst. go.
          
    }
  Qed.

  Lemma gcd2_proof: denoteModule module |-- gcd2_spec.
  Proof.
    verify_spec'.
    wapply gcd_proof. go.
  Qed.


(** Next tutorial sessions

Next:
- more expressive ways to split ownership: read-write/ write/write-concurrency: SPSCQueue: one thread can only increment one can only decrement
- deeper dive into proofs of execute_block

After next:
- pick a module in our codebase, write specs, sketch high-level correctness proof

Overall goal:
- write specs in Coq.
  + precise documentation
  + tools to either prove the spec, or give you counterexample
  + when bug happens, can focus on unprover parts

 *)

  Lemma doubleSpending: _global "x" |-> primR "int" 1 0 ** _global "x" |-> primR "int" 1 0|-- [| False |].
  Proof. Abort.
  
  Lemma okSpending: _global "x" |-> primR "int" (1/2) 0 ** _global "x" |-> primR "int" (1/2) 0|--  _global "x" |-> primR "int" 1 0.
  Proof. Abort.
  Lemma duplTypePtr (ap:ptr): type_ptr uint ap |-- type_ptr uint ap ** type_ptr uint ap.
  Proof. go. Qed.
  Lemma duplSpec (ap:ptr): gcd_spec |-- gcd_spec ** gcd_spec.
  Proof. go. Qed.
                                          
  Example nestedArrayR (rows: list (list Z)) (p:ptr) (q:Qp): mpred :=
p|->arrayR "int*"
      (fun mrow: list Z => Exists rowBase:ptr, primR "int*" q (Vptr rowBase)
                            ** pureR (rowBase |-> arrayR "int" (fun i:Z => primR uint q i) mrow))
      rows.

  
End with_Sigma.

