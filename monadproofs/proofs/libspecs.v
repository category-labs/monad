Require Import bluerock.auto.cpp.proof.

Require Import monad.asts.exb.
Require Import bluerock.auto.invariants.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.misc.

Definition PriorityPool: Type. Proof using. Admitted.

Section cp.
  Import own.
  Import frac.

Context `{Sigma:cpp_logic} {CU: genv} {hh: HasOwn mpredI algebra.frac.fracR}. (* some standard assumptions about the c++ logic *)



  (* defines how [c] is represented in memory as an object of class Chain *)
  Definition PriorityPoolR (q: Qp) (c: PriorityPool): Rep. Proof using. Admitted.

  Definition VectorRbase (cppType: type) (q:Qp) (base: ptr) (size: N): Rep.
  Proof using.
    (*Exists cap, 
       _field "base" |-> ptrR q base
       ** _field "size" |-> intR q size
       ** _field "capacity" |-> intR q cap *)
  Admitted.
  
 Definition VectorR {ElemType} (cppType: type) (elemRep: ElemType -> Rep) (q:Qp) (lt:list ElemType): Rep :=
   Exists (base: ptr), VectorRbase cppType q base (lengthN lt)
                         ** pureR (base |-> arrayR cppType elemRep lt).

    (* set_value() passes the resource/assertion P to the one calling get_future->wait()*)
  Definition PromiseR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseProducerR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseConsumerR (g: gname) (P: mpred) : Rep. Proof using. Admitted.
  Definition PromiseUnusableR: Rep. Proof using. Admitted.

  Lemma sharePromise g P:  PromiseR g P -|- PromiseProducerR g P **  PromiseConsumerR g P.
  Proof using. Admitted.

Context  {MODd : exb.module ⊧ CU}.
  Definition promise_constructor_spec (this:ptr) :WpSpec mpredI val val :=
    \pre{P:mpred} emp
    \post Exists g:gname, this |->  PromiseR g P.

  cpp.spec "boost::fibers::promise<void>::set_value()"  as set_value with
     (fun (this:ptr) =>
    \pre{(P:mpred) (g:gname)} this |-> PromiseProducerR g P
    \pre P
    \post emp).
  
  cpp.spec "monad::wait_for_promise(boost::fibers::promise<void>&)" as wait_for_promise with 
          (
            \arg{promise} "promise" (Vref promise)
            \pre{(P:mpred) (g:gname)} promise |-> PromiseConsumerR g P
            \post P ** promise |-> PromiseUnusableR).

  cpp.spec
    "std::vector<monad::Transaction, std::allocator<monad::Transaction>>::size() const"
    as tvector_spec with
      (fun (this:ptr) =>
         \prepost{q base size} this |-> VectorRbase (Tnamed "::monad::Transaction")  q base size
         \post[Vn size] (emp:mpred)
      ).

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


  Definition optionalPrimR (q:Qp) (primty:type) (on: option N): Rep :=
    optionR primty
      (fun v:N => primR primty (cQp.mut q) (Vint v)) (cQp.mut q) on.
  
  
  Definition NodeR  (q: cQp.t) (data: Z) (nextLoc: ptr): Rep :=
    _field "Node::data_" |-> primR "int" q (Vint data)
    ** _field "Node::next_" |-> primR "Node*" q (Vptr nextLoc)
    ** structR "Node" q.
  
  Fixpoint ListR (q : cQp.t) (l : list Z) : Rep :=
    match l with
    | [] => nullR
    | hd :: tl =>
        Exists (tlLoc: ptr),
          NodeR q hd tlLoc
          ** pureR (tlLoc |-> ListR q tl)
    end.

  (* Rep predicate for `std::optional<int>` *)
  Definition optionalIntR  (q:cQp.t) (o: option Z) : Rep  :=
    @optionR Z "int" (fun (z:Z) => primR "int" q (Vint z)) q o.

  (* Rep predicate for `std::optional<List>` *)
  Definition optionalListR  (q:cQp.t) (o: option (list Z)) : Rep  :=
    @optionR (list Z) "List" (fun (l: list Z) => ListR q l) q o.
  
  Definition addressR (q: Qp) (a: evm.address): Rep. Proof. Admitted.
  Definition optionAddressR (q:Qp) (oaddr: option evm.address): Rep := optionR "evmc::address" (fun a => addressR q a) q oaddr.


  (* TODO: rename to vectorbase_split_n *)
  Lemma vectorbase_loopinv {T} ty base q (l: list T) (i:nat) (Heq: i=0):
    VectorRbase ty q base (lengthN l) -|- (VectorRbase ty (q*Qp.inv (N_to_Qp (1+lengthN l))) base (lengthN l) ** 
    ([∗ list] _ ∈ (drop i l),  VectorRbase ty (q*Qp.inv (N_to_Qp (1+lengthN l))) base (lengthN l))).
  Proof using. Admitted.
  #[local] Definition fork_task_namei:= Eval vm_compute in (firstEntryName (findBodyOfFnNamed2 exb.module (isFunctionNamed2 "fork_task"))).

  Definition basee3 (n:name) :=
    match n with
    | Ninst (Nscoped (Nglobal (Nid scopename)) _) targs => scopename
    | _ => ""%pstring
    end.

  Definition all_but_last {T:Type} (l: list T):= take (length l -1)%nat l. 
  Definition fork_task_nameg (taskLamStructTy: core.name) :=
    match fork_task_namei with
    | Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q (base) argTypes)) templateArgs =>
        let argTypes' := all_but_last argTypes ++  [Tref (Tqualified QC (Tnamed taskLamStructTy))] in
        Ninst (Nscoped (Nglobal (Nid scopename)) (Nfunction q (base) argTypes')) [Atype (Tnamed taskLamStructTy)]
    | _ => Nunsupported "no match"
    end.


  Lemma fork_task_name_inst: exists ty, fork_task_nameg ty = fork_task_namei.
  Proof using.
    unfold fork_task_nameg. unfold fork_task_namei.
    eexists. reflexivity.
  Qed.

  Definition taskOpName : atomic_name := (Nop function_qualifiers.Nc OOCall) [].
  
  Definition taskOpSpec (lamStructName: core.name) (objOwnership: Rep) (taskPre: mpred):=
    specify {| info_name :=  (Nscoped lamStructName taskOpName) ;
              info_type := tMethod lamStructName QC "void" [] |}
      (fun (this:ptr) =>
         \prepost this |-> objOwnership
         \pre taskPre
         \post emp).
  
  Definition forkTaskSpec (lamStructName: core.name) : WpSpec mpredI val val :=
    \arg{priority_poolp: ptr} "priority_pool" (Vref priority_poolp)
    \prepost{priority_pool: PriorityPool} priority_poolp |-> PriorityPoolR 1 priority_pool
    \arg{priority} "i" (Vint priority)  
    \arg{task:ptr} "func" (Vref task)
    \pre{objOwnership taskPre} taskOpSpec lamStructName objOwnership taskPre
    \prepost task |-> objOwnership
    \pre taskPre
    \post emp.

  Definition fork_taskg (lamStructTyName: core.name):=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Ninst
          (Nscoped (Nglobal (Nid "monad"))
             (Nfunction function_qualifiers.N ("fork_task")
                [Tref (Tnamed (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "fiber")) (Nid "PriorityPool"))); "unsigned long"%cpp_type;
                 Tref
                   (Tconst
                      (Tnamed lamStructTyName))]))
          [Atype
             (Tnamed
                lamStructTyName)];
      info_type :=
        tFunction "void"
          [Tref (Tnamed (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "fiber")) (Nid "PriorityPool"))); "unsigned long"%cpp_type;
           Tref
             (Tconst
                (Tnamed
                   lamStructTyName))]
    |}
    (forkTaskSpec lamStructTyName).
  
  Lemma learnVUnsafe e t (r:e->Rep): LearnEq2 (VectorR t r).
  Proof. solve_learnable. Qed.
  #[global] Instance learnVUnsafe2 e t: LearnEq3 (@VectorR e t) := ltac:(solve_learnable).
  #[global] Instance learnpArrUnsafe e t: LearnEq2 (@parrayR _ _ _ _ e t) := ltac:(solve_learnable).
  #[global] Instance learnVectorRbase: LearnEq4 VectorRbase:= ltac:(solve_learnable).
  #[global] Instance learnPpool : LearnEq2 PriorityPoolR := ltac:(solve_learnable).

Definition opt_reconstr_spec T ty : ptr -> WpSpec mpredI val val :=
      (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \prepost{(R: T -> Rep) t} other |-> R t
       \pre{prev} this |-> optionR ty R 1 prev
       \post [Vptr this] this |-> optionR ty R 1 (Some t)
    ).
      
Definition opt_reconstr baseModelTy basety :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Ninst
        (Nscoped
          (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
             [Atype basety])
          ((Nop function_qualifiers.N OOEqual)
             [Trv_ref
                      basety])) [Atype basety];
      info_type :=
        tMethod
          (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
             [Atype basety])
          QM
          (Tref
             (Tnamed
                (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                   [Atype basety])))
          [Trv_ref  basety]
    |} (opt_reconstr_spec baseModelTy basety).
  

  Definition vector_opg (cppType: type) (this:ptr): WpSpec mpredI val val :=
    \arg{index} "index" (Vn index)
    \prepost{qb base size} this |-> VectorRbase cppType qb base size
    \require (index<size)%Z
    \post [Vref (base ,, .[cppType!index])] emp.

Opaque VectorR.

Definition opt_move_assign_spec T ty : ptr -> WpSpec mpredI val val :=
      (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \pre{(q:Qp) (R: T -> Rep) oaddr} other |-> optionR ty R q oaddr
       \pre{prev} this |-> optionR ty R q prev
       \post [Vptr this] this |-> optionR ty R q oaddr **  other |-> optionR ty R q None
    ).

       (* TODO: generalize the name and use [opt_move_assign_spec] *)
cpp.spec "std::optional<evmc::address>::operator=(std::optional<evmc::address>&&)" as opt_move_assign with
    (fun (this:ptr) =>
       \arg{other} "other" (Vptr other)
       \pre{q oaddr} other |-> optionAddressR q oaddr
       \pre{prev} this |-> optionAddressR 1 prev
       \post [Vptr this] this |-> optionAddressR 1 oaddr **  other |-> optionAddressR q None
    ).

(* TODO: generalize *)
  cpp.spec (Nscoped "std::optional<evmc::address>" (Ndtor)) as destrop with
      (fun (this:ptr) =>
         \pre{oa} this |-> optionAddressR 1 oa
           \post emp
      ).

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

 Definition value ty T :=
   specify
     {|
       info_name :=
         Nscoped (Ninst "std::optional" [Atype ty])
           (Nfunction function_qualifiers.Ncl "value" []);
       info_type :=
         tMethod (Ninst "std::optional" [Atype ty]) QC "const evmc::address&" []
     |}
     (fun (this : ptr) =>
         \prepost{(R : T → Rep) (t : T) (q : Qp)} this |-> optionR ty R q (Some t)
         \post[Vptr (this ,, opt_somety_offset ty)] emp).
   (*
   cpp.spec "std::optional<int>::value()" as value_int_spec with
       (fun (this:ptr) =>
       \prepost{(z : Z) (q : cQp.t)} this |-> optionalIntR q (Some z)
       \post[Vptr (this ,, opt_somety_offset "int")] emp).
                                                             ).
   *)
  #[global] Instance learnTrRbase2: LearnEq2 optionAddressR:= ltac:(solve_learnable).
  #[global] Instance learnOpt b: LearnEq4 (@optionR b):= ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseR := ltac:(solve_learnable).
  #[global] Instance : LearnEq2 PromiseProducerR:= ltac:(solve_learnable).
  
End cp.

#[global] Opaque optionR.
