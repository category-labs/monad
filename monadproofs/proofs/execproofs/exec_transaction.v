Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.ext.
Require Import monad.proofs.exec_specs.
  Import environments.
  
Ltac applyPHyp :=
  let Hbb := fresh "autogenhyp" in
  match goal with
    [ Ha:?T, Hb: _ |- _] =>
      let Tt := type of T in
      unify Tt Prop;
      pose proof Hb as Hbb; apply Ha in Hbb
  end.

      Ltac assertp foo :=  iAssert foo as "#?"%string;[admit|].

  Ltac hidePost :=
  IPM.perm_left ltac:(fun L n =>
                          let f:= fresh "fullyHiddenPostcond" in
                        match L with
                        | HiddenPostCondition => hideFromWorkAs L f
                        end
                     ).
      Opaque libspecs.optionR.
  Lemma wAssert2 `{cpp_logic} {A B:Type}(P: A-> B-> Rep) (p:ptr): forall a b, p|->P a b |-- p|-> P a b. Proof. reflexivity. Qed.
  Lemma wAssert3 `{cpp_logic} {A B C:Type}(P: A-> B-> C-> Rep) (p:ptr): forall a b c, p|->P a b c|-- p|-> P a b c. Proof. reflexivity. Qed.
  Ltac foldRep Rc R :=
    (wapply (wAssert2 Rc)
     || wapply (wAssert3 Rc));
    lazymatch goal with
    | |- envs_entails _ (_ ** ?r) =>
        let fn := fresh "CallresumeUseWand" in
        hideFromWorkAs r fn
    end;
    unfold R;
    work;
    repeat (iExists _);
    eagerUnifyU;
    work;
    lazymatch goal with
    | |- envs_entails _ ?r => hsubst r
    end.
    
  Tactic Notation "foldr" constr(Rc) reference(R) := (foldRep Rc R).

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : ext.module ⊧ CU}.

  Set Nested Proofs Allowed.
  Set Printing Coercions.
  #[global] Instance learnOpt a b c d e a1 b1 c1 d1 e1: Learnable (@libspecs.optionR _ _ _ _ a b c d e) (@libspecs.optionR _ _ _ _ a1 b1 c1 d1 e1) [a=a1] := ltac:(solve_learnable).

  cpp.spec (Ninst
     "monad::execute_impl(const monad::Chain&, unsigned long, const monad::Transaction&, const evmc::address&, const monad::BlockHeader&, const monad::BlockHashBuffer&, monad::BlockState&, boost::fibers::promise<void>&)"
     [Avalue (Eint 11 "enum evmc_revision")]) as fff inline.

  cpp.spec (Ninst
        "monad::static_validate_transaction(const monad::Transaction&, const std::optional<intx::uint<256u>>&, const intx::uint<256u>&, unsigned long)"
        [Avalue (Eint 11 "enum evmc_revision")])  as validate_spec with
      (
        \arg{txp} "tx" (Vref txp)
        \prepost{qtx t} txp |-> TransactionR qtx t
        \arg{basefeep} "base" (Vref basefeep)
        \arg{chainidp} "chainid" (Vref chainidp)
        \arg{maxcodesize} "maxcodesize" (Vint maxcodesize)
       \post{retp} [Vptr retp] (reference_to
     "boost::outcome_v2::basic_result<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>"
    retp ∗
 retp |-> emp)
      ).

(* TODO : generalize over 256 *)
Definition destr_u256 :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Nscoped
          (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])
          (Ndtor);
      info_type :=
        tDtor
          (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])
    |} (λ this : ptr, \pre{w} this |-> u256R 1 w
                        \post    emp).
  #[global] Instance : LearnEq2 u256R := ltac:(solve_learnable).

  cpp.spec 
          "boost::outcome_v2::try_operation_has_value<boost::outcome_v2::basic_result<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>&, bool>(boost::outcome_v2::basic_result<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>&, boost::outcome_v2::detail::has_value_overload)" as try_op_has_val with
      (
        \arg{basefeep} "base" (Vref basefeep)
        \arg{chainidp} "base" (Vref chainidp)        
        \post [Vbool true] emp).

Definition destr_outcome_overload :=
λ {thread_info : biIndex} {_Σ : gFunctors} {Sigma : cpp_logic thread_info _Σ} {CU : genv},
  specify
    {|
      info_name :=
        Nscoped
          (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload"))
          (Ndtor);
      info_type :=
        tDtor
          (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload"))
    |} (λ this : ptr, \pre this |->  structR (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload")) (cQp.mut 1)
                        \post    emp).

(* use a const instance instead *)
  Lemma wp_const_const_delete tu ty from to p Q :
    Q |-- wp_const tu from to p ty Q.
  Proof using. Admitted.

  cpp.spec (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))
             (Nctor ["unsigned long"%cpp_type; "unsigned long"%cpp_type]))
         as incarnation_constr with
  (fun this:ptr =>
     \arg{bn} "" (Vn bn)
       \arg{txindex:nat} ""  (Vint (Z.of_nat txindex + 1))
     \post this |-> IncarnationR 1 (Build_Indices bn (N.of_nat txindex))  
  ).

Definition destr_incarnation :=
  specify
    {|
      info_name :=
        Nscoped
          (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))
          (Ndtor);
      info_type :=
        tDtor
          (Nscoped (Nglobal (Nid "monad")) (Nid "Incarnation"))
    |} (λ this : ptr, \pre{w} this |-> IncarnationR 1 w
                        \post    emp).
Require Import bluerock.prelude.lens.


    Import LensNotations.
    #[local] Open Scope lens_scope.

    Locate balance.
    Definition minSenderBalForTx (tx: Transaction): N. Proof. Admitted.
    Definition relaxed_constructor_init_state (sender_addr: evm.address) (sender_nonce min_sender_balance: N) (bsp: ptr) (ind: Indices) (sf: StateM) : Prop :=
      exists (loc:ptr) senderAc, senderAc .^ _nonce = sender_nonce /\ (min_sender_balance <= senderAc .^ _balance)%Z  /\
        sf =
          {|
            relaxedValidation:= true;
            newStates:= [];
            preTxAssumedState := [(sender_addr, (loc,( {| coreState := Some senderAc; relevantKeys :=[]; substateModel := Build_AccountSubstateModel false false false [] |},  {| min_balance := Some min_sender_balance  ; nonce_exact :=false |})))];
            blockStatePtr := bsp;
            indices:= ind;
          |}.


    Definition u256t : type :=
      Tnamed ((Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])).
    
  cpp.spec (Nscoped "monad::State"
          (Nctor
             [Tref "monad::BlockState";
              Tnamed "monad::Incarnation"
    ]))
    as StateConstrExact with
  (    fun (this:ptr) =>
      \arg{bsp} "" (Vref bsp)
      \arg{incp} "" (Vptr incp)
      \prepost{q inc} incp |-> IncarnationR q inc 
      \post this |-> StateR {| blockStatePtr := bsp; indices:= inc; preTxAssumedState := []; newStates:= []; relaxedValidation := true|}).
  
  Lemma observeState (state_addr:ptr) t: 
    Observe (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))) state_addr)
            (state_addr |-> StateR t).
  Proof using. Admitted.

  Definition observeStateF r t := @observe_fwd _ _ _ (observeState r t).
  Hint Resolve observeStateF : br_opacity.
(*            ** (reference_to "monad::State" this)). (* convenient but logically redundant *) *)

#[global] Instance : LearnEq2 (addressR) := ltac:(solve_learnable).
#[global] Instance : LearnEq1 (StateR) := ltac:(solve_learnable).

cpp.spec ( Ninst
        "monad::execute_impl2(monad::CallTracerBase&, const monad::Chain&, const monad::Transaction&, const evmc::address&, const monad::BlockHeader&, const monad::BlockHashBuffer&, monad::State&)"
        [Avalue (Eint 11 "enum evmc_revision")])
  as execute_impl2 with (execute_impl2_specg).

  
  #[global] Instance : LearnEq2 IncarnationR := ltac:(solve_learnable).
Opaque Zdigits.Z_to_binary.
   Definition execute_final_spec : WpSpec mpredI val val :=
    \arg{statep: ptr} "state" (Vref statep)
    \pre{assumptionsAndUpdates}  statep |-> StateR assumptionsAndUpdates
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{bfeep: ptr} "base_fee_per_gase" (Vref bfeep)
    \prepost{q basefeepergas} bfeep |-> u256R q basefeepergas
    \arg{i preTxState resultp hdr} "" (Vptr resultp)
    \pre{postTxState result} [| (postTxState, result) = stateAfterTransactionAux hdr preTxState i t |]
    \prepost resultp |-> EvmcResultR result
    \arg{benp} "beneficiary" (Vref benp)
    \prepost{benAddr qben} benp |-> addressR qben benAddr
    \pre [| postTxState = applyUpdates assumptionsAndUpdates preTxState |]
    \prepost{preBlockState g} (blockStatePtr assumptionsAndUpdates) |-> BlockState.Rauth preBlockState g preTxState
    \pre [| satisfiesAssumptions assumptionsAndUpdates preTxState |]
    \post{retp}[Vptr retp] Exists assumptionsAndUpdatesFinal,
       retp |-> ReceiptR result ** statep |-> StateR assumptionsAndUpdatesFinal
       ** [| satisfiesAssumptions assumptionsAndUpdatesFinal preTxState |]
       ** [| blockStatePtr assumptionsAndUpdatesFinal = blockStatePtr assumptionsAndUpdates |]
       ** [| indices assumptionsAndUpdatesFinal = indices assumptionsAndUpdates |]
       ** [| (stateAfterTransaction hdr i preTxState t).1 = applyUpdates assumptionsAndUpdatesFinal preTxState |].

Lemma ResultSucRDef {T} (R: T-> _) t : ResultSuccessR R t  -|- o_field CU (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "value_fixme")) |-> R t.
Proof using. Admitted.

cpp.spec 
       "monad::has_error<evmc::Result>(const boost::outcome_v2::basic_result<evmc::Result, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<evmc::Result, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>&)" as has_error with
      (\pre emp (* TODO: fix *)
         \arg{resp} "res" (Vptr resp)
         \prepost{res} resp |->  ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
         \post [Vbool false] emp
      ).

(* TODO: generalize *)
Definition opt_value_or  :=
specify
  {|
    info_name := "std::optional<intx::uint<256u>>::value_or<int>(int&&) const &";
    info_type :=
      tMethod "std::optional<intx::uint<256u>>" QC "intx::uint<256u>" ["int&&"%cpp_type]
  |}
  (λ this : ptr,
     \arg{defp : ptr} "" (Vptr defp)
     \prepost{(q : Qp) (n : N)} defp |-> intR q$m (Z.of_N n)
     \prepost{(q0 : Qp) (hdr : BlockHeader)}
       this |-> libspecs.optionR u256t (u256R q0) q0 (base_fee_per_gas hdr)
     \post{retp : ptr}[Vptr retp]
              retp
              |-> u256R 1 match base_fee_per_gas hdr with
                          | Some x => x
                          | None => n
                          end).
(*
constexpr const value_type &&value() const && { return static_cast<value_type &&>(_value); }
 *)

cpp.spec "monad::value<evmc::Result>(const boost::outcome_v2::basic_result<evmc::Result, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<evmc::Result, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>&)" as result_value with
          (
      \arg{this} "this" (Vptr this)
       \prepost{res} this |-> ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
       \post [Vref (this ,, _field "boost::outcome_v2::value_fixme")] emp).

(*
Definition exec_final :=
  specify
  {|
    info_name :=
        Ninst
        "monad::execute_final(monad::State&, const monad::Transaction&, const evmc::address&, const intx::uint<256u>&, const evmc::Result&, const evmc::address&)"
        [Avalue (Eint 11 "enum evmc_revision")];
    info_type :=
      tFunction (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt")))
        [Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
         Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
         Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])));
         Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))))]
  |} execute_final_spec.
 *)

(* TODO: generalize *)

Definition result_val_contr_name valty :=
  ((Ninst
          (Nscoped (resultn valty)
             (Nctor
                [Trv_ref (Tconst valty);
                 Tnamed (Nscoped (resultn valty) (Nid "value_converting_constructor_tag"))]))
          [Atype valty; Atype "void"])).
(*
#[ignore_errors]
cpp.spec (result_val_contr_name "monad::ExecutionResult")
  as result_val_constr with (fun this:ptr =>
                               \arg{recp} ("recp"%pstring) (Vref recp)
                               \prepost{r} recp |-> ReceiptR r
                               \arg{vtag} ("vtag"%pstring) (Vptr vtag)
                               \post this |-> ResultSuccessR ReceiptR r).
 *)
(*
  cpp.spec (Nscoped (Nscoped resultn (Nid "value_converting_constructor_tag")) (Nctor []))
    as tag_constr with
      (fun (this:ptr) => \post this |-> structR ((Nscoped resultn (Nid "value_converting_constructor_tag"))) (cQp.mut 1)).
  cpp.spec (Nscoped (Nscoped resultn (Nid "value_converting_constructor_tag")) (Ndtor))
    as tag_dtor with
      (fun (this:ptr) => \pre this |-> structR ((Nscoped resultn (Nid "value_converting_constructor_tag"))) (cQp.mut 1)
                          \post emp
      ).
*)  
  cpp.spec (Nscoped ("monad::Receipt") (Ndtor))
    as rcpt_dtor with
      (fun (this:ptr) => \pre{r} this |-> ReceiptR r
                          \post emp
      ).
  (* TODO: generalize *)
  cpp.spec (Nscoped (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
       [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
        Atype
          (Tnamed
             (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
        Atype
          (Tnamed
             (Ninst
                (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                   (Nid "status_code_throw"))
                [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                 Atype
                   (Tnamed
                      (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                         [Atype
                            (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                 Atype "void"]))]) (Ndtor))
    as res_dtor with
      (fun (this:ptr) =>
         \pre{r} this |-> ResultSuccessR EvmcResultR r
           \post emp
      ).
  cpp.spec (Nscoped ("monad::State") (Ndtor))
    as st_dtor with
      (fun (this:ptr) => \pre{au} this |-> StateR au
                          \post emp
      ).
  (* TODO: fix *)
  cpp.spec "boost::outcome_v2::basic_result<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<void, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>::~basic_result()"
    as br_dtor with
      (fun (this:ptr) => \pre this |-> emp
                          \post emp
      ).
  Lemma resultObserve (result_addr:ptr) t: 
    Observe
(reference_to
       "boost::outcome_v2::basic_result<evmc::Result, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<evmc::Result, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>"
       result_addr) (result_addr |-> ResultSuccessR EvmcResultR t).
  Proof using. Admitted.

  cpp.spec "monad::get_max_code_size(const monad::Chain&, unsigned long, unsigned long)"
    as max_code_size with (
        \arg{chainp} "chain" (Vptr chainp)
        \prepost{q c} chainp |-> ChainR q c
        \arg{bn} "number" (Vint bn)
        \arg{ts} "timestamp" (Vint ts)
        \post{maxcs:N} [Vint maxcs] emp
      ).
  
#[global] Instance : LearnEq3 (BlockState.Rauth) := ltac:(solve_learnable).
Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : LearnEq1 ReceiptR := ltac:(solve_learnable).
  #[global] Instance : LearnEq1 EvmcResultR := ltac:(solve_learnable).
  Lemma recObserve (state_addr:ptr) t: 
    Observe (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt"))) state_addr)
            (state_addr |-> ReceiptR t).
  Proof using. Admitted.
  cpp.spec "monad::State::State(monad::BlockState&, monad::Incarnation, const evmc::address&, unsigned long, const intx::uint<256u>&)"
    as StateConstrRelaxed with
  (    fun (this:ptr) =>
      \arg{bsp} "" (Vref bsp)
      \arg{incp} "" (Vptr incp)
      \arg{sender_addrp} "sender_addr" (Vptr sender_addrp)
      \arg{sender_nonce:N} "sender_nonce" (Vint sender_nonce)
      \arg{sender_balp} "sender_balp" (Vptr sender_balp)
      \prepost{qbal sender_bal} sender_balp |-> u256R qbal sender_bal
      \prepost{sender_addr q} sender_addrp |-> addressR q sender_addr
      \prepost{q inc} incp |-> IncarnationR q inc 
      \post Exists au, this |-> StateR au ** [| blockStatePtr au = bsp |]
                   ** (reference_to "monad::State" this) (* convenient but logically redundant *)
                   ** [| relaxed_constructor_init_state sender_addr sender_nonce sender_bal bsp inc au|]).
  
  #[global]  Instance kldsjflsjal q q2 v tx1 (txp:ptr) :
    Learnable
      (txp |-> TransactionR q tx1)
      (txp ,, o_field CU "monad::Transaction::nonce" |-> primR "unsigned long" q2 v)
      [q2= cQp.mut q; v=(Z.of_N (tx_nonce tx1))] := ltac:(solve_learnable).
  Lemma borrow_nonce2 q tx (txp:ptr) :
    (txp |-> TransactionR q tx) |--
   ((txp ,, o_field CU "monad::Transaction::nonce" |-> ulongR (cQp.mut q) (Z.of_N (tx_nonce tx))) -* txp |-> TransactionR q tx) **                             
      ((txp ,, o_field CU "monad::Transaction::nonce" |-> ulongR (cQp.mut q) (Z.of_N (tx_nonce tx)))) .
  Proof using.
    Transparent TransactionR.
    unfold TransactionR. go.
    Opaque TransactionR.
  Qed.
  Definition borrow_nonce2_C := [CANCEL] borrow_nonce2.
  Hint Resolve borrow_nonce2_C: br_opacity.
  cpp.spec (Nscoped "monad::CallTracer"
          (Nctor
             [Tref "const monad::Transaction"]))
    as callTracerConstr with
      (    fun (this:ptr) =>
        \arg{txp} "tx" (Vptr txp)
        \prepost{qt tx} txp |-> TransactionR qt tx
        \post this |-> structR "monad::CallTracer" (cQp.mut 1)).
  cpp.spec "monad::min_balance(const monad::Transaction&)" as minb with
      (
        \arg{txp} "tx" (Vptr txp)
        \prepost{qt tx} txp |-> TransactionR qt tx
        \post{x:ptr} [Vptr x] x |-> u256R 1 (minSenderBalForTx tx)
      ).

  (*
  #[global]  Instance refineInjVint: RefineInj (=) (=) Vint.
  Proof using.
    hnf.
    intros.
    congruence.
  Qed.
  #[global]  Instance refineInjSr: RefineInj (=) (=) (fun x:Z=> x+1)%Z.
  Proof using.
    hnf.
    intros.
    lia.
  Qed.
  #[global]  Instance refineInjSr2: RefineInj (=) (=) (fun x:nat=> Z.of_nat x+1)%Z.
  Proof using.
    hnf.
    intros.
    lia.
  Qed.
*)
  Remove Hints primR_split_C: br_opacity. (* TODO: remove *)
  #[global]  Instance lsfjdlksj q q2 hdr hdr2 (hdrp:ptr):
    learn_exist_interface.Learnable
      (hdrp |-> BheaderR q hdr)
      (hdrp ,, o_field CU "monad::BlockHeader::base_fee_per_gas" |-> libspecs.optionR u256t (u256R q2) q2 (base_fee_per_gas hdr2))
      [q2= cQp.mut q; hdr2=hdr] := ltac:(solve_learnable).
  Transparent BheaderR.
  Lemma borrow_basefee q hdr (hdrp:ptr) :
    let br :=   (hdrp ,, o_field CU "monad::BlockHeader::base_fee_per_gas" |-> libspecs.optionR u256t (u256R q) q (base_fee_per_gas hdr))
    in
    (hdrp |-> BheaderR q hdr) |-- (br -* hdrp |-> BheaderR q hdr) ** br.
  Proof using.
    unfold BheaderR. go.
  Qed.
  Definition borrow_basefee_C := [CANCEL] borrow_basefee.
  Hint Resolve borrow_basefee_C: br_opacity.
      cpp.spec (Ninst
             "monad::execute_final(const monad::Chain&, monad::State&, const monad::BlockHeader&, const monad::Transaction&, const evmc::address&, const intx::uint<256u>&, const evmc::Result&, const evmc::address&)"
             [Avalue (Eint 11 "enum evmc_revision")]) as exec_final_spec with (
    \arg{chainp} "chain" (Vptr chainp)
    \prepost{qchain chain} chainp |-> ChainR qchain chain
    \arg{statep: ptr} "state" (Vref statep)
    \pre{assumptionsAndUpdates}  statep |-> StateR assumptionsAndUpdates
    \arg{hdrp: ptr} "hdr" (Vref hdrp)
    \prepost{qh header} hdrp |-> BheaderR qh header
    \arg{txp} "tx" (Vref txp)
    \prepost{qtx t} txp |-> TransactionR qtx t
    \arg{senderp} "sender" (Vref senderp)
    \prepost{qs} senderp |-> addressR qs (sender t)
    \arg{bfeep: ptr} "base_fee_per_gase" (Vref bfeep)
    \prepost{q basefeepergas} bfeep |-> u256R q basefeepergas
    \arg{i preTxState resultp hdr} "" (Vptr resultp)
    \pre{postTxState result} [| (postTxState, result) = stateAfterTransactionAux hdr preTxState i t |]
    \prepost resultp |-> EvmcResultR result
    \arg{benp} "beneficiary" (Vref benp)
    \pre [| benp = (hdrp ,, o_field CU "monad::BlockHeader::beneficiary") |]
    \pre [| postTxState = applyUpdates assumptionsAndUpdates preTxState |]
    \prepost{preBlockState g} (blockStatePtr assumptionsAndUpdates) |-> BlockState.Rauth preBlockState g preTxState
    \pre [| satisfiesAssumptions assumptionsAndUpdates preTxState |]
    \post{retp}[Vptr retp] Exists assumptionsAndUpdatesFinal,
       retp |-> ReceiptR result ** statep |-> StateR assumptionsAndUpdatesFinal
       ** [| satisfiesAssumptions assumptionsAndUpdatesFinal preTxState |]
       ** [| blockStatePtr assumptionsAndUpdatesFinal = blockStatePtr assumptionsAndUpdates |]
       ** [| indices assumptionsAndUpdatesFinal = indices assumptionsAndUpdates |]
       ** [| (stateAfterTransaction hdr i preTxState t).1 = applyUpdates assumptionsAndUpdatesFinal preTxState |]).
  
  Lemma CR_const : const.CONST1 module "intx::uint<256u>" u256R.
  Proof. Admitted.
  Definition CR_const_C := [CANCEL] CR_const.
  #[local] Hint Resolve CR_const_C : br_opacity.
  #[global] Instance : LearnEq2 BheaderR:= ltac:(solve_learnable).

cpp.spec "boost::outcome_v2::basic_result<monad::ExecutionResult, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<monad::ExecutionResult, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>::basic_result<monad::ExecutionResult, void>(monad::ExecutionResult&&, boost::outcome_v2::basic_result<monad::ExecutionResult, system_error2::errored_status_code<system_error2::detail::erased<long>>, boost::outcome_v2::experimental::policy::status_code_throw<monad::ExecutionResult, system_error2::errored_status_code<system_error2::detail::erased<long>>, void>>::value_converting_constructor_tag)"
  as result_val_constr with (fun this:ptr =>
                               \arg{recp} ("recp"%pstring) (Vref recp)
                               \prepost{r} recp |-> ExecutionResultR r
                               \arg{vtag} ("vtag"%pstring) (Vptr vtag)
                               \post this |-> ResultSuccessR ExecutionResultR r).
cpp.spec "monad::Receipt::Receipt(const monad::Receipt&)"
  as result_val_constr2 with (fun this:ptr =>
                               \arg{recp} ("recp"%pstring) (Vref recp)
                               \prepost{r} recp |-> ReceiptR r
                               \post this |-> ReceiptR r).
cpp.spec "evmc::address::address(const evmc::address&)"
  as addr_copy_constr with (fun this:ptr =>
                               \arg{recp} ("recp"%pstring) (Vref recp)
                               \prepost{q r} recp |-> addressR q r
                               \post this |-> addressR 1 r).
cpp.spec "std::vector<monad::CallFrame, std::allocator<monad::CallFrame>>::vector()" as vector_constr_spec with
    (fun this:ptr =>
       \pre emp
       \post this |-> VectorR "monad::CallFrame" (fun _:unit=>emp) 1 []).
  cpp.spec (Nscoped (Nscoped (resultn "monad::ExecutionResult") (Nid "value_converting_constructor_tag")) (Nctor []))
    as tag_constr with
      (fun (this:ptr) => \post this |-> structR ((Nscoped (resultn "monad::ExecutionResult") (Nid "value_converting_constructor_tag"))) (cQp.mut 1)).
  cpp.spec (Nscoped (Nscoped (resultn "monad::ExecutionResult") (Nid "value_converting_constructor_tag")) (Ndtor))
    as tag_dtor with
      (fun (this:ptr) => \pre this |-> structR ((Nscoped (resultn "monad::ExecutionResult") (Nid "value_converting_constructor_tag"))) (cQp.mut 1)
                          \post emp).
  cpp.spec (Nscoped "monad::ExecutionResult" (Ndtor))
    as execres_dtor with
      (fun (this:ptr) =>
         \pre{r} this |-> ExecutionResultR r
         \post emp
      ).
  cpp.spec (Nscoped "monad::CallTracer" (Ndtor))
    as ct_dtor with
      (fun (this:ptr) =>
         \pre this |-> structR "monad::CallTracer" (cQp.mut 1)
         \post emp
      ).
  cpp.spec (Nscoped "monad::Receipt" (Ndtor))
    as rec_dtor with
      (fun (this:ptr) =>
         \pre{r} this |-> ReceiptR r
         \post emp
      ).
Lemma ExecutionResultRdef t (r: TransactionResult) :
  ExecutionResultR r -|-
    structR "monad::ExecutionResult" (cQp.mut 1)
    ** o_field CU "monad::ExecutionResult::sender" |-> addressR 1 (sender t)
    **  o_field CU "monad::ExecutionResult::receipt" |-> ReceiptR r
    ** o_field CU "monad::ExecutionResult::call_frames" |-> VectorR "monad::CallFrame" (λ _ : (), emp) 1 [].
Proof using. Admitted.
Opaque VectorR.
  Instance: LearnEq1 ExecutionResultR := ltac:(solve_learnable).
  Opaque _nonce. (* o/w simpl hangs. TODO: move up *)
  Opaque _balance.
  Set Printing Coercions.


  Definition wp_init_implicit_B := [BWD] wp_init_implicit.
  Hint Resolve wp_init_implicit_B: br_opacity. (* TODO: investigagte why it is not already in automation *)
  #[global] Instance lsfjdlksj2 q q2 hdr (hdrp:ptr) v:
    learn_exist_interface.Learnable
      (hdrp |-> BheaderR q hdr)
      (hdrp ,, o_field CU "monad::BlockHeader::number" |-> primR "unsigned long" q2 v)
      [q2= cQp.mut q; v = number hdr] := ltac:(solve_learnable).
  Lemma borrow_number (q:Qp) hdr (hdrp:ptr) :
    let br := hdrp ,, o_field CU "monad::BlockHeader::number" |-> primR "unsigned long" (cQp.mut q) (number hdr)
    in
    (hdrp |-> BheaderR q hdr) |-- (br -* hdrp |-> BheaderR q hdr) ** br.
  Proof using.
    simpl.
    unfold BheaderR. go.
  Qed.
  Definition borrow_number_C := [CANCEL] borrow_number.
  Hint Resolve borrow_number_C: br_opacity.
    Definition observeResult r t := @observe_fwd _ _ _ (resultObserve r t).
    Hint Resolve observeResult : br_opacity.

Ltac slautot rw := go; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); rw; try (erewrite take_S_r;[| eauto;fail]))
  then slautot rw  else idtac.

Ltac slauto := slautot idtac. (* try rewrite left_id; *)

 Definition recObserveF s t := @observe_fwd _ _ _ (recObserve s t) .
Hint Resolve recObserveF: br_opacity.

End with_Sigma.
  Hint Resolve observeStateF : br_opacity.
  Hint Resolve borrow_nonce2_C: br_opacity.
  Hint Resolve borrow_basefee_C: br_opacity.
  #[local] Hint Resolve CR_const_C : br_opacity.
  Hint Resolve wp_init_implicit_B: br_opacity. (* TODO: investigagte why it is not already in automation *)
  Hint Resolve borrow_number_C: br_opacity.
Hint Resolve observeResult : br_opacity.
Hint Resolve recObserveF: br_opacity.
(*
  Lemma prf: denoteModule module
             ** rec_dtor
             ** ct_dtor
             ** execres_dtor
             ** tag_constr
             ** tag_dtor
             ** vector_constr_spec
             ** result_val_constr
             ** result_val_constr2
             ** addr_copy_constr
             ** (opt_reconstr TransactionResult resultT)
             ** minb
             ** callTracerConstr
             ** wait_for_promise
             ** destrop
             ** (destr_res (Tnamed "monad::ExecutionResult") ExecutionResultR) (* is this needed? *)
             ** destr_u256
             ** (has_value "evmc::address" evm.address)
             ** (value "evmc::address" evm.address)
             ** get_chain_id
             ** validate_spec
             ** try_op_has_val
             ** destr_outcome_overload
             ** incarnation_constr
             ** max_code_size
             ** StateConstrExact
             ** StateConstrRelaxed
(*             ** set_original_nonce_spec *)
             ** execute_impl2
             ** destr_incarnation
             ** can_merge
             ** opt_value_or
             ** has_error
             ** result_value
             ** exec_final_spec
             ** exec_specs.merge
(*             ** result_val_constr *)
(*             ** tag_constr *)
(*             ** tag_dtor *)
             ** rcpt_dtor
             ** res_dtor
             ** st_dtor
             ** br_dtor
             |-- ext1.
Proof using MODd.
  verify_spec'.
  hidePost.
  go; try (ego; fail).
  Transparent BheaderR.
  unfold BheaderR.
  go.
  iExists (_:nat). go. (* this manual intervention should not be needed. likely a bug in Refine1, reported to bluerock *)
  foldr BheaderR BheaderR.
  go.
  Transparent libspecs.optionR.
  simpl in *.
  go.
  unfold libspecs.optionR. go.
  (* TODO: switch to NOOPCALLTRACER. this spec is garbage *)

  unfold relaxed_constructor_init_state in H.
  forward_reason. 
  rewrite Hrr. simpl.
  progress autorewrite with syntactic.
  iExists true.
  slauto.
  iExists preBlockState. (* dummy as we are in the speculative case where this is not used *)
  slauto.
  wp_if. (* case analysis on the result of can_merge *)
  {
    intros.
    slauto.
    progress applyPHyp.
    repeat (iExists _). 
     match goal with
    | H:context[stateAfterTransactionAux ?a1 ?b1 ?c1 ?d1] |- context[stateAfterTransactionAux ?a2 ?b2 ?c2 ?d2] => 
        unify a1 a2; unify b1 b2; unify c1 c2; unify d1 d2;
        remember (stateAfterTransactionAux a1 b1 c1 d1) as saf
    end.
 (*   rename result into resultOld. *)
    destruct saf as [smid result].
    simpl in *.
    progress go.
    rewrite ResultSucRDef.
    progress go.
    forward_reason.
    ren_hyp au StateM.
    subst.
    Forward.rwHyps.
    go.
    rewrite <- wp_const_const_delete.
    wapplyObserve recObserve. eagerUnifyU.
    (* iAssert (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt"))) _x_1) as  "#?"%string;[admit|]. *)
    go.
(*    unshelve rewrite <- wp_init_implicit. *)
    go.
    setoid_rewrite ExecutionResultRdef at 1.
    go.
    rewrite <- wp_const_const_delete.
    go.
    unhideAllFromWork.
    setoid_rewrite ResultSucRDef.
(*    Remove Hints borrow_basefee_C: br_opacity. *)
    go.
    iClear "#"%string.
    match goal with
    | H: _.1 = applyUpdates _ _ |- _ => revert H
    end.
    unfold stateAfterTransaction.
    rewrite <- Heqsaf.
    go.
    rewrite ResultSucRDef.
    work.
  }
  {
(*    rename result_addr into result_addr_del.
    rename state_addr into state_addr_del. *)
    slauto.
    iExists (_:nat). (* rename call_tracer_addr into call_tracer_addr2. *) slauto. (* this manual intervention should not be needed. likely a bug in Refine1, reported to bluerock *)
(*  run1.
  wapplyObserve stateObserve.
  progress eagerUnifyU.
  slauto.
  Transparent TransactionR.
  progress unfold TransactionR.
  slauto.

  Transparent libspecs.optionR.
  slauto1.
  Transparent set_original_nonce.
  unfold set_original_nonce in *.
  simpl in *.
  autorewrite with syntactic.
(*   rewrite lookup_empty in H. *)
  forward_reason. subst.
  go. subst. go.
  unfold BheaderR. go.
  unfold TransactionR. go. *)
    iExists false.
    slauto.
(*  do 3 (iExists _). 
  eagerUnifyU.
  run1.
    wapplyObserve @resultObserve. eagerUnifyU.
    slauto.
    go.
    repeat (iExists _).
    eagerUnifyU.
    slauto.
    rewrite <- wp_const_const_delete. 
    slauto.
    go.
    unfold TransactionR.
    go. *)
    use_wand_no_assert.
 Definition recObserveF s t := @observe_fwd _ _ _ (recObserve s t) .
Hint Resolve recObserveF: br_opacity.
    rewrite ResultSucRDef.
    go.
    repeat (iExists _). eagerUnifyC.
    match goal with
    | H:context[stateAfterTransactionAux ?a1 ?b1 ?c1 ?d1] |- context[stateAfterTransactionAux ?a2 ?b2 ?c2 ?d2] => 
        unify a1 a2; unify b1 b2; unify c1 c2; unify d1 d2;
        remember (stateAfterTransactionAux a1 b1 c1 d1) as saf; destruct saf as [smid result]
    end.

    Forward.forward_reason.
    Forward.rwHyps. go.
    rewrite <- wp_const_const_delete.
    go.
    setoid_rewrite ExecutionResultRdef at 1.
    go.
    rewrite <- wp_const_const_delete.
    go.
    setoid_rewrite ResultSucRDef.
    unhideAllFromWork.
    go.
    iClear "#"%string.
    autorewrite with syntactic in *.
    match goal with
    | H: _.1 = applyUpdates _ _ |- _ => revert H
    end.
    unfold stateAfterTransaction.
    repeat rewrite <- Heqsaf.
    go.
    rewrite ResultSucRDef. go.
}
Qed. *)
