Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bedrock.auto.invariants.
Require Import bedrock.auto.cpp.proof.

Require Import bedrock.auto.cpp.tactics4.
Require Import monad.asts.ext.
Require Import monad.proofs.exec_specs.

Opaque libspecs.optionR.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : ext.module ⊧ CU}.

  Set Nested Proofs Allowed.
  Set Printing Coercions.
  #[global] Instance learnOpt a b c d e a1 b1 c1 d1 e1: Learnable (@libspecs.optionR _ _ _ _ a b c d e) (@libspecs.optionR _ _ _ _ a1 b1 c1 d1 e1) [a=a1] := ltac:(solve_learnable).

  cpp.spec (
          (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("execute_impl")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain")))); "unsigned long"%cpp_type;
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockState")));
                    Tref
                      (Tnamed
                         (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "fibers")) (Nid "promise"))
                            [Atype "void"]))]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])) as fff inline.

  cpp.spec  (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("static_validate_transaction")
                   [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref
                      (Tconst
                         (Tnamed
                            (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
                               [Atype (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))])));
                    Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])));
                    "unsigned long"%cpp_type
             ]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))]) as validate_spec with
      (
        \arg{txp} "tx" (Vref txp)
        \prepost{qtx t} txp |-> TransactionR qtx t
        \arg{basefeep} "base" (Vref basefeep)
        \arg{chainidp} "chainid" (Vref chainidp)
        \arg{maxcodesize} "maxcodesize" (Vint maxcodesize)
       \post{retp} [Vptr retp] (reference_to
    (Tnamed
       (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
          [Atype "void";
           Atype
             (Tnamed
                (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                   [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
           Atype
             (Tnamed
                (Ninst
                   (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                      (Nid "status_code_throw"))
                   [Atype "void";
                    Atype
                      (Tnamed
                         (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                            [Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                    Atype "void"]))]))
    retp ∗
 retp |-> emp)
    ).
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
          (Ninst
             (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2"))
                (Nfunction function_qualifiers.N ("try_operation_has_value")
                   [Tref
                      (Tnamed
                         (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                            [Atype "void";
                             Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                     [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                             Atype
                               (Tnamed
                                  (Ninst (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy")) (Nid "status_code_throw"))
                                     [Atype "void";
                                      Atype
                                        (Tnamed
                                           (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                              [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                      Atype "void"]))]));
                    Tnamed (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "detail")) (Nid "has_value_overload"))]))
             [Atype
                (Tref
                   (Tnamed
                      (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                         [Atype "void";
                          Atype
                            (Tnamed
                               (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                  [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                          Atype
                            (Tnamed
                               (Ninst (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy")) (Nid "status_code_throw"))
                                  [Atype "void";
                                   Atype
                                     (Tnamed
                                        (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                           [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                   Atype "void"]))])));
              Atype "bool"]) as try_op_has_val with
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
Require Import bedrock.prelude.lens.
    #[only(lens)] derive AssumptionsAndUpdates.
    #[only(lens)] derive block.block_account.


    Import LensNotations.
    #[local] Open Scope lens_scope.

    Definition relaxed_constructor_init_state (sender_addr: evm.address) (sender_nonce sender_balance: N)  (bsp: ptr) (ind: Indices) (sf: AssumptionsAndUpdates) : Prop :=
      exists senderAc, senderAc .^ _nonce = sender_nonce /\ senderAc .^ _balance = sender_balance /\
        sf =
          {|
            relaxedValidation:= true;
            newStates:= ∅;
            original := <[sender_addr := (senderAc, {| balance := true; nonce :=false |}) ]> ∅;
            blockStatePtr := bsp;
            indices:= ind;
          |}.


    Fixpoint isFunctionNamed2 (fname: ident) (n:name): bool :=
    match n with
    | Nglobal  (Nfunction _ i _) => bool_decide (i=fname)
    | Ninst nm _ => isFunctionNamed2 fname nm
    | Nscoped _ (Nfunction _ i _) => bool_decide (i=fname)
    | _ => false
    end.

    Definition u256t : type :=
      Tnamed ((Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])).
  (*cpp.spec (Nscoped "monad::State"
          (Nctor
             [Tref "monad::BlockState";
              Tconst "monad::Incarnation";
              Tref (Tconst "evmc::address");
              Tconst ("unsigned long long"%cpp_type);
              Tref (Tconst u256t)
              
    ]))
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
      \post Exists au, this |-> StateR au ** [| relaxed_constructor_init_state sender_addr sender_nonce sender_bal bsp inc au|]).
  *)  
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
      \post this |-> StateR {| blockStatePtr := bsp; indices:= inc; original := ∅; newStates:= ∅ ; relaxedValidation := true|}).
  
  Compute (findBodyOfFnNamed2 module (isFunctionNamed2 "set_original_nonce_and_balance")).
  (*
  cpp.spec ((Nscoped
               (Nscoped (Nglobal (Nid "monad")) (Nid "State"))
               (Nfunction function_qualifiers.N ("set_original_nonce_and_balance")
                  [Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address")))); Tconst ("unsigned long"%cpp_type)])))
  as set_original_nonce_spec with
    (fun this:ptr =>
       \arg{addrp} "a" (Vptr addrp)
       \arg{nonce} "a" (Vint nonce)
       \prepost{addr q} addrp |-> addressR q addr
       \pre{au} this |-> StateR au
       \post Exists auf, this |-> StateR auf **
                [| set_original_nonce addr (Zdigits.Z_to_binary 256 nonce) au auf |]
    ). *)
#[global] Instance : LearnEq2 (addressR) := ltac:(solve_learnable).
#[global] Instance : LearnEq1 (StateR) := ltac:(solve_learnable).

cpp.spec (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("execute_impl2")
                   [
                     Tref ((Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "CallTracerBase"))));
                     Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Chain"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHeader"))));
                    Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "BlockHashBuffer"))));
                    Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State")))]))
             [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))])
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

Ltac applyPHyp :=
  let Hbb := fresh "autogenhyp" in
  match goal with
    [ Ha:?T, Hb: _ |- _] =>
      let Tt := type of T in
      unify Tt Prop;
      pose proof Hb as Hbb; apply Ha in Hbb
  end.
Lemma ResultSucRDef {T} (R: T-> _) t : ResultSuccessR R t  -|- o_field CU (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "value_fixme")) |-> R t.
Proof using. Admitted.
Ltac slauto2 := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail); try autorewrite with syntactic)
  then slauto2  else idtac.
Ltac slauto1 := go; try name_locals; tryif progress(try (ego; eagerUnifyU; go; fail); try (apply False_rect; try contradiction; try congruence; try nia; fail))
  then slauto1  else idtac.
  (* TODO: generalize over evmc::Result *)
cpp.spec 
       (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("has_error")
                   [Tref
                      (Tconst
                         (Tnamed
                            (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                               [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                                Atype
                                  (Tnamed
                                     (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                        [Atype
                                           (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
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
                                                    (Tnamed
                                                       (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                         Atype "void"]))])))]))
             [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))]) as has_error with
      (\pre emp (* TODO: fix *)
         \arg{resp} "res" (Vptr resp)
         \prepost{res} resp |->  ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
         \post [Vbool false] emp
    ).
Definition opt_value_or  :=
specify
  {|
    info_name :=
      Ninst
        (Nscoped
           (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
              [Atype (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))])
           (Nfunction function_qualifiers.Ncl ("value_or") ["int&&"%cpp_type]))
        [Atype "int"];
    info_type :=
      tMethod
        (Ninst (Nscoped (Nglobal (Nid "std")) (Nid "optional"))
           [Atype (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))])
        QC (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")]))
        ["int&&"%cpp_type]
  |}
      ( fun this =>
          \arg{defp} "" (Vptr defp)
           \prepost{q (n:N)} defp |-> intR (cQp.mut q) n
      \prepost{q hdr} this |-> libspecs.optionR u256t (u256R q) q (base_fee_per_gas hdr)
      \post{retp} [Vptr retp] retp |-> u256R 1 (match (base_fee_per_gas hdr) with | Some x => x | None => n end)
    ).

(*
constexpr const value_type &&value() const && { return static_cast<value_type &&>(_value); }
*)
cpp.spec (Ninst
             (Nscoped (Nglobal (Nid "monad"))
                (Nfunction function_qualifiers.N ("value")
                   [Tref
                      (Tconst
                         (Tnamed
                            (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
                               [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")));
                                Atype
                                  (Tnamed
                                     (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                                        [Atype
                                           (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
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
                                                    (Tnamed
                                                       (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                                         Atype "void"]))])))]))
             [Atype (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))]) as result_value with
    (
      \arg{this} "this" (Vptr this)
       \prepost{res} this |-> ResultSuccessR EvmcResultR (* TODO: EvmcResultR *) res
       \post [Vref (this ,, _field "boost::outcome_v2::value_fixme")] emp).


Definition exec_final :=
  specify
  {|
    info_name :=
      Ninst
        (Nscoped (Nglobal (Nid "monad"))
           (Nfunction function_qualifiers.N ("execute_final")
              [Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
               Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
               Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])));
               Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))))]))
        [Avalue (Eint 11 (Tenum (Nglobal (Nid "evmc_revision"))))];
    info_type :=
      tFunction (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt")))
        [Tref (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))));
         Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))));
         Tref (Tconst (Tnamed (Ninst (Nscoped (Nglobal (Nid "intx")) (Nid "uint")) [Avalue (Eint 256 "unsigned int")])));
         Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "Result")))); Tref (Tconst (Tnamed (Nscoped (Nglobal (Nid "evmc")) (Nid "address"))))]
  |} execute_final_spec.

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
  cpp.spec (Nscoped (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
       [Atype "void";
        Atype
          (Tnamed
             (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
        Atype
          (Tnamed
             (Ninst
                (Nscoped (Nscoped (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "experimental")) (Nid "policy"))
                   (Nid "status_code_throw"))
                [Atype "void";
                 Atype
                   (Tnamed
                      (Ninst (Nscoped (Nglobal (Nid "system_error2")) (Nid "errored_status_code"))
                         [Atype
                            (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                 Atype "void"]))]) (Ndtor))
    as br_dtor with
      (fun (this:ptr) => \pre this |-> emp
                          \post emp
      ).
  Lemma resultObserve (result_addr:ptr) t: 
    Observe
(  reference_to
    (Tnamed
       (Ninst (Nscoped (Nscoped (Nglobal (Nid "boost")) (Nid "outcome_v2")) (Nid "basic_result"))
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
                            [Atype (Tnamed (Ninst (Nscoped (Nscoped (Nglobal (Nid "system_error2")) (Nid "detail")) (Nid "erased")) [Atype "long"]))]));
                    Atype "void"]))]))
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
  
  Lemma stateObserve (state_addr:ptr) t: 
    Observe (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "State"))) state_addr)
            (state_addr |-> StateR t).
  Proof using. Admitted.
#[global] Instance : LearnEq3 (BlockState.Rauth) := ltac:(solve_learnable).
Existing Instance UNSAFE_read_prim_cancel.
  #[global] Instance : LearnEq1 ReceiptR := ltac:(solve_learnable).
  #[global] Instance : LearnEq1 EvmcResultR := ltac:(solve_learnable).
  Lemma recObserve (state_addr:ptr) t: 
    Observe (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt"))) state_addr)
            (state_addr |-> ReceiptR t).
  Proof using. Admitted.
  cpp.spec (Nscoped "monad::State"
          (Nctor
             [Tref "monad::BlockState";
              Tnamed "monad::Incarnation";
              Tref (Tconst "evmc::address");
              ("unsigned long"%cpp_type);
              Tref (Tconst u256t)
              
    ]))
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
      \post Exists au, this |-> StateR au ** [| relaxed_constructor_init_state sender_addr sender_nonce sender_bal bsp inc au|]).
  
  Lemma prf: denoteModule module
             ** (opt_reconstr TransactionResult resultT)
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
             ** exec_final
             ** merge
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
  go; try (ego; fail).
  Transparent BheaderR.
  unfold BheaderR.
  slauto.
  rewrite <- wp_const_const_delete.
  go.
  unshelve rewrite <- wp_init_implicit.
  go.
  iExists i. (* TODO: add a REfine 1 hint to avoid needing this *)
  go.
  (* need spec for min_balance *)
  wapplyObserve stateObserve.
  eagerUnifyU.
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
  rewrite lookup_empty in H.
  forward_reason. subst.
  go. subst. go.
  unfold BheaderR. go.
  unfold TransactionR. go.
  iExists true.  slauto.
  do 3 (iExists _). iExists preBlockState. (* dummy as we are in the speculative case where this is not used *)
  eagerUnifyU. slauto.
  slauto.
  wp_if.
  {
    intros.
    wapplyObserve @resultObserve. eagerUnifyU.
    slauto.
    slauto.
    go.
    repeat (iExists _).
    eagerUnifyU.
    slauto.
    rewrite <- wp_const_const_delete.
    slauto.
    go.
    unfold TransactionR.
    go.
    progress applyPHyp.
    repeat (iExists _). eagerUnifyC.
    match goal with
    | H:context[stateAfterTransactionAux ?a1 ?b1 ?c1 ?d1] |- context[stateAfterTransactionAux ?a2 ?b2 ?c2 ?d2] => 
        unify a1 a2; unify b1 b2; unify c1 c2; unify d1 d2;
        remember (stateAfterTransactionAux a1 b1 c1 d1) as saf
    end.
    
    rename result into resultOld.
    destruct saf as [smid result].
    simpl in *.
    go.
    eagerUnifyU.
    
    rewrite ResultSucRDef.
    go.
    eagerUnifyC.
    forward_reason.
    ren_hyp au AssumptionsAndUpdates.
    subst.
    eagerUnifyC.
    go.
    rewrite <- wp_const_const_delete.
    go.
    rewrite <- wp_const_const_delete.
    go.

    wapplyObserve recObserve. eagerUnifyU.
    (* iAssert (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt"))) _x_1) as  "#?"%string;[admit|]. *)
    go.
    unshelve rewrite <- wp_init_implicit.
    go.
    setoid_rewrite ResultSucRDef.
    go.
    repeat (iExists _). eagerUnifyC. go.

    (* too many temps need to be destructed just before returning *)

    go.
    rewrite <- wp_const_const_delete.
    go.
    go.
    setoid_rewrite ResultSucRDef.
    go.
    go.
    autorewrite with syntactic in *.
    iClear "#"%string.
    match goal with
    | H: _.1 = applyUpdates _ _ |- _ => revert H
    end.
    unfold stateAfterTransaction.
    rewrite <- Heqsaf.
    go.
    rewrite ResultSucRDef. go.
}
{
  rename result_addr into result_addr_del.
  rename state_addr into state_addr_del.
  slauto.
  iExists i. (* TODO: add a REfine 1 hint to avoid needing this *)
  run1.
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
  unfold TransactionR. go.
  iExists false.  slauto.
  do 3 (iExists _). 
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
    go.
    repeat (iExists _). eagerUnifyC.
    rename result into resultOld.
    match goal with
    | H:context[stateAfterTransactionAux ?a1 ?b1 ?c1 ?d1] |- context[stateAfterTransactionAux ?a2 ?b2 ?c2 ?d2] => 
        unify a1 a2; unify b1 b2; unify c1 c2; unify d1 d2;
        remember (stateAfterTransactionAux a1 b1 c1 d1) as saf; destruct saf as [smid result]
    end.

    simpl in *.
    go.
    eagerUnifyU.
    
    rewrite ResultSucRDef.
    go.
    eagerUnifyC.
    forward_reason.
    ren_hyp au AssumptionsAndUpdates.
    subst.
    Forward.rwHyps.
    eagerUnifyC.
    go.
    rewrite <- wp_const_const_delete.
    go.
    rewrite <- wp_const_const_delete.
    go.

    wapplyObserve recObserve. eagerUnifyU.
    (* iAssert (reference_to (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Receipt"))) _x_1) as  "#?"%string;[admit|]. *)
    go.
    unshelve rewrite <- wp_init_implicit.
    go.
    setoid_rewrite ResultSucRDef.
    go.
    repeat (iExists _). eagerUnifyC. go.

    (* too many temps need to be destructed just before returning *)

    go.
    rewrite <- wp_const_const_delete.
    go.
    go.
    setoid_rewrite ResultSucRDef.
    go.
    go.
    autorewrite with syntactic in *.
    iClear "#"%string.
    match goal with
    | H: _.1 = applyUpdates _ _ |- _ => revert H
    end.
    unfold stateAfterTransaction.
    rewrite <- Heqsaf.
    go.
    rewrite ResultSucRDef. go.
}
Qed.

End with_Sigma.
