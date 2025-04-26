Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.exb.
Require Import monad.proofs.exec_specs.


Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : exb.module ⊧ CU}.

  Set Nested Proofs Allowed.
  Set Printing Coercions.
  
  cpp.spec (Nscoped 
              (Nscoped (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) (Nanon 0)) (Ndtor))  as exlamdestr inline.
      
Lemma prf: denoteModule module
             ** (opt_reconstr TransactionResult resultT)
             ** tvector_spec
             ** reset_promises
             ** (fork_taskg (Nscoped (Ninst "monad::execute_transactions(const monad::Block&, monad::fiber::PriorityPool&, const monad::Chain&, const monad::BlockHashBuffer&, monad::BlockState &)" [Avalue (Eint 11 "enum evmc_revision")]) (Nanon 0)))
             ** vector_op_monad
             ** recover_sender
             ** wait_for_promise
             ** set_value
             ** destrop
             ** ext1
             ** (destr_res (Tnamed "monad::ExecutionResult") ExecutionResultR)
             |-- exect.
Proof using MODd.
  verify_spec'.
  name_locals.
  hideRhs.
  hideP ff.
  Transparent VectorR.
  unfold BlockR, VectorR.
  work.
  ren_hyp vectorbase ptr.
  rewrite (arrLearn2 vectorbase).
  rewrite (arrLearn2 (_global "monad::senders")).
  rewrite (arrLearn2 (_global "monad::results")).
  rewrite parrLearn2.
  unhideAllFromWork.
  slauto.
  iExists unit.
  go.
  (* TODO: construct the iExists arg below programmatically, rather than writing by hand *)
  iExists  (fun i _ =>
    let '(actual_final_state, receipts) := stateAfterTransactions (header block) preBlockState (take i (transactions block)) in
    ((_global "monad::results" |-> arrayR oResultT (fun r => libspecs.optionR resultT (ResultSuccessR ExecutionResultR) 1 (Some r)) receipts)
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_hash_bufferp |-> BlockHashBufferR (qbuf*/(N_to_Qp (1+ lengthN (transactions block)))) buf))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (chainp |-> ChainR (qchain*/(N_to_Qp (1+ lengthN (transactions block)))) chain))
     ** _global "monad::senders" |->
          arrayR
            (Tnamed "std::optional<evmc::address>")
            (fun t=> optionAddressR qs (Some (sender t)))
            (take i (transactions block))

     ** (_global "monad::promises" |->
            parrayR
              (Tnamed "boost::fibers::promise<void>")
              (fun i t => PromiseUnusableR)
              ((map (fun _ => ()) (take i (transactions block)))))
     ** ([∗ list] _ ∈ (take i (transactions block)),  blockp ,, o_field CU (Nscoped (Nscoped (Nglobal (Nid "monad")) (Nid "Block")) (Nid "header"))
      |-> BheaderR (qb*/(N_to_Qp (1+ lengthN (transactions block)))) (header block))
     ** ([∗ list] _ ∈ (take i (transactions block)),  (block_statep |-> BlockState.Rfrag preBlockState (qf*/(N_to_Qp (1+ lengthN (transactions block)))) g))
     **  vectorbase
          |-> arrayR (Tnamed (Nscoped (Nglobal (Nid "monad")) (Nid "Transaction"))) (λ t0 : Transaction, TransactionR qb t0)
          (take i (transactions block)))
      ** block_statep |-> BlockState.Rauth preBlockState g actual_final_state
           ).
  go.
  unfold lengthN in *.
  autorewrite with syntactic.
  go.
  autorewrite with syntactic.
  go.
  hideP p.
  setoid_rewrite sharePromise.
  rewrite parrayR_sep. go.
  IPM.perm_left ltac:(fun L n =>
                        match L with
                        | context[PromiseProducerR] =>  iRevert n
                        end
                     ).
  hideLhs.
  rewrite unit_snoc_cons.
  unhideAllFromWork.
  iIntros "?"%string.
  rewrite parrayR_cons.
  autorewrite with syntactic.
  go.
  autorewrite with syntactic.
  go.
  rewrite parrayR_nil. go.
  autorewrite with syntactic.
  go.
  hideP p.
  rewrite parrayR_app1.
  go.
  autorewrite with syntactic.
  (* for loop *)
  name_locals.
  assert (exists ival:nat, ival=0) as Hex by (eexists; reflexivity).
  destruct Hex as [ival Hex].
  rewrite -> (generalize_arrayR_loopinv ival (_global "monad::senders")); [| assumption].
  rewrite (generalize_arrayR_loopinv ival (_global "monad::results")); [| assumption].
  rewrite -> (generalize_arrayR_loopinv ival vectorbase); [| assumption].
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises")); [| assumption].
  rewrite (generalize_parrayR_loopinv ival (_global "monad::promises" ,, _)); [| assumption].
  rewrite -> @bhb_splitl_loopinv with (i:=ival) (l:=transactions block) by assumption.
  rewrite -> @BlockState.split_frag_loopinv with (i:=ival) (l:=transactions block) by assumption.
  rewrite -> @ChainR_split_loopinv with (i:=ival) (l:=transactions block) by assumption.
  rewrite -> @header_split_loopinv with (i:=ival) (l:=transactions block) by assumption.
  assert (Vint 0 = Vnat ival) as Hexx by (subst; auto).
  rewrite Hexx. (* TODO: use a more precise pattern *)
  clear Hexx.
  assert (ival <= length (transactions block)) as Hle by (subst; lia).
  clear Hex.
  genOver ival.
  wp_for (fun _ => emp).
  go.
  unhideAllFromWork.
  slauto.
  wp_if.
  { (* loop condition is true and thus the body runs. so we need to reistablish the loopinv *)
    slauto.
    ren_hyp ival nat.
    repeat rewrite skipn_map.
    applyToSomeHyp @drop_S2.
    match goal with
      [H:_ |- _] => destruct H as [tri Htt]; destruct Htt as [Httl Httr]
    end.
    repeat rewrite Httr.
    go.
    iExists (N.of_nat ival). (* automate this using some Refine1 hint *)
    slauto.
    aggregateRepPieces a.
    slauto.
    repeat rewrite -> arrayR_cons.
    repeat rewrite -> parrayR_cons.
    go.
    autorewrite with syntactic.
    progress repeat rewrite o_sub_sub.
    simpl.
    progress go.
    IPM.perm_left ltac:(fun L n =>
      match L with
      |   _ |-> BlockHashBufferR _ _ => iRevert n
      end
      ).
    IPM.perm_left ltac:(fun L n =>
      match L with
      |   _ |-> BlockState.Rfrag _ _ _ => iRevert n
      end
      ).
    repeat IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | _ .[_ ! Z.of_nat ival] |-> _ => iRevert n
      end).
    IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | _ .[_ ! _] |-> PromiseProducerR _ _ => iRevert n
      end).
    IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | chainp |-> _ => iRevert n
      end).
    IPM.perm_left_spatial  ltac:(fun L n =>
      match L with
      | _ |-> BheaderR _ _ => iRevert n
      end).
    repeat rewrite bi.wand_curry.
    match goal with
        [ |-environments.envs_entails _ (?R -* _)] => iIntrosDestructs; iExists R
    end.
    go.
    iSplitL ""%string.
    {
      unfold taskOpSpec.
      verify_spec'.
      slauto.
      match goal with
        |- context[stateAfterTransactions ?a ?b (take ival ?l)] => remember (stateAfterTransactions a b (take ival l)) as sabc
      end.
      destruct sabc.
      simpl in *.
      go.
      unshelve (do 2 iExists _; eagerUnifyU);[].
      slauto.
      match goal with
        |- context[stateAfterTransaction ?a ?b ?c ?d] => remember (stateAfterTransaction a b c d) as sat
      end.
      destruct sat.
      simpl in *.
      slauto.
      replace (1+ival)%Z with (ival+1)%Z  by lia.
      go.
      rewrite stateAfterTransactionsC.
      rewrite <- Heqsabc.
      simpl.
      autorewrite with syntactic.
      rewrite <- Heqsat.
      simpl.
      go.
      repeat rewrite arrayR_snoc.
      go.
      autorewrite with syntactic.
      go.
      repeat rewrite big_opL_snoc.
      go.
      applyToSomeHyp rect_len.
      autorewrite with syntactic in *.
      go.
      rewrite map_app.
      simpl.
      subst.
      rewrite parrayR_app1.
      go.
      autorewrite with syntactic.
      go.
    }
    {
      slauto.
      iExists (1+ival).
      unfold lengthN in *.
      go.
      replace (Z.of_nat ival + 1)%Z with (Z.of_nat (S ival)); try lia.
      go.
      progress repeat rewrite Nat.add_succ_r.
      progress setoid_rewrite Nat.add_succ_r.
      go.
      repeat rewrite skipn_map.
      go.
      icancel (cancel_at (_global "monad::promises"  ,, _)).
      {
        repeat f_equiv; try 
                          apply Nat.add_succ_r.
      }
      autorewrite with syntactic.
      go.
      normalize_ptrs.
      replace (1+ Z.of_nat ival + 1)%Z with (1+ Z.of_nat (S ival))%Z; try lia.
      icancel (cancel_at (_global "monad::promises"  ,, _)).
      {
        repeat f_equiv; try 
                          apply Nat.add_succ_r.
      }
      go.
    }
  }
  { (* loop condition is false *)
    slauto.
    unfold lengthN in *.
    ren_hyp ival nat.
    assert (ival=length(transactions block))  by lia.
    subst.
    slauto.
    autorewrite with syntactic.
    rewrite drop_ge;[|autorewrite with syntactic; lia].
    go.
    repeat rewrite arrayR_nil.
    repeat rewrite parrayR_nil.
    go.
(*    rename i_addr into i1_addr. *)
    simpl in *.
    go.
    remember (stateAfterTransactions (header block) preBlockState (transactions block)) as abc.
    destruct abc.
    go.
    hideLhs.
    rewrite -> @ChainR_split_loopinv with (i:=0) (l:=transactions block) by reflexivity.
    rewrite -> @header_split_loopinv with (i:=0) (l:=transactions block) by reflexivity.
    rewrite -> @bhb_splitl_loopinv with (i:=0) (l:=transactions block) by reflexivity.
    rewrite -> @BlockState.split_frag_loopinv with (i:=0) (l:=transactions block) by reflexivity.
    unhideAllFromWork. go.
    autorewrite with syntactic.
    repeat rewrite _at_big_sepL. go.
    rewrite parrayR_app1. go.
    autorewrite with syntactic. go.
  }
Qed.
End with_Sigma.

