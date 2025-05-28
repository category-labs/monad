Require Import monad.proofs.misc.
Require Import monad.proofs.libspecs.
Require Import monad.proofs.evmopsem.
Import linearity.
Require Import bluerock.auto.invariants.
Require Import bluerock.auto.cpp.proof.

Require Import bluerock.auto.cpp.tactics4.
Require Import monad.asts.block_state_cpp.
Require Import monad.proofs.exec_specs.

Opaque libspecs.optionR.

Section with_Sigma.
  Context `{Sigma:cpp_logic} {CU: genv}.
           (*   hh = @has_own_monpred thread_info _Σ fracR (@cinv_inG _Σ (@cpp_has_cinv thread_info _Σ Sigma)) *)
  Context  {MODd : ext.module ⊧ CU}.

  (*
  Compute (findBodyOfFnNamed2 module (isFunctionNamed2 "fix_account_mismatch")).
   *)

  Definition AccountStateR (q:Qp) (s: evm.account_state) : Rep. Proof. Admitted.
  Print addressR.
  cpp.spec "monad::BlockState::fix_account_mismatch(monad::State&, const evmc::address&, monad::AccountState&, const std::optional<monad::Account>&) const" as fix_spec with (fun this:ptr =>
   \prepost{preBlockState g au actualPreTxState} (blockStatePtr au) |-> BlockState.Rauth preBlockState g actualPreTxState
   \pre [| blockStatePtr au = this |]
   \arg{statep: ptr} "state" (Vref statep)
   \pre{au}  statep |-> StateR au
   \arg{addrp: ptr} "address" (Vref addrp)
   \prepost{qa fixee} addrp |-> addressR qa fixee
   \arg{origp: ptr} "original" (Vref origp)
   \pre{assumedFixeeState} origp |-> AccountStateR 1 assumedFixeeState
   \arg{actualp: ptr} "actual" (Vref actualp)
   \pre actualp |-> libspecs.optionR "monad::AccountState" (AccountStateR 1) 1 (actualPreTxState !! fixee)
   \post{satisfiesAssumptionsb:bool} [Vbool satisfiesAssumptionsb]
      [| satisfiesAssumptionsb <-> satisfiesAssumptions au actualPreTxState |] **
      if (negb satisfiesAssumptionsb)
      then statep |-> StateR au ** origp |-> AccountStateR 1 assumedFixeeState
      else                          
        Exists auf exactFixeeAssumption, statep |-> StateR auf
          ** origp |-> AccountStateR 1 exactFixeeAssumption
          ** [| relaxedValidation auf = false |]
          ** [| applyUpdates auf actualPreTxState = applyUpdates au actualPreTxState |]).

  Set Nested Proofs Allowed.
  Lemma observeState (state_addr:ptr) q t: 
    Observe (reference_to "monad::AccountState" state_addr)
            (state_addr |-> AccountStateR q t).
  Proof using. Admitted.

  Definition observeStateF r q t := @observe_fwd _ _ _ (observeState r q t).
  Hint Resolve observeStateF : br_opacity.
Ltac slauto := (slautot ltac:(autorewrite with syntactic equiv iff slbwd; try rewrite left_id; try solveRefereceTo)); try iPureIntro.
  
Lemma prf: denoteModule module |-- fix_spec.
Proof using.
  verify_spec'.
  slauto.
Abort.
(*
  Locate RepFor.
  Print rep.RepFor.C.
  go.
  slauto2
  iAssert (origp |-> structR "monad::AccountState" 1) as "?"%string. admit.
  admitRef
  go.
  
    go.
*)    
End with_Sigma.
