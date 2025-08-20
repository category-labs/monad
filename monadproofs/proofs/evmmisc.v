Require Import monad.proofs.bigauto.
Require Import monad.proofs.evmopsem.
Require Import monad.proofs.misc.
Require Import bluerock.hw_models.utils.
Require Import bluerock.auto.cpp.tactics4.

#[only(lens)] derive block.block_account.
#[only(lens)] derive AccountM.

(* move to evmmisc.v *)

Definition zbvfun (fz: Z -> Z) (w: keccak.w256): keccak.w256:=
  let wnz := fz (w256_to_Z w) in
  Z_to_w256 wnz.

Definition nbvfun (fz: N -> N) (w: keccak.w256): keccak.w256:=
  let wnz := fz (w256_to_N w) in
  Z_to_w256 (Z.of_N wnz).


Definition zbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A Z Z :=
  {| view := λ a : A, w256_to_Z (a .^ l);
    Lens.over := λ (fz : Z → Z) (a : A), (l %= zbvfun fz) a |}.

Definition nbvlens {A:Type} (l: Lens A A keccak.w256 keccak.w256): Lens A A N N :=
  {| view := λ a : A, w256_to_N (a .^ l);
    Lens.over := λ (fz : N → N) (a : A), (l %= nbvfun fz) a |}.


(*
Definition _balance : Lens AccountM AccountM Z Z:=
  zbvlens (_coreAc .@ _block_account_balance).
 *)

Definition _balanceN : Lens AccountM AccountM N N :=
  nbvlens (_coreAc .@ _block_account_balance).

#[global] Instance inh : Inhabited AccountM := populate dummyAc.
Definition updateBalanceOfAc (s: evm.GlobalState) (addr: evm.address) (upd: N -> N) : evm.GlobalState :=
  <[ addr :=  (s !!! addr) &: _balance %= upd ]> s.


Lemma def0:
  w256_to_N keccak.w256_default = 0%N.
Proof using.
  reflexivity.
Qed.


Lemma balanceOfUpd s ac f acp:
  balanceOfAc (updateBalanceOfAc s ac f) acp = if (bool_decide (ac=acp)) then f (balanceOfAc s ac) else (balanceOfAc s acp).
Proof.
  simpl.
  unfold updateBalanceOfAc.
  unfold balanceOfAc.
  autorewrite with syntactic.
  rewrite lookup_insert_iff;[| exact dummyAc].
  case_bool_decide;  auto.
  unfold lookup_total.
  unfold fin_maps.map_lookup_total.
  unfold default.
  unfold evm.account_state.
  case_match; auto.
  2:{
    setoid_rewrite H0.
    reflexivity.
  }
  {
    setoid_rewrite H0.
    unfold id.
    destruct a.
    reflexivity.
  }
Qed.



Ltac resdec tac :=
  repeat match goal with
  | [|- context [decide ?P] ] =>
    resultsIn0or1Goals ltac:(destruct (decide P); try solve [ tac ])
  | [|- context [bool_decide ?P] ] =>
    resultsIn0or1Goals ltac:(rewrite (bool_decide_decide P); (destruct (decide P); try solve [ tac ]))
  | [H:context [decide ?P] |- _ ] =>
    resultsIn0or1Goals ltac:((destruct (decide P); try solve [ tac ]))
  | [H:context [bool_decide ?P] |- _ ] =>
    resultsIn0or1Goals ltac:(rewrite (bool_decide_decide P) in H; (destruct (decide P); try solve [ tac ]))
    end.
