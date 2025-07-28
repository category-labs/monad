(* some lemmas proving the obligations in the proof of fix_account_mismatch and sender_has_balance *)
Require Import ZArith.
Require Import stdpp.decidable.
(* 2²⁵⁶ as a Z constant — the EVM balance modulus                     *)
Definition mod256 : Z := 2 ^ 256.

(* Reduce any integer modulo 2²⁵⁶ into the canonical range [0,mod256)  *)
Definition mod256z (x : Z) : Z := Z.modulo x mod256.

(* ------------------------------------------------------------------ *)
(* Direct translation of the C++ balance-patch logic                   *)
(* ------------------------------------------------------------------ *)

Require Import bluerock.auto.cpp.specs.
Require Import bluerock.auto.cpp.tactics4.


Open Scope Z_scope.
Definition update_balance
           (original actual local : Z) : Z :=
  if bool_decide (original > actual) then
    (* original.balance > actual.balance branch *)
    let diff   := mod256z (original - actual) in
    let local' := mod256z (local - diff)      in
    local'
  else
    (* original.balance ≤ actual.balance branch *)
    let diff   := mod256z (actual - original) in
    let local' := mod256z (local + diff)      in
    local'.


Definition update_balance_mod
           (original actual local : Z) : Z :=
  mod256z (local + (actual - original)).


Lemma ff original actual local: update_balance original actual local = update_balance_mod original actual local.
Proof using.
  unfold update_balance, update_balance_mod.
  simpl. unfold mod256z.
  case_bool_decide.
  - Arith.mod_simpl. f_equiv. lia.
  - Arith.mod_simpl. reflexivity.
Qed.
  

Require Import ZArith Lia.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Basic constants and helpers                                         *)
(* ------------------------------------------------------------------ *)

Definition u256 (z : Z) : Prop := 0 ≤ z < mod256.

(* “max” update performed by original_state.set_min_balance()          *)
Definition set_min_balance (old new : Z) : Z :=
  Z.max old new.

(* Sender‑balance helper (value ≥ 0 is already endian‑decoded)         *)
Definition sender_has_balance_core
           (balance value original_balance min_balance : Z)
           : Z (* the *new* min_balance that will be stored *) :=
  if Z.ge_dec balance  value then
    (* enough balance – will debit                           *)
    let diff := balance - value in
    if Z.gt_dec original_balance diff  (* original > diff ? *)
    then set_min_balance min_balance (original_balance - diff)
    else min_balance                   (* leave it unchanged *)
  else
    (* insufficient funds – validate_exact_balance flag set
       (min_balance stays unchanged)                       *)
    min_balance.

(** The invariant we want to preserve. *)
Definition invariant
           (orig cur minb : Z) : Prop :=
  orig - cur ≤ minb.

Ltac ulia := unfoldLocalDefs; lia.
(** A single call to [sender_has_balance_core] preserves it. *)
Lemma sender_has_balance_preserves
      (balance value original_balance min_balance : N)
      (Hbal  : u256 balance)
      (Hval  : 0 ≤ value)               (* value is uint256 too *)
      (Horig : u256 original_balance)
      (Hmin  : u256 min_balance)
      (Hinv  : invariant original_balance balance min_balance) :
  invariant original_balance
            (if Z.ge_dec balance value
             then balance - value       (* the balance *after* debit *)
             else balance)              (* balance unchanged         *)
            (sender_has_balance_core
               balance value original_balance min_balance).
Proof.
  unfold invariant, sender_has_balance_core, set_min_balance in *.
  destruct (Z.ge_dec balance value) as [Hge | Hlt].

  (* ------------ CASE 1: balance ≥ value (we will debit) ------------ *)
  - set (diff := balance - value).
    assert (Hdiff : diff = balance - value) by reflexivity.
    
    destruct (Z.gt_dec original_balance diff) as [Hgt | Hle]; lia.

  (* ------------ CASE 2: balance < value (no debit) ------------------ *)
  - (* min_balance is unchanged; current_balance stays = balance       *)
    simpl. lia.
Qed.
