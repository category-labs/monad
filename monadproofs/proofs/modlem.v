(* some lemmas proving the obligations in the proof of fix_account_mismatch and sender_has_balance *)
Require Import ZArith.
Require Import stdpp.decidable.
Require Import bluerock.auto.cpp.specs.
Require Import bluerock.auto.cpp.tactics4.
Definition mod256 : Z := 2 ^ 256.

Definition mod256z (x : Z) : Z := Z.modulo x mod256.

Open Scope Z_scope.

(* model of the current code for updating recent->balance. the output of this fn is stored there *)
Definition update_balance
           (original actual recent : Z) : Z :=
  if bool_decide (original > actual) then
    let diff   := mod256z (original - actual) in
    mod256z (recent - diff)
  else
    let diff   := mod256z (actual - original) in
    mod256z (recent + diff).


(* model of the proposed change to the logic for  updating recent->balance. the output of this fn is stored there *)
Definition update_balance_mod
           (original actual recent : Z) : Z := 
  mod256z (recent + (actual - original)).

Require Import bluerock.auto.cpp.tactics4.

Lemma changeIsEquivalentToOrig: forall original actual recent,
    update_balance original actual recent
    = update_balance_mod original actual recent.
Proof using.
  intros.
  unfold update_balance, update_balance_mod.
  simpl. unfold mod256z.
  case_bool_decide.
  - Arith.mod_simpl. f_equiv. lia.
  - Arith.mod_simpl. reflexivity.
Qed.
  
(*
Print Assumptions changeIsEquivalentToOrig.
Closed under the global context

*)

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
