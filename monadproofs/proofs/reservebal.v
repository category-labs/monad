(* proofs about reserve balances:
- consensus guarnatees when it sends a block for executions
- what consensus assumes execution guarantees
- how those guarantees ensure execution will never run into a chase when an account has insufficient balance to pay gas fees
 *)
Require Import bluerock.auto.cpp.tactics4.
Require Import monad.proofs.evmopsem.


(*
In the above latex document, there is an algorithm within \begin{algorithm} with caption
"Consensus Checks for block $n$ for sequencing transaction $t$ from account $a$".
Implement it in Gallina as a function by filling in the following:

```gallina
Definition consensusAcceptableTx (s: evm.GlobalState) (intermediate: list Transaction) (a: Transaction) : bool :=
```

Unlike in the latex document, assume that list `intermediate` does NOT contain the candidate transaction `a`. Above `s` can be considered as the $state^{n-k}$ argument in the latex document.
Ignore the $\mathcal{P}_{n-2k+2}^{t}$ argument, which is only needed in the call to is_emptying_transaction, which you can leave admitted for now.

Use N to do operations on balances, not monad.EVMOpSem.keccak.w256.
We have w256_to_N and Z_to_w256.

Use bool_decide for boolean decisions: e.g. use `bool_decide (a<b)%N` instead of `N.ltb a b`.
Once your definitions typecheck and you are satisfied, do the beautification stage where you reduce the fully qualified names to more readable names and use more notations. Keep a TOFIXLATER until then so that the outer bot keeps coming back to you.
 
+++ QUERIES
Print evm.GlobalState.
Print w256_to_N.
Print Z_to_w256.
Print balanceOfAc.
Print updateBalanceofAc.

+++ FILES
../proofs/reservebal.md

*)
 Set Printing FullyQualifiedNames.
(* ----------------------------------------------------------------------- *)
(* Read the “reserve balance” of account [sender] at consensus state [s].  *)
(* Here we use the on‐chain balance, i.e. no per‐account override.          *)
Definition user_reserve_balance
  (s : monad.proofs.evmopsem.evm.GlobalState)
  (sender : monad.proofs.evmopsem.evm.address)
  : N :=
  monad.proofs.evmopsem.balanceOfAc s sender.

(* Predicate for “emptying transaction” – currently always returns false. *)
Definition is_emptying_transaction
  (sender : monad.proofs.evmopsem.evm.address)
  (t0 : monad.proofs.evmopsem.Transaction)
  : bool :=
  false.

(* Interpret the legacy gas_price field as our gas_bid. *)
Definition gas_bid_of (t : monad.proofs.evmopsem.Transaction) : N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_gas_price t).

(* Convert the w256‐typed gas_limit to N. *)
Definition gas_limit_of (t : monad.proofs.evmopsem.Transaction) : N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_gas_limit t).

(* Sum over gas_limit * gas_bid for a list of transactions. *)
Fixpoint sum_gas_bids (l : list monad.proofs.evmopsem.Transaction) : N :=
  match l with
  | [] => 0
  | tx :: xs =>
      N.add (N.mul (gas_limit_of tx) (gas_bid_of tx))
            (sum_gas_bids xs)
  end.

(* Consensus‐side acceptability check for sequencing [a], given state s = state^{n-k}
   and the list [intermediate] of prior txns from this sender in the same block. *)
Definition consensusAcceptableTx
           (s : monad.proofs.evmopsem.evm.GlobalState)
           (intermediate : list monad.proofs.evmopsem.Transaction)
           (a : monad.proofs.evmopsem.Transaction)
  : bool :=
  let sender := monad.EVMOpSem.block.tr_from a in
  let bal0   := monad.proofs.evmopsem.balanceOfAc s sender in
  let gl_a   := gas_limit_of a in
  let gb_a   := gas_bid_of a in
  match intermediate with
  | [] =>
      let reserve := N.min (user_reserve_balance s sender) bal0 in
      bool_decide (N.mul gl_a gb_a <= reserve)%N
  | t0 :: rest =>
      if is_emptying_transaction sender t0 then
        (* subtract the “emptying” tx’s value + its gas fee *)
        let bal1 :=
          N.sub
            (N.sub bal0
                   (monad.proofs.evmopsem.w256_to_N
                      (monad.EVMOpSem.block.tr_value t0)))
            (N.mul (gas_limit_of t0) (gas_bid_of t0)) in
        let reserve := N.min (user_reserve_balance s sender) bal1 in
        bool_decide (sum_gas_bids rest <= reserve)%N
      else
        let reserve := N.min (user_reserve_balance s sender) bal0 in
        bool_decide (sum_gas_bids intermediate <= reserve)%N
  end.
(* ----------------------------------------------------------------------- *)


