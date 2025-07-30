(* proofs about reserve balances:
- consensus guarnatees when it sends a block for executions
- what consensus assumes execution guarantees
- how those guarantees ensure execution will never run into a chase when an account has insufficient balance to pay gas fees
 *)
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
(*=== Stub definitions for W256 arithmetic; to be filled in later ===*)
Definition w256 := monad.EVMOpSem.keccak.w256.
Parameter w256_zero : w256.                          (* TOFIXLATER *)
Parameter w256_add  : w256 -> w256 -> w256.          (* TOFIXLATER *)
Parameter w256_sub  : w256 -> w256 -> w256.          (* TOFIXLATER *)
Parameter w256_mul  : w256 -> w256 -> w256.          (* TOFIXLATER *)
Parameter w256_geb  : w256 -> w256 -> bool.          (* TOFIXLATER *)
Parameter min_w256  : w256 -> w256 -> w256.          (* TOFIXLATER *)

(* lookup an account’s balance at state s, defaulting to zero *)
Definition get_balance_estimate
           (s: monad.proofs.evmopsem.evm.GlobalState)
           (addr: monad.proofs.evmopsem.evm.address) : w256 :=
  match stdpp.base.lookup addr s with
  | Some ac =>
      let ba := monad.proofs.evmopsem.coreAc ac in
      monad.EVMOpSem.block.block_account_balance ba
  | None =>
      w256_zero
  end.                                              (* TOFIXLATER: verify coreAc usage *)

(* reserve‐balance parameters *)
Parameter default_reserve_balance
          : w256.                                 (* TOFIXLATER *)
Parameter user_reserve_balance
          : monad.proofs.evmopsem.evm.GlobalState ->
            monad.proofs.evmopsem.evm.address -> w256.
                                                 (* TOFIXLATER *)

(* transaction equality test *)
Parameter eqb_tx
          : monad.proofs.evmopsem.Transaction ->
            monad.proofs.evmopsem.Transaction -> bool.
                                                 (* TOFIXLATER *)

(* sum of gas‐fee amounts in a list *)
Fixpoint sum_gas_fees
           (l: list monad.proofs.evmopsem.Transaction) : w256 :=
  match l with
  | Corelib.Init.Datatypes.nil => w256_zero
  | Corelib.Init.Datatypes.cons tx rest =>
      w256_add
        (w256_mul (monad.EVMOpSem.block.tr_gas_limit tx)
                  (monad.EVMOpSem.block.tr_gas_price tx))
        (sum_gas_fees rest)
  end.

(* stub for the “emptying transaction” predicate *)
Parameter is_emptying_transaction
          : monad.proofs.evmopsem.evm.GlobalState ->
            list monad.proofs.evmopsem.Transaction ->
            monad.proofs.evmopsem.Transaction -> bool.
                                                 (* TOFIXLATER *)

Open Scope bool_scope.

Definition consensusAcceptableTx
           (s: monad.proofs.evmopsem.evm.GlobalState)
           (intermediate: list monad.proofs.evmopsem.Transaction)
           (a: monad.proofs.evmopsem.Transaction) : bool :=
  match intermediate with
  | Corelib.Init.Datatypes.nil =>
      let bal0    := get_balance_estimate s (monad.EVMOpSem.block.tr_from a) in
      let reserve := min_w256 default_reserve_balance bal0 in
      w256_geb reserve
        (w256_mul (monad.EVMOpSem.block.tr_gas_limit a)
                  (monad.EVMOpSem.block.tr_gas_price a))
  | Corelib.Init.Datatypes.cons first rest =>
      let bal0 := get_balance_estimate s (monad.EVMOpSem.block.tr_from a) in
      if is_emptying_transaction s (Corelib.Init.Datatypes.cons first rest) a then
        if eqb_tx first a then
          (* only transaction is a itself *)
          w256_geb bal0
            (w256_mul (monad.EVMOpSem.block.tr_gas_limit a)
                      (monad.EVMOpSem.block.tr_gas_price a))
        else
          let bal1 :=
              w256_sub bal0
                (w256_add (monad.EVMOpSem.block.tr_value first)
                          (w256_mul (monad.EVMOpSem.block.tr_gas_limit first)
                                    (monad.EVMOpSem.block.tr_gas_price first)))
          in
          let reserve :=
              min_w256
                (user_reserve_balance s (monad.EVMOpSem.block.tr_from a))
                bal1
          in
          w256_geb reserve (sum_gas_fees rest)
      else
        let reserve :=
            min_w256
              (user_reserve_balance s (monad.EVMOpSem.block.tr_from a))
              bal0
        in
        w256_geb reserve (sum_gas_fees (Corelib.Init.Datatypes.cons first rest))
  end.





