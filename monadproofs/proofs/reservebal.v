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
(* Placeholder for the emptying‐check. *)
Parameter is_emptying_transaction
  : monad.proofs.evmopsem.evm.address
    -> monad.proofs.evmopsem.Transaction
    -> list monad.proofs.evmopsem.Transaction
    -> monad.proofs.evmopsem.evm.GlobalState
    -> bool.
(* TOFIXLATER *)

(* Placeholder for user‐configured reserve balances. *)
Parameter user_reserve_balance
  : monad.proofs.evmopsem.evm.address -> Corelib.Numbers.BinNums.N.
(* TOFIXLATER *)

(* Convert w256-fields to N. *)
Definition tx_gas_limit_N (tx : monad.proofs.evmopsem.Transaction)
  : Corelib.Numbers.BinNums.N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_gas_limit tx).

Definition tx_gas_bid_N (tx : monad.proofs.evmopsem.Transaction)
  : Corelib.Numbers.BinNums.N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_gas_price tx).

Definition tx_value_N (tx : monad.proofs.evmopsem.Transaction)
  : Corelib.Numbers.BinNums.N :=
  monad.proofs.evmopsem.w256_to_N
    (monad.EVMOpSem.block.tr_value tx).

(* Sum of gas_limit * gas_bid over a list of transactions *)
Fixpoint sum_gas_fee (l : list monad.proofs.evmopsem.Transaction)
                     : Corelib.Numbers.BinNums.N :=
  match l with
  | []      => Corelib.Numbers.BinNums.N0
  | t :: ts => tx_gas_limit_N t * tx_gas_bid_N t
               + sum_gas_fee ts
  end.

(* The consensus‐side reserve‐balance check *)
Definition consensusAcceptableTx
           (s            : monad.proofs.evmopsem.evm.GlobalState)
           (intermediate : list monad.proofs.evmopsem.Transaction)
           (a            : monad.proofs.evmopsem.Transaction)
           : bool :=
  let sender   := monad.EVMOpSem.block.tr_from a in
  let balance0 := monad.proofs.evmopsem.balanceOfAc s sender in
  match intermediate with
  | [] =>
      (* No prior tx: require reserve ≥ 0 *)
      let reserve :=
        Corelib.Numbers.BinNums.N.min
          (user_reserve_balance sender)
          balance0 in
      Corelib.Numbers.BinNums.leb
        Corelib.Numbers.BinNums.N0
        reserve
  | h :: t =>
      if is_emptying_transaction sender h [] s then
        (* First tx empties: subtract its cost, then check the rest *)
        let balance1 :=
            balance0
            - tx_value_N h
            - (tx_gas_limit_N h * tx_gas_bid_N h) in
        let reserve :=
          Corelib.Numbers.BinNums.N.min
            (user_reserve_balance sender)
            balance1 in
        Corelib.Numbers.BinNums.leb
          (sum_gas_fee t)
          reserve
      else
        (* Otherwise: all in‐window fees must fit reserve *)
        let reserve :=
          Corelib.Numbers.BinNums.N.min
            (user_reserve_balance sender)
            balance0 in
        Corelib.Numbers.BinNums.leb
          (sum_gas_fee (h :: t))
          reserve
  end.


