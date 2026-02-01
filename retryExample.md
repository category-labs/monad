# Unnecessary retry example (cached reserve-balance tracking)

## Setup
- Reserve threshold: `R = 10 MON` (fixed)
- Account **A**: EOA/delegated (subject to reserve checks), **not** the tx sender
- Original (pre-transaction) balance: `orig(A) = 100`

## Transaction (no CHECKRESERVEBALANCE opcode)
Inside one transaction:
1) `A` sends `80` → balance becomes `20`
2) Later in the same tx, `A` receives `80` → balance returns to `100`

## What the cached impl records (strict)
On the debit, `State::subtract_from_balance(A, 80)` triggers:

```
update_rb_violation(A, &account_state)
  -> rb_reserve_cap(A)
     -> check_min_original_balance(A, 10)
  -> check_account_min_balance(orig_state, current_account, 10)
```

With `balance = 20`, `orig_balance = 100`, and `value = 10`:

```
min_balance := value + (orig_balance - balance)
            = 10 + (100 - 20)
            = 90
```

This is recorded in `OriginalAccountState::set_min_balance(...)` and is
**monotone** (can only increase), so later credits cannot weaken it. Also,
`add_to_balance` skips recomputing when the account is not already in the
violation set, so no later update reduces this assumption.

## What the old end-of-tx scan would record (minimal)
At the end of tx, `balance = 100`:

```
check_min_balance(10) -> min_balance = 10
```

So the old scan only required `min_balance >= 10`.

## Why this causes an unnecessary retry
Assume a prior committed tx changes the pre-state to `orig(A) = 60`.
The final balance of this tx is still `>= 10`, so the reserve check should
pass.

- **Old scan**: requires `min_balance >= 10` → passes.
- **Cached impl**: requires `min_balance >= 90` → fails → retry.

## Key point
The stricter assumption (`min_balance = 90`) is recorded **mid-tx**, even
though no `CHECKRESERVEBALANCEVIOLATIONS` was executed and the only intended
check is at end-of-tx. This creates unnecessary retries.
