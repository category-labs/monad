# Skipped retry example (credit‑only account)

## Setup
- Reserve threshold `R = 10 MON` (fixed).
- Account `foo` is **subject** (EOA or delegated EOA), **not** the sender.
- The transaction **only credits** `foo` (no debits from `foo`).

## Speculative execution (what we ran locally)
- Pre‑tx balance observed during execution: `orig_exec(foo) = 5`.
- Transaction credits `foo` by `+1`.
- End balance during execution: `6`.

## Old uncached end‑of‑tx scan (iterates all changed accounts)
- Computes reserve using the speculative pre‑balance:
  ```
  reserve = min(R, orig_exec) = min(10, 5) = 5
  ```
- Calls `check_min_balance(foo, reserve)` with current balance `6`.
- This records a relaxed‑merge constraint:
  ```
  min_balance := orig_exec - (balance - reserve)
              = 5 - (6 - 5)
              = 4
  ```
  so it requires `orig_at_merge(foo) >= 4`.

## Actual merge pre‑state (what really happened earlier in the block)
- Suppose the true pre‑tx balance is lower: `orig_merge(foo) = 3`.
- The **actual** reserve for the tx is:
  ```
  reserve_actual = min(10, 3) = 3
  ```
- Final balance after credit: `3 + 1 = 4`, which **passes** (`4 >= 3`).

## Outcome
- **Old uncached impl**: fails merge because it recorded `min_balance >= 4`,
  but `orig_merge = 3` → **retry**.
- **New lazy cached impl**: no constraint is recorded for a credit‑only account
  (no `subtract_from_balance`), so merge succeeds → **no retry**.

## Key point
The old scan recorded a speculative pre‑balance‑dependent constraint for a
credit‑only account, even though the reserve check would pass for the actual
(pre‑merge) balance. The lazy cached impl avoids that unnecessary constraint,
so it can skip a retry.
