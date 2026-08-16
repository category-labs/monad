# Submodule patches for the zkVM guest

Two changes that could not be committed with the levers they belong to, because they live in
submodules pointing at upstream repositories (`martinus/unordered_dense`, `arximboldi/immer`)
rather than at forks.

**Nothing applies these automatically.** They are kept here so the work is versioned and reviewable,
not because the build consumes them.

## What they are

`third_party/unordered_dense` — the map stores `max_load_factor` as a `float` and computes
`m_num_buckets * 0.8f` on every rehash and size query. The guest has no FPU, so each one is a call
to `__floatundisf` and `__mulsf3`. For the power-of-two bucket counts this map uses, `(n * 4) / 5`
is the same integer. This one is arguably upstreamable: it is strictly better on any target and
loses nothing.

`third_party/immer` — the HAMT's `popcount`. There is no `cpop` on riscv64ima, so
`__builtin_popcountll` becomes a call to a 30-instruction libgcc helper, and the champ makes one
per level of every lookup and every insert.

## What they are worth, on the current guest

Re-measured on the `mtune` build, block 25551991 (`profiling/FINDINGS.md` §19 for the cost model):

| | | |
|---|---|---|
| `__popcountdi2` | 41,909 calls, 1,257,270 steps | 0.96 % of the guest |
| `__floatundisf` + `__mulsf3` | 368,154 steps | 0.28 % of the guest |

The popcount hunk takes the call path from 31 instructions to 18 and pays four 8-byte loads:
**820 COST per call, 34.4 M, 0.17 % of total COST**. The load-factor hunk removes the soft-float
family outright: **~25 M, 0.13 %**. Together **~0.30 %**.

The earlier note here said "0.40 point, 1.4 % of the total gain" from a 16-block run against
`ed16787ae`. That was a share of the guest's own work on an older build, not of COST, and it is not
comparable to the figures above — the guest has since lost 22 % of its steps.

## Two corrections to the immer hunk

**It did not compile.** The inline replacement was inserted inside the `#if defined(_MSC_VER)`
guard at the top of `bits.hpp`, while the two call sites that use it are on the `#else` side. On
gcc that is `error: 'monad_popcount_inline' has not been declared`, twice. Whatever produced the
0.40-point measurement above, it was not this file. The namespace now sits above the guard.

**The constants were still immediates.** rv64 has no 64-bit immediate, so gcc rebuilt each of the
SWAR's four constants with `lui/addi/slli/add` at every site — which is most of why the libgcc
helper costs 30 instructions in the first place. Fetching them from `.rodata` instead takes the
inline body from 29 instructions to 19. Same arithmetic either way: 20,004,166 host cases against
`__builtin_popcountll` (all 64 single- and double-bit patterns, all 64 prefixes, 20 M random words
biased sparse and dense), 0 divergences.

The fetch is `asm("ld %0, %1" : "=r"(v) : "m"(c))` under `MONAD_ZKVM_ZISK` only, behind
`if !consteval`. gcc folds any constant it can see straight back into an immediate, and the operand
has to be `"m"` rather than `"r"` or gcc is free to satisfy the address by rebuilding the value —
which is the thing being removed. SP1 is rv32im, where a 64-bit constant is two 32-bit halves and
materialising costs about what loading would; the host keeps the plain literals.

## Applying them

    git apply --directory=third_party/unordered_dense  # first hunk
    git apply --directory=third_party/immer            # second hunk

or, to carry them properly: fork `unordered_dense` under `category-labs`, land the integer
load-factor change there, and bump the submodule pointer. `immer`'s single site is not worth a fork
on its own.
