# Submodule patches for the zkVM guest

Two changes measured as part of `al/zkvm-levers` that could not be committed with it, because they
live in submodules pointing at upstream repositories (`martinus/unordered_dense`,
`arximboldi/immer`) rather than at forks.

**Nothing applies these automatically.** They are kept here so the work is versioned and reviewable,
not because the build consumes them.

## What they are

`third_party/unordered_dense` — the map stores `max_load_factor` as a `float` and computes
`m_num_buckets * 0.8f` on every rehash and size query. The guest has no FPU, so each one is a call
to `__floatundisf` and `__mulsf3`. For the power-of-two bucket counts this map uses, `(n * 4) / 5`
is the same integer. This one is arguably upstreamable: it is strictly better on any target and
loses nothing.

`third_party/immer` — one more `std::popcount` site, on the same footing as the ones in
`al/zkvm-levers`: no `cpop` on riscv64ima, so it becomes a 29-instruction libgcc call.

## What they are worth

Measured on 16 blocks of 25551991-25552607, against `ed16787ae`, post-state root verified:

| | guest's own work |
|---|---|
| `al/zkvm-levers` alone | **27.69 %** |
| with these two | **28.09 %** |

**0.40 point, 1.4 % of the total gain.** They are not a blocker for anything.

## Applying them

    git apply --directory=third_party/unordered_dense  # first hunk
    git apply --directory=third_party/immer            # second hunk

or, to carry them properly: fork `unordered_dense` under `category-labs`, land the integer
load-factor change there, and bump the submodule pointer. `immer`'s single site is not worth a fork
on its own.
