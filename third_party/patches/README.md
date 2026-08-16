# Submodule patches for the zkVM guest

One change that cannot be committed with the lever it belongs to, because it lives in a submodule
pointing at an upstream repository (`martinus/unordered_dense`) rather than at a fork.

**Nothing applies it automatically.** It is kept here so the work is versioned and reviewable, not
because the build consumes it.

There used to be a second hunk here, for `arximboldi/immer`. It is gone: the same win is now
carried by this repository. See "The immer hunk, and why it left" below — the short version is that
a submodule patch was never the only way to reach it, and the alternative measured *identically*.

## What it is

`third_party/unordered_dense` — the map stores `max_load_factor` as a `float` and computes
`m_num_buckets * 0.8f` on every rehash and size query. The guest has no FPU, so each one is a call
to `__floatundisf` and `__mulsf3`. For the power-of-two bucket counts this map uses, `(n * 4) / 5`
is the same integer. This one is arguably upstreamable: it is strictly better on any target and
loses nothing.

There is no way to reach it from this repository. `default_max_load_factor` is a
`static constexpr float` **member**, not a configuration macro, and the multiply is written out at
the two use sites — nothing an include-path shim or a force-included header can bind to. Unlike the
immer hunk, this one really does need the submodule.

## What it is worth — measured end to end, not estimated

Built and run on block 25551991, branch `al/zkvm-r4-levers` at `83aeb3ad7`, public output
byte-identical:

| build | STEPS | COST |
|---|---|---|
| branch, submodules pristine | 119,173,370 | 18,931,554,415 |
| + this hunk | 118,695,720 | **18,884,245,287** |

**−477,650 steps, −47,309,128 COST, 0.236 % of the reference.**

Every earlier number in this file was an estimate, and every estimate was low. This hunk was
recorded at 0.13 %; it is 0.236 %. The immer hunk was recorded at 0.17 %; it is 0.359 %. The
estimates priced the instructions removed from the callee and missed what removing a *call* does to
the caller.

Two older figures were also wrong and are recorded here so nobody re-derives them: "0.40 point,
1.4 % of the total gain", which was a share of the guest's own work on a build that has since lost
22 % of its steps; and the claim that SP1 is rv32im, which it is not — see
`zkvm/build-support/src/lib.rs`, it is rv64im.

## The immer hunk, and why it left

The HAMT's `popcount`. riscv64ima has no `cpop`, so `__builtin_popcountll` becomes a call to a
30-instruction libgcc helper, and the champ makes one per level of every lookup and every insert:
41,909 calls a block — all of the guest's popcount traffic, as it turns out.

It never needed a submodule. `__builtin_popcountll` is an ordinary identifier to the preprocessor,
so a force-included header can redefine it — for every guest translation unit at once, third-party
ones included, from a file this repository owns. That is `zkvm/core/builtin_popcount.hpp`, wired up
in `zkvm/guest/CMakeLists.txt`, and it measures **byte-identically** to the patched submodule:
117,870,371 steps and 18,812,345,445 COST either way.

Two things had to be right before that held, and both are written down beside the code:

**The hunk did not compile.** The inline replacement was inserted inside the `#if defined(_MSC_VER)`
guard at the top of `bits.hpp`, while the two call sites that use it are on the `#else` side. On gcc
that is `error: 'monad_popcount_inline' has not been declared`, twice. Whatever produced the
original 0.40-point measurement, it was not this file.

**The constants have to be fetched, and the second one has to be hoisted.** rv64 has no 64-bit
immediate, so gcc rebuilds each of the SWAR's four constants with `lui/addi/slli/add` at every
site — which is most of why the libgcc helper costs 30 instructions in the first place. Loading them
from `.rodata` instead takes the body from 29 instructions to 19. Then, counter-intuitively, one of
the four should go *back* to being an immediate: `bits::popcount64` refuses to hoist it into a
`const` local because standalone that costs two instructions, and standalone that is correct — but
inside immer's descent loop a materialised constant is loop-invariant arithmetic that LICM lifts out
and an `asm` load is not, and the difference is 0.124 % of the block. `popcount64_licm` in
`zkvm/core/builtin_popcount.hpp` is the loop-facing form; `bits::popcount64` stays as it is.

Same arithmetic in every form: 20,004,166 host cases against `__builtin_popcountll` (all 64 single-
and double-bit patterns, all 64 prefixes, 20 M random words biased sparse and dense), 0 divergences.

## Applying it

    git apply --directory=third_party/unordered_dense third_party/patches/zkvm-guest-submodules.patch

That leaves the submodule dirty and records nothing: a submodule is a separate repository pinned by
SHA, so no commit in *this* repository can carry its file contents. To carry it properly, fork
`unordered_dense` under `category-labs`, land the integer load-factor change there, and bump the
submodule pointer — the pointer bump *is* a commit here.
