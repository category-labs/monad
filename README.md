(removed original readme, documenting here the optimization im working on)

# Inline DIV/MOD when divisor fits in 64 bits

The JIT currently lowers `DIV`/`MOD` through a couple of peepholes, constant-folding when both operands are literals, and a shifting when the divisor is a power of two.
Otherwise it calls `runtime::udiv` / `runtime::umod`.

- [udiv emitter](https://github.com/category-labs/monad/blob/v0.14.4-rc.1/category/vm/compiler/ir/x86/emitter.cpp#L3333-L3338)
- [current optimizations)](https://github.com/category-labs/monad/blob/v0.14.4-rc.1/category/vm/compiler/ir/x86/emitter.cpp#L7190-L7264)
- [runtime overload](https://github.com/category-labs/monad/blob/v0.14.4-rc.1/category/core/runtime/uint256.hpp)

**This PR adds the following optimization**: when the divisor is a literal that fits in 64 bits, inline the long division as four hardware `div r/m64` instructions instead of calling into the runtime. The inlined sequence is short (a few instructions, no spill of the divisor) and the case is very common in a bunch of contracts.

## Why this matters

Divisions by `1e18` (wei), `1e6` (stablecoin decimals), `31_536_000` (seconds in a year), `100`, etc. show up all over the place, and the divisor almost always fits in 64 bits. Two real examples:

- [Curve stETH/ETH pool `0xDC24316b9AE028F1497c275EB9192a3Ea0f67022`](https://etherscan.io/address/0xDC24316b9AE028F1497c275EB9192a3Ea0f67022)
- [Aave: Supply Logic `0x33654b16a4de97bce05d7dd06803bf1066f3123c`](https://etherscan.io/address/0x33654b16a4de97bce05d7dd06803bf1066f3123c)

Common patterns in their bytecode (disassembled with [etherscan opcode-tool](https://etherscan.io/opcode-tool)):

literal divisor `100`:
```
[1053] PUSH1 0x64
[1054] DUP1
[1055] DUP3
[1056] DIV
```

literal divisor `10^10`:
```
[2516] PUSH5 0x02540be400
[2517] DUP1
[2518] DUP3
[2519] DIV
```

divisor `31_536_000` (seconds in a year):
```
[5601] PUSH4 0x01e13380
[5602] SWAP1
[5603] DIV
```

the classic `/1e18`:
```
[5961] PUSH8 0x0de0b6b3a7640000
[5962] PUSH1 0x02
[5963] DUP5
[5964] DIV
```

With this PR these opcodes are replaced by the JIT compiler by some inline code, rather than the runtime call.

## Benchmarks

This PR delivers with some benchmarks, to prove the optimization. Said optimization is gated behind `MONAD_DISABLE_UDIV_BY_UINT64_OPT` (to be removed when integrated).

Build two binaries. One without the optimization (gated behind ) and one with it on:

```
CC=gcc-15 CXX=g++-15 cmake -G Ninja -B build-noopt \
    -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_CXX_FLAGS="-DMONAD_DISABLE_UDIV_BY_UINT64_OPT" \
    -DMONAD_COMPILER_BENCHMARKS=On \
    -DMONAD_COMPILER_TESTING=Off
```

Build both.
```
cmake --build build        --target vm-micro-benchmarks -j8   # optimization ON
cmake --build build-noopt  --target vm-micro-benchmarks -j8   # optimization OFF
```

Run without the optimization.
```
./build-noopt/test/vm/micro_benchmarks/vm-micro-benchmarks \
    --title-filter='PUSH N; SWAP1; DIV/MOD' \
    --impl-filter='Compiler' \
    --format=md
```

Run with the optimization.
```
./build/test/vm/micro_benchmarks/vm-micro-benchmarks \
    --title-filter='PUSH N; SWAP1; DIV/MOD' \
    --impl-filter='Compiler' \
    --format=md
```

The affected sequences get 7–13% faster. Control cases (divisor > 64 bits, and SDIV/SMOD which this PR doesn't touch) are unchanged.
The following table is a summary of the output of the results reported by the previous two commands.

```
┌──────────────────────────────────────┬──────────────────┬────────────────┬────────┬────────┬─────────────┐
│              Sequence                │ Before (opt OFF) │ After (opt ON) │  Δ ns  │   %    │   Verdict   │
├──────────────────────────────────────┼──────────────────┼────────────────┼────────┼────────┼─────────────┤
│ Affected by this PR (should drop)    │                  │                │        │        │             │
├──────────────────────────────────────┼──────────────────┼────────────────┼────────┼────────┼─────────────┤
│ PUSH1 0x0A; SWAP1; DIV               │           113.46 │         104.92 │  −8.54 │  −7.5% │ ✅ faster   │
│ PUSH2 0x2710; SWAP1; DIV             │           117.86 │         108.96 │  −8.90 │  −7.5% │ ✅ faster   │
│ PUSH8 0xDE0B6B3A7640000; SWAP1; DIV  │           108.20 │         100.24 │  −7.96 │  −7.4% │ ✅ faster   │
│ PUSH1 0x0A; SWAP1; MOD               │           117.31 │         104.75 │ −12.56 │ −10.7% │ ✅ faster   │
│ PUSH2 0x2710; SWAP1; MOD             │           118.98 │         109.40 │  −9.58 │  −8.1% │ ✅ faster   │
│ PUSH8 0xDE0B6B3A7640000; SWAP1; MOD  │           115.48 │          99.93 │ −15.55 │ −13.5% │ ✅ faster   │
├──────────────────────────────────────┼──────────────────┼────────────────┼────────┼────────┼─────────────┤
│ Control: wide divisor (>64 bits)     │                  │                │        │        │             │
├──────────────────────────────────────┼──────────────────┼────────────────┼────────┼────────┼─────────────┤
│ PUSH9 0x30000000000000000; SWAP1; DIV│           145.88 │         147.57 │  +1.69 │  +1.2% │ ✓ unchanged │
│ PUSH9 0x30000000000000000; SWAP1; MOD│           151.20 │         148.37 │  −2.83 │  −1.9% │ ✓ unchanged │
├──────────────────────────────────────┼──────────────────┼────────────────┼────────┼────────┼─────────────┤
│ Control: signed variant              │                  │                │        │        │             │
├──────────────────────────────────────┼──────────────────┼────────────────┼────────┼────────┼─────────────┤
│ PUSH8 0xDE0B6B3A7640000; SWAP1; SDIV │           118.95 │         120.07 │  +1.12 │  +0.9% │ ✓ unchanged │
│ PUSH8 0xDE0B6B3A7640000; SWAP1; SMOD │           120.57 │         120.73 │  +0.16 │  +0.1% │ ✓ unchanged │
└──────────────────────────────────────┴──────────────────┴────────────────┴────────┴────────┴─────────────┘
```

## Binary size cost

Inlining costs bytes. To check the cost is bounded, run the compile benchmarks on a set of real contracts:

```
./build/test/vm/compile_benchmarks/compile-benchmarks \
    --benchmark_filter='compile/' \
    --benchmark_report_aggregates_only
```
```
./build-noopt/test/vm/compile_benchmarks/compile-benchmarks \
    --benchmark_filter='compile/' \
    --benchmark_report_aggregates_only
```

Note that I have added a few new contracts where this pattern (div by literal <64 bit number) appears multiple times.

```
┌───────────────────────┬───────────┬───────────────────────────┬────────────────────────┬─────────┬─────────┬─────────────────────┐
│       Contract        │ EVM bytes │ Native size (without opt) │ Native size (with opt) │ Δ bytes │   Δ %   │ Optimization fires? │
├───────────────────────┼───────────┼───────────────────────────┼────────────────────────┼─────────┼─────────┼─────────────────────┤
│ usdt                  │    11,075 │                   103,989 │                103,989 │       0 │   0.00% │ no                  │
│ stop                  │         1 │                        56 │                     56 │       0 │   0.00% │ no                  │
│ uniswap               │    21,943 │                   268,705 │                268,705 │       0 │   0.00% │ no                  │
│ uniswap_v3            │    24,497 │                   317,631 │                317,632 │      +1 │  0.000% │ noise (≤ 1 byte)    │
│ lido_withdrawal_queue │    24,190 │                   325,239 │                325,239 │       0 │   0.00% │ no                  │
│ balancer_v3_vault     │    24,538 │                   387,749 │                387,815 │     +66 │ +0.017% │ yes, ~3 sites       │
│ aave_v3_supply_logic  │    10,717 │                   164,521 │                164,678 │    +157 │ +0.095% │ yes, ~7 sites       │
│ curve_steth_eth       │    15,735 │                   252,776 │                253,527 │    +751 │ +0.297% │ yes, ~34 sites      │
└───────────────────────┴───────────┴───────────────────────────┴────────────────────────┴─────────┴─────────┴─────────────────────┘
```

Worst case in the sample is `curve_steth_eth` at +0.30%. Contracts where the optimization doesn't fire are byte-for-byte identical to the unoptimized build.

## Reproducer

A minimal program that hits the new branch:

```
[0] PUSH0 0x
[1] CALLDATALOAD
[2] PUSH8 0x0DE0B6B3A7640000
[3] SWAP1
[4] DIV
[5] STOP
```

Compile it with both binaries and diff the emitted asm:

```
mkdir -p /tmp/a /tmp/b
HEX='5F35670DE0B6B3A7640000900400'
(cd /tmp/a && printf '%s' "$HEX" | xxd -r -p | ~/monad/build/cmd/vm/parser/parser-tool       --stdin --binary --compile >/dev/null)
(cd /tmp/b && printf '%s' "$HEX" | xxd -r -p | ~/monad/build-noopt/cmd/vm/parser/parser-tool --stdin --binary --compile >/dev/null)
diff -u /tmp/b/out.asm /tmp/a/out.asm | less
```

In a nutshell, this is the produced diff:

```diff
diff -u /tmp/b/out.asm /tmp/a/out.asm
--- /tmp/b/out.asm    2026-05-14 17:20:13.747310393 +0000
+++ /tmp/a/out.asm    2026-05-14 17:20:13.737838800 +0000
@@ -29,12 +29,26 @@
 vpermq ymm0, ymm15, 27
 vpshufb ymm0, ymm0, qword ptr [ROD+32]
 L3:
-vmovaps qword ptr [rbp+32], ymm0
-lea rsi, qword ptr [rbp+32]
-lea rdx, qword ptr [ROD+64]
-lea rdi, qword ptr [rbp]
-vzeroupper
-call qword ptr [ROD+8]
+vmovaps qword ptr [rbp], ymm0
+mov r12, qword ptr [rbp]
+mov r13, qword ptr [rbp+8]
+mov r14, qword ptr [rbp+16]
+mov r15, qword ptr [rbp+24]
+mov rax, 1000000000000000000
+mov qword ptr [rsp+56], rax
+xor edx, edx
+mov rax, r15
+div qword ptr [rsp+56]
+mov r15, rax
+mov rax, r14
+div qword ptr [rsp+56]
+mov r14, rax
+mov rax, r13
+div qword ptr [rsp+56]
+mov r13, rax
+mov rax, r12
+div qword ptr [rsp+56]
+mov r12, rax
 mov qword ptr [rbx+256], 0
 jmp ContractEpilogue
 align 16
@@ -50,7 +64,7 @@
 ret
 L4:
 call qword ptr [ROD]
-short jmp L5
+jmp L5
 align 16
 Error:
 mov qword ptr [rbx+256], 2
@@ -58,4 +72,4 @@
 align 4
 .section ro {#1}
 ROD:
-.db 0xD0, 0x78, 0x8D, 0xE6, 0x8A, 0x5F, 0x00, 0x00, 0x10, 0xDC, 0x87, 0xE6, 0x8A, 0x5F, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00, 0x0F, 0x0E, 0x0D, 0x0C, 0x0B, 0x0A, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00, 0x0F, 0x0E, 0x0D, 0x0C, 0x0B, 0x0A, 0x09, 0x08, 0x00, 0x00, 0x64, 0xA7, 0xB3, 0xB6, 0xE0, 0x0D, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00
+.db 0xD0, 0xD7, 0x0B, 0xFC, 0xA2, 0x5E, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00, 0x0F, 0x0E, 0x0D, 0x0C, 0x0B, 0x0A, 0x09, 0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01, 0x00, 0x0F, 0x0E, 0x0D, 0x0C, 0x0B, 0x0A, 0x09, 0x08
```
