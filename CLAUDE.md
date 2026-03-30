# monad (C++) Development Guide

## Quick Reference

```bash
# Configure (default GCC 15, RelWithDebInfo, AVX2)
CC=gcc-15 CXX=g++-15 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo

# Build
cmake --build build --parallel

# Test
ctest --test-dir build --output-on-failure --timeout 500 --parallel
pytest-3 --pyargs monad

# Format
scripts/apply-clang-format.sh

# Lint (requires Clang+Debug build with MONAD_COMPILER_TESTING — use /lint skill)
scripts/check-clang-tidy.sh -p build
python3 scripts/check-trait-instantiations.py
```

Use `/build`, `/test`, `/lint`, `/format`, `/fuzz` skills for full options (sanitizers, Clang, specific targets, etc.).

### Toolchain files (`category/core/toolchains/`)

| Toolchain | Compiler | Flags |
|-----------|----------|-------|
| `gcc-avx2.cmake` | GCC or Clang | `-march=haswell` (default) |
| `gcc-avx512.cmake` | GCC or Clang | `-march=skylake-avx512` |
| `gcc-asan.cmake` | GCC only | ASAN + UBSAN. **Breaks VM interpreter** (must-tail incompatibility) |
| `gcc-tsan.cmake` | GCC only | TSAN |
| `clang-tsan.cmake` | Clang only | TSAN |
| `clang-fuzz.cmake` | Clang only | ASAN + UBSAN + fuzzing instrumentation |

## PR Conventions

- **Single-commit PRs** unless there are very distinct changes (e.g. a lint fix followed by a feature). Squash/rebase before merging.
- **Rebase on main** — no merge commits. Use `git rebase origin/main` before pushing.
- Before creating a PR, ensure these checks pass:
  1. **Formatting** (`/format`): `clang-format-19` on all source files
  2. **Linting** (`/lint`): clang-tidy with const-correctness plugin, and trait instantiation checks
  3. **Tests** (`/test`): ctest unit tests and pytest

## Traits and Explicit Instantiation

All execution code is templated on a `Traits` parameter that encodes the chain revision at compile time. This is the central abstraction for supporting both standard Ethereum revisions and Monad-specific revisions without runtime branching.

### Trait types

There are two trait families, defined in `category/vm/evm/traits.hpp`:

- **`EvmTraits<evmc_revision>`** — one per EVM fork (HOMESTEAD through OSAKA, 14 total)
- **`MonadTraits<monad_revision>`** — one per Monad revision (MONAD_ZERO through MONAD_NEXT, 11 total)

Both satisfy the `Traits` concept, which exposes `consteval` methods for:
- `evm_rev()` — the underlying EVM revision (MonadTraits maps to an EVM rev, e.g. MONAD_FOUR+ maps to EVMC_PRAGUE)
- Feature flags like `eip_2929_active()`, `eip_4844_active()`, `mip_3_active()`
- Constants like `cold_account_cost()`, `max_code_size()`

Because all methods are `consteval`, `if constexpr` on trait queries is zero-cost — dead branches are eliminated at compile time.

### How dispatch works

Runtime revision values are mapped to the correct template instantiation via switch macros in `category/vm/evm/switch_traits.hpp`:

```cpp
// At a call site that has a runtime evmc_revision:
SWITCH_EVM_TRAITS(execute_transaction, chain, tx, header, ...);

// At a call site that has a runtime monad_revision:
SWITCH_MONAD_TRAITS(execute_transaction, chain, tx, header, ...);
```

Each expands to a switch statement that calls `execute_transaction<EvmTraits<EVMC_OSAKA>>(...)`, `execute_transaction<EvmTraits<EVMC_PRAGUE>>(...)`, etc.

### Explicit instantiation macros

Templates must be explicitly instantiated in `.cpp` files using macros from `category/vm/evm/explicit_traits.hpp`:

| Macro | What it instantiates | Revisions |
|-------|---------------------|-----------|
| `EXPLICIT_EVM_TRAITS(f)` | Free function `f` | 14 EVM revisions |
| `EXPLICIT_MONAD_TRAITS(f)` | Free function `f` | 11 Monad revisions |
| `EXPLICIT_TRAITS(f)` | Free function `f` | All 25 |
| `EXPLICIT_EVM_TRAITS_CLASS(c)` | Class template `c` | 14 EVM revisions |
| `EXPLICIT_MONAD_TRAITS_CLASS(c)` | Class template `c` | 11 Monad revisions |
| `EXPLICIT_MONAD_TRAITS_STRUCT(c)` | Struct template `c` | 11 Monad revisions |
| `EXPLICIT_TRAITS_CLASS(c)` | Class template `c` | All 25 |
| `EXPLICIT_EVM_TRAITS_MEMBER(f)` | Member function `f` | 14 EVM revisions |
| `EXPLICIT_MONAD_TRAITS_MEMBER(f)` | Member function `f` | 11 Monad revisions |
| `EXPLICIT_TRAITS_MEMBER(f)` | Member function `f` | All 25 |

**Rules:**
- Instantiation macros go in `.cpp` files only, never in headers.
- A function/class must not be instantiated by the same macro in multiple translation units. Using `EXPLICIT_EVM_TRAITS` in one TU and `EXPLICIT_MONAD_TRAITS` in another for the same function IS allowed — that's the ethereum/monad split pattern. The `check-trait-instantiations.py` lint enforces this.
- Choose the narrowest macro: use `EXPLICIT_EVM_TRAITS` for EVM-only code, `EXPLICIT_MONAD_TRAITS` for Monad-only code, `EXPLICIT_TRAITS` only when the same implementation serves both.

### The ethereum/ vs monad/ convention

The `category/execution/` tree is split into `ethereum/` and `monad/` subdirectories. The key convention:

**Do not branch on `is_monad_trait_v` vs `is_evm_trait_v` inside `ethereum/` code.** Instead, use the trait system to dispatch different behavior via separate instantiations.

The pattern is:
1. **Declare** the function template in `ethereum/` with a `Traits` parameter
2. **Provide a default implementation** in `ethereum/*.cpp`, instantiated with `EXPLICIT_EVM_TRAITS`
3. **Provide the Monad override** in `monad/*.cpp`, instantiated with `EXPLICIT_MONAD_TRAITS`

Example — `revert_transaction`:

```cpp
// ethereum/reserve_balance.cpp — EVM default: no-op
template <Traits traits>
bool revert_transaction(Address const &, Transaction const &,
    uint256_t const &, uint64_t, State &, ChainContext<traits> const &) {
    return false;
}
EXPLICIT_EVM_TRAITS(revert_transaction);

// monad/reserve_balance.cpp — Monad override: real implementation
template <Traits traits>
bool revert_transaction(Address const &sender, Transaction const &tx,
    uint256_t const &base_fee_per_gas, uint64_t i, State &state,
    ChainContext<traits> const &ctx) {
    // ... actual reserve balance revert logic ...
}
EXPLICIT_MONAD_TRAITS(revert_transaction);
```

The linker picks the right instantiation — EVM callers get the no-op, Monad callers get the real implementation. No `if constexpr (is_monad_trait_v<traits>)` needed in the shared code.

**When branching IS acceptable:**
- Using `if constexpr` on **feature flags** like `traits::eip_2929_active()` or `traits::evm_rev() >= EVMC_ISTANBUL` is fine — these are per-revision decisions, not monad-vs-EVM decisions.
- Using `requires is_monad_trait_v<traits>` constraints on functions that only make sense for Monad (e.g. `can_sender_dip_into_reserve`) is fine — these aren't branches, they're compile-time constraints that prevent misuse.
- **Pragmatic exceptions** exist in `ethereum/` where the separate-instantiation pattern would be unwieldy — e.g. one-line initialization guards like `if constexpr (is_monad_trait_v<traits>) { init_reserve_balance_context(...); }` in `execute_transaction.cpp` and `execute_block.cpp`. Prefer the split-instantiation pattern for new code, but a guarded call is acceptable when the alternative would be splitting an entire function just to add one Monad-specific line.

### ChainContext specialization

`ChainContext<traits>` is the main type that differs between EVM and Monad. It's forward-declared in `ethereum/chain/chain.hpp` and specialized via `requires` constraints:

- `ChainContext<T> requires is_evm_trait_v<T>` — empty struct (no extra context needed)
- `ChainContext<T> requires is_monad_trait_v<T>` — contains sender sets, authorities, etc. (defined in `monad/chain/monad_chain.hpp`)

Functions in `ethereum/` that take `ChainContext<traits> const &` work with both — for EVM traits it's an empty struct, for Monad traits it carries the Monad-specific data.

### Monad revisions

Defined in `category/vm/evm/monad/revision.h`:

| Revision | Underlying EVM | Notable changes |
|----------|---------------|-----------------|
| MONAD_ZERO–THREE | EVMC_CANCUN | Base Monad; MONAD_TWO raises max code size to 128KB |
| MONAD_FOUR–EIGHT | EVMC_PRAGUE | EIP-7951 active; larger initcode; Monad pricing v1 at MONAD_SEVEN |
| MONAD_NINE+ | EVMC_OSAKA | MIP-3 active |
| MONAD_NEXT | EVMC_OSAKA | Future/development |

Key differences from EVM traits: EIP-4844 (blob gas) is always disabled, cold account/storage costs are higher (Monad pricing), and code size limits are larger (128KB code, 256KB initcode). See the [Monad changelog](https://docs.monad.xyz/developer-essentials/changelog) for user-facing details of each revision.

## Code Conventions

### Namespaces

All code uses macros from `category/core/config.hpp` — do not write `namespace monad {` directly:

```cpp
#include <category/core/config.hpp>

MONAD_NAMESPACE_BEGIN
// production code
MONAD_NAMESPACE_END

MONAD_ANONYMOUS_NAMESPACE_BEGIN
// file-local helpers
MONAD_ANONYMOUS_NAMESPACE_END
```

Test code uses `MONAD_TEST_NAMESPACE_BEGIN/END` (from `monad/test/config.hpp`), which nests under `monad::test`.

### Headers and includes

- Always `#pragma once` (not `#ifndef` guards)
- Include paths use the full `category/` prefix: `#include <category/core/hex.hpp>`
- Naming: `snake_case` for functions, `PascalCase` for types (some older code uses `snake_case` types), trailing `_` for private members

## Adding Tests

Tests use Google Test. CMake helper functions are defined in root `CMakeLists.txt`:

| CMake function | Usage |
|---------------|-------|
| `monad_add_test(name source.cpp)` | Single test executable (auto-links GTest + `monad_execution`, includes custom main) |
| `monad_add_test_folder(dir/)` | Auto-discovers `test_*.cpp` and `*_test.cpp` in a directory, creates one executable per file |
| `monad_add_test_death(name FAIL_REGEX "..." SOURCES ...)` | Death test — passes if output matches regex |

New library/executable targets should call `monad_compile_options(target)` to apply the standard C++23 flags, warnings, and compile definitions. Most targets link against `monad_execution` — the aggregate library that bundles all of `category/`.

Test files live in two places:
- **Alongside source** in `category/` subdirectories (e.g., `category/core/hex_test.cpp`, `category/execution/ethereum/evm_test.cpp`)
- **In `test/`** for cross-cutting or suite-level tests (e.g., `test/ethereum_test/`, `test/vm/`)

Test data paths are available via generated header `test/test_resource_data.h`:
- `test_resource::test_data_dir` — `test/`
- `test_resource::vm_data_dir` — `test/vm/data/`
- `test_resource::build_dir` — build output directory

## Known Pitfalls

- **GCC + ASAN breaks the VM interpreter** — GCC's ASAN implementation is incompatible with the must-tail calling convention used by the interpreter. Use Clang for ASAN builds when working on VM code.
- **`third_party/evmone` is not a submodule** — it's gitignored and must be manually cloned from `category-labs/evmone` (branch `v0.18.0-category`). Only needed for `MONAD_COMPILER_TESTING`, `MONAD_COMPILER_BENCHMARKS`, lint, and fuzz builds.
- **Submodules in worktrees** — Fresh clones and git worktrees need `git submodule update --init --recursive` before configuring.
- **Always use toolchain files** — Passing bare `-march=haswell` via `CFLAGS`/`CXXFLAGS` misses assembly sources (e.g., `keccak_impl.S`). Use `-DCMAKE_TOOLCHAIN_FILE=...` instead.
