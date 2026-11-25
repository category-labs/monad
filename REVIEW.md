# Code Review Guide

This document is the review policy for the `monad` C++ repository. It is consumed by:

- The `claude.yml` GitHub Action, which runs Claude as an automated reviewer on PRs.
- Local developers invoking `/review` or asking Claude to review staged changes or a specific PR.

It complements (does not replace) the `/review` and `/security-review` plugin commands. Those skills cover general review mechanics; this file encodes monad-specific expectations.

See also: [`CLAUDE.md`](./CLAUDE.md) for the canonical descriptions of the traits system, PR conventions, and known pitfalls. When this file and `CLAUDE.md` disagree, `CLAUDE.md` wins. When either disagrees with the code on `main` (a renamed identifier, a revision count), trust the code.

## Review Process

You are acting as a reviewer for a proposed code change made by another engineer. Review the pull request and provide inline feedback using the GitHub review system. For each finding, post an inline comment on the specific line(s) of code. After all inline comments, submit an overall review summary with your verdict.

- Submit as `COMMENT` if the patch is correct with only minor issues.
- Submit as `REQUEST_CHANGES` only if there are P0 or P1 blocking issues.
- Keep the summary short: the verdict and one line per P0/P1 finding. Don't restate what the PR does, praise it, or list what you checked.
- On a re-review, don't re-raise a finding the author answered with a reason unless you can show, citing a line, that the reason is wrong.

End the overall summary with: `🤖 Generated with [Claude Code](https://claude.com/claude-code)`

## What to Flag

General guidelines for whether an issue rises to a reviewable finding:

- It meaningfully impacts the correctness, performance, security, or maintainability of the code.
- The finding is discrete and actionable (not a general complaint about the codebase or a combination of unrelated issues).
- Fixing it does not demand a level of rigor that is not present in the rest of the codebase.
- The bug was introduced in the commit (pre-existing bugs should not be flagged).
- The author would likely fix it if they were made aware.
- It does not rely on unstated assumptions about the codebase or author's intent.
- Don't speculate that a change "may" disrupt another part of the codebase — identify the concrete file/function that is provably affected.
- The change is clearly not intentional. If the PR description or commit message indicates the behavior is deliberate, don't flag it.

Repo-specific calibration, learned from findings the team accepted and rejected:

- **Verify claims about code outside the diff.** Before stating what an unchanged function, macro, or vendored library (`third_party/`) does, read it and cite `file:line`. If you can't confirm a claim, ask in the summary instead of posting a finding.
- **Moved code.** When the diff deletes lines and re-adds them elsewhere (a file split, a rename, a port from `third_party/`), review only what changed in the move. New dependencies the moved code introduces are in scope.
- **Stacked PRs and declared follow-ups.** If the description says the PR is part of a stack or that something lands in a named follow-up, review only this PR's change and don't flag the deferred part; add one summary line if the gap is risky in the meantime.
- **Sibling gaps.** When a PR fixes a bug or adds a missing check at one site, look for the same gap at its siblings (the other decoder of the same type, the other length parameter of the same `extern "C"` function, the other precompile with the same input handling, the other execution entry points in §3) and list survivors in the summary, not as inline comments. This is the exception to "pre-existing bugs should not be flagged".

These are defaults; more specific guidance elsewhere in a developer message, user message, file, or this document overrides them.

## Number of Findings

Output all findings that the original author would fix if they knew about them. If no such finding exists, output none — don't pad. Do not stop at the first qualifying finding.

## Priority Levels

Tag each finding with a priority at the start of the title, e.g. `[P1] Un-padding slices along wrong tensor dimensions`.

- `[P0]` — Drop everything. Blocks release, operations, or major usage. Reserved for issues that hold under any reasonable input/environment.
- `[P1]` — Urgent. Must be addressed before merge.
- `[P2]` — Normal. Fix eventually.
- `[P3]` — Nice to have.

Use P0/P1 only when you can name the failure: the CI job or command that breaks, the reachable input that crashes or corrupts, or the consensus divergence. Convention, comment, test-only and dev-tool issues are P2 at most.

## Comment Guidelines

- Clearly state why it's a bug and what scenario/input triggers it.
- Tone: matter-of-fact. Not accusatory, not gushing. No "Great job" or "Thanks for …".
- One paragraph max per comment, no internal line breaks unless needed for a code fragment.
- No code chunks longer than 3 lines. Wrap short snippets in inline code or a block.
- Keep the line range short — ideally the exact line, and never more than 10 lines.
- Use ` ```suggestion` blocks only for concrete replacement code, with no commentary inside. Preserve the exact leading whitespace (spaces vs tabs, count) of the lines being replaced. Do not change outer indentation levels unless that is the fix itself.

## Formatting / Style Nits

Ignore trivial style unless it obscures meaning or violates a documented standard in `CLAUDE.md`, this file, or the `.clang-format` / `.clang-tidy` configs. CI already fails on clang-format, license headers (`.github/workflows/license.sh`), `check-trait-instantiations.py` and clippy; don't post those.

clang-tidy runs in CI only on the directories `scripts/check-clang-tidy.sh` passes it (`category/{async,core,event,mpt,rpc,statesync,vm}` and `zkvm/`). Elsewhere — chiefly `category/execution/`, `category/crypto/`, `cmd/` and `test/` — what it would catch is in scope on lines the diff adds: missing east-`const` (see `CLAUDE.md`), a symbol used without including its header, an include the diff left unused, use-after-move, `std::move` of a `const`, non-`inline` definitions in headers. Post these as one comment per PR listing the lines.

---

## Repo-Specific Review Areas

The following sections override the generic guidance above for monad-specific concerns. Anything here is explicitly in-scope for this repo.

### 1. Traits system

See [`CLAUDE.md`](./CLAUDE.md) (§ "Traits and Explicit Instantiation") for the full rules. CI's `check-trait-instantiations.py` already rejects instantiation macros in headers and the same macro instantiating a function in two TUs.

Flag the following:

- **Wrong macro granularity.** Use `EXPLICIT_EVM_TRAITS` for EVM-only, `EXPLICIT_MONAD_TRAITS` for Monad-only, `EXPLICIT_TRAITS` only when the same implementation serves both. A needlessly broad macro instantiates code that will never be called.
- **`is_monad_trait_v<traits>` / `is_evm_trait_v<traits>` inside `category/execution/ethereum/`.** That includes an `if constexpr` branch, a `requires is_monad_trait_v` clause on a declaration, and a `requires is_evm_trait_v` / `requires is_monad_trait_v` overload pair standing in for the link-time split. The correct pattern is a trait flag, or separate instantiations in `ethereum/*.cpp` and `monad/*.cpp`. The existing one-line guards (`execute_transaction.cpp`, `execute_block_header.cpp`, `block_hash_history.cpp`) are not to be extended. `static_assert(is_evm_trait_v<traits>)` in an EVM-only `ethereum/*.cpp` definition is fine.
- **Revision comparisons in new code.** Gate new fork- or chain-dependent behaviour on a `consteval` flag declared in the `Traits` concept and defined on both `EvmTraits` and `MonadTraits` in `category/vm/evm/traits.hpp`, named after the EIP or MIP it implements (`eip_7702_active()`, `mip_3_active()`, scoped names like `eip_4844_header_active()` for partial adoption). Flag bare `traits::evm_rev()` / `monad_rev()` comparisons outside `traits.hpp` and `static_assert`, and free `has_*<traits>()` helpers. For an Ethereum EIP the Monad flag is `evm_rev() >= MONAD_ETH_<FORK>`, not `Rev >= MONAD_NEXT`.
- **Monad's deliberately false flags.** `MonadTraits` returns `false` from `eip_4844_active()`, `eip_7685_active()`, `eip_7691_active()`, `eip_7918_active()` and `eip_7928_active()`, while `eip_4844_header_active()`, `eip_4844_opcodes_active()`, `eip_4844_precompile_active()` and `eip_7685_header_active()` are true. Read both definitions before suggesting a swap from one gate to another: gating on `eip_4844_active()` turns off the point-evaluation precompile on Monad.
- **The Berlin floor.** `EARLIEST_SUPPORTED_EVM_FORK` is `MONAD_ETH_BERLIN`, so a branch on an earlier revision is always taken: collapse it, keeping `static_assert(traits::evm_rev() >= MONAD_ETH_BERLIN)` where the assumption matters.
- **Runtime checks where `if constexpr (traits::feature_active())` would work.** Feature-flag methods are `consteval`; missing the `constexpr` lets the dead branch leak into the binary.
- **New `ChainContext<traits>` fields added without the right `requires` constraint.** Fields specific to Monad belong in the `is_monad_trait_v<T>` specialization in `monad/chain/monad_chain.hpp`, not the EVM one in `ethereum/chain/chain.hpp`.
- **Runtime `monad_eth_revision` / `monad_revision` values dispatched without `SWITCH_EVM_TRAITS` / `SWITCH_MONAD_TRAITS`.** Hand-rolled switches are easy to miss a revision on when new forks are added.
- **Shipped revisions are frozen.** Every revision in `monad_mainnet.cpp` and `monad_testnet.cpp` replays historical blocks. A change to gas, status codes, logs, state, receipts, encodings or precompile output goes behind a new trait flag and leaves older revisions byte-identical; flag refactors on live paths that change an observable result, even on an edge case. A new header field is a trailing `std::optional` member of `BlockHeader` that `block_rlp.cpp` encodes only when set.
- **Activation timestamps.** When a PR adds or changes a timestamp in `category/execution/monad/chain/monad_{mainnet,testnet,devnet}.cpp` or `ethereum_mainnet.hpp`, decode it (`date -u -d @<ts>`) and flag a mismatch with its comment or the PR description, a timestamp not later than the previous revision's, mainnet before testnet, or a second copy elsewhere.

### 2. FFI boundary (C++ ↔ Rust)

C headers consumed by Rust through bindgen or cxx are the inputs named in `rust/crates/*/build.rs`: `category/rpc/monad_executor.h`, `chain_config.h`, the statesync client/messages/version headers, `category/core/event/*.h`, the exec-event ctypes headers, `log_ffi.h` and `rust/crates/monad-triedb/include/ffi.h`. Breakage here manifests as Rust compile failures (best case) or silent UB across the ABI boundary (worst case).

Flag:

- **Changes to `extern "C"` struct layout, function signatures, or enum values** without the matching change to the in-repo consumers under `rust/crates/` in the same PR — especially adding/removing/reordering fields. Layout changes are ABI breaks. You can't see `monad-bft`; if a downstream change is needed and the description doesn't link one, say so once in the summary, not inline.
- **C++ exceptions propagating across an `extern "C"` boundary** on a per-request path: the `monad_executor_*` submit and decode paths, the override setters in `category/rpc/`, statesync message handling. Those must catch internally and report via return code / out-parameter. Don't flag `std::bad_alloc` or filesystem errors in one-time constructors and openers (`monad_executor_create`, `triedb_open`, process start-up in `cmd/`); those are fail-stop by design.
- **Ownership ambiguity at the boundary.** Who frees the memory? If a C function returns a pointer, the header comment must say whether the caller is responsible for freeing it and with what.
- **RLP encoding changes** for protocol-level types (Block, Transaction, Header, consensus block headers). These serialize across the FFI and across the network; a silent change can desync nodes.
- **Callback pointers without lifetime discipline.** If C++ stores a Rust callback, the Rust side must outlive the C++ side. Flag patterns that don't make this obvious.
- **Persisted and cross-version formats.** A change to what `commit_builder.cpp` writes (receipts, call frames via `rlp::encode_call_frames`), to `category/mpt/detail/db_metadata.hpp`, to snapshot streams (`MONAD_SNAPSHOT_STREAM_VERSION`) or to the statesync protocol (`monad_statesync_protocol_version`) must keep existing databases and peers readable or bump the version, and the PR must say which. A `db_metadata` layout change bumps `MAGIC` and adds an upgrade path. A new startup assertion on DB state must hold for every state an upgrade or recovery tool can leave behind.
- **Operator-visible changes.** Removing or renaming an option of `monad` (`cmd/monad/main.cpp`) or `monad-mpt` (`category/mpt/cli_tool_impl.cpp`), changing a default or the meaning of an accepted value, or accepting an option and then ignoring it needs a line in the PR description for the release notes.

### 3. C++ correctness

The usual C++ landmines, ordered roughly by how often they bite in this repo:

- **Lifetimes** — dangling references from functions returning references to locals or temporaries; `std::string_view` / `std::span` outliving its backing storage; references captured in lambdas that outlive the caller's stack frame; range-based `for` over a temporary container. `ExecuteTransaction`, `ExecuteTransactionNoValidation`, `ExecuteSystemTransaction`, `EvmcHostBase`, `CallTracer` and the state tracers keep constructor arguments as reference members: flag a temporary (`{}`, a literal, a by-value return) passed to one, including through delegating constructors and default arguments. A new class that stores a reference should `= delete` the rvalue overload.
- **Undefined behavior** — signed-integer overflow, OOB indexing (especially in `byte_string`, `bytes32_t` / `Address` conversions), reads of uninitialized members, strict-aliasing violations via `reinterpret_cast`, misuse of `std::bit_cast` across types that differ in size or aren't trivially copyable. Empty inputs often have a null `data()`: CALL and CREATE with no input pass `nullptr`, as do default-constructed views. `memcpy`, `memcmp`, `&p[len - n]` and nonnull third-party APIs on them are UB; guard with `.empty()`.
- **Integer arithmetic** — overflow in `uint64_t` gas math, silent narrowing from `size_t` to `int` / `uint32_t`, mixing signed and unsigned in comparisons, forgetting that `uint256_t` arithmetic wraps mod 2²⁵⁶.
- **Move semantics** — moved-from objects reused without reassignment; `std::move` on `const` (no-op, silently copies); returning a moved local (usually pessimization, occasionally inhibits NRVO).
- **`const` correctness** — accessor methods that should be `const`; parameters passed by non-const reference when not mutated; `const_cast` uses.
- **Exception safety** — functions that allocate or lock mid-construction without ensuring cleanup on throw; missing `noexcept` on move constructors (breaks `std::vector` strong guarantees).
- **`[[nodiscard]]`** — add it to new factory/checked-result functions where ignoring the return value is a bug.
- **Thread safety** — data races on shared state; missing synchronization on fields accessed from multiple fibers or threads; `std::atomic` used with non-default memory orders (often wrong). TSAN builds exist for a reason.
- **Optimistic parallel execution.** `ExecuteTransaction::operator()` runs `execute_impl2` for every transaction concurrently against speculative state, then waits on its predecessor (`prev_.wait()`) and runs `can_merge`, any re-execution and `merge` serially. Don't flag races on state touched only after the wait. Do flag code in the first pass that assumes final state: an assert, throw, log, metric or user-visible error that holds only under sequential execution, a branch on an exact balance that doesn't call `set_validate_exact_balance()`, or a state read that bypasses `State` (`can_merge` only validates what `State` recorded).
- **Assert macros in release builds.** Shipped builds are `RelWithDebInfo`, so `NDEBUG` is set: `MONAD_DEBUG_ASSERT` and `assert()` compile out, and a violated `MONAD_ASSUME` or `std::unreachable()` is UB. CI's `MONAD_COMPILER_TESTING` builds force debug asserts back on, so green tests prove nothing about release. Flag these when they are the only guard for an index, length, buffer bound, or on-disk or consensus invariant; use `MONAD_ASSERT`, or an error when the input is untrusted. Debug asserts on hot-path invariants only a programming error can break are fine. Unreachable branches use `MONAD_ABORT("why")`, not `MONAD_ASSERT(false)`.
- **Asserts reachable from RPC.** `category/rpc/monad_executor.cpp` runs node code on request-controlled data — state and block overrides that can set any balance, nonce, storage or code for any sender (including system contracts), synthetic headers, cancellation and pruned history. That code includes `execute_block`, `execute_block_header`, `execute_block_transactions`, `ExecuteTransaction` / `ExecuteTransactionNoValidation`, `BlockState::can_merge` / `merge`, the tracers in `category/execution/ethereum/trace/`, `TrieRODb`, the RLP decoders and the VM. A new `MONAD_ASSERT` / `MONAD_ABORT` whose condition request data can falsify, in those functions or their callees, is a remote crash of the RPC process: use `MONAD_ASSERT_THROW` or a `Result` error. Flag the same when a PR makes RPC call an existing node function for the first time. Asserts on internal invariants no request can break (trie structure, VM stack, data consensus already validated) are the intended fail-stop; don't ask for graceful handling. Converting to `MONAD_ASSERT_THROW` in shared code is safe: `monad_executor.cpp` catches it per request and `cmd/monad/main.cpp` still exits on `MonadException`.
- **Execution entry points stay in step.** Blocks and transactions are executed by the live runloop (`category/execution/runloop/runloop_monad.cpp`), replay (`runloop_ethereum.cpp`, `runloop_monad_ethblocks.cpp`), RPC (`eth_call_impl`, `eth_simulate_impl` and `eth_trace_block_or_transaction_impl` in `monad_executor.cpp`, each of which calls different pieces of the block pipeline), `ExecuteSystemTransaction`, and the zkVM guest (`zkvm/guest/`). When a PR adds an input (a `BlockHeader` field, a consensus-supplied value, a `ChainContext` member) or a step (a system call, validation, finalization such as `destruct_touched_dead`, a tracer or event hook) on one path, check the others and flag any that leaves it defaulted, skips it, or calls the Ethereum variant where the live path calls the Monad one.
- **Paired implementations.** The interpreter (`category/vm/interpreter/`) and compiler (`category/vm/compiler/`), native precompiles and their `zkvm/` shadows, and `revert_transaction` and `revert_transaction_cached` must give identical results. When a PR changes one side, check the other or a test that pins both. Flag a change that relaxes a differential oracle to make a divergence pass (`test/vm/fuzzer/assertions.cpp`, fuzzer models, test-runner skip lists) unless it is scoped and carries an issue.
- **zkVM portability.** `category/vm/{evm,runtime,interpreter}`, `category/execution` and parts of `category/core` are also built for the RISC-V zkVM guest (`zkvm/guest/CMakeLists.txt`); `category/vm/compiler` is not. Flag x86-only code there (`<immintrin.h>`, `_mm*` intrinsics, inline x86 asm, MULX/ADX) without a feature-macro fallback (`#ifdef __AVX2__`, `__BMI2__`) or a shadow under `zkvm/category/`. zkVM-only behaviour is selected at compile time (template parameter or shadow), not with a runtime branch in shared code.
- **Status-code domains.** Each `quick_status_code_from_enum` specialization needs a freshly generated `domain_uuid`; a copied UUID makes two domains compare equal.
- **VM interpreter `must-tail` discipline** — in `category/vm/interpreter/`, every handler dispatches through `MONAD_VM_NEXT` / `MONAD_VM_MUST_TAIL`. Flag a handler or dispatch path that calls the next handler without it, or moves work after the dispatch.
- **Sanitizer compatibility** — code that deliberately trips UBSAN/ASAN (e.g. overaligned placement new, `reinterpret_cast` through unrelated types) needs a comment explaining why.

### 4. Testing

- **New source under `category/` should have a test** where that directory keeps its tests (a sibling `*_test.cpp`, the directory's `test/` subfolder, or `test/vm/unit/` for `category/vm/`) unless it's a trivial change or covered by an existing cross-cutting test in `test/`.
- **Use `monad_add_test` / `monad_add_test_folder` / `monad_add_test_death`** — don't reinvent the test wiring. See `CLAUDE.md` § "Adding Tests".
- **Test resource paths** should go through `test_resource::test_data_dir` etc., not hardcoded relative paths.
- **Sanitizer-dependent code or tests** gate on `MONAD_HAVE_ASAN` (`category/core/asan.h`); unsupported sanitizer/compiler pairs are excluded in the CI matrix, not per test.
- **Flaky tests** introduced as `DISABLED_*` should have a linked issue or TODO identifying the owner.
- **Fork-dependent tests run over the revision matrix.** Use the typed fixtures in `test/unit/common/include/monad/test/traits_test.hpp` (`TraitsTest`, `MonadTraitsTest`, `EvmTraitsTest`, `MonadRevisionTypesSince<…>`, `EvmRevisionTypesSince<…>`) with expectations branched on `TestFixture::Trait::<flag>()`. Flag new tests of gated behaviour that pin one revision, or that cover only the post-activation side of a new gate.
- **Limits are tested at the limit and just past it** (`max_code_size()`, `max_initcode_size()`, memory and staking caps, gas thresholds). Test bytecode is built with `EvmBuilder` (`category/vm/utils/evm-as/builder.hpp`), not hex byte literals.
- **VM semantics or gas changes run on both engines**, e.g. `execute_and_compare` in `test/vm/unit/evm_fixture.hpp`; the compiler charges gas per basic block, so interpreter-only or spec-test coverage misses compiler bugs. New emitter paths need cases in `test/vm/unit/emitter_tests.cpp`. `test/vm/unit` runs via `scripts/vm/test.sh`, not ctest.
- **RPC-only output needs a pinning test.** `test/ethereum_test` covers consensus execution only. `eth_simulateV1`, `eth_call` overrides, the call/prestate/state-diff tracers and exec-event conversion are pinned only by `category/rpc/monad_executor_test.cpp`, `category/execution/ethereum/test/test_call_trace.cpp` and `category/execution/ethereum/trace/state_tracer_test.cpp`. When a PR changes that output, directly or via an EIP that changes logs, SELFDESTRUCT, transfers or header fields, flag a missing test there. Geth is the reference for these APIs; don't claim behaviour "matches geth" unless you have read geth's code.
- **Asking for tests.** Before asking for a new unit test, check whether the path already runs under `test/ethereum_test`, replay or a fuzzer, and say what they miss. Don't ask for tests of stats counters, logging, dev-tool output, or race windows that can't be forced deterministically. A test that would still pass with the bug is a better finding than a missing test.
- **Tests, fuzzers, scripts and dev tools** (`test/`, `*_test.cpp`, `test/vm/fuzzer/`, `cmd/vm/mce/`, `category/vm/utils/`, `scripts/`): flag what makes them give a wrong answer — a test that passes with the bug, a fuzzer that masks a divergence, a CI step that passes when it should fail, flakiness, UB. Robustness to malformed CLI arguments, temp-file hygiene and performance there are P3 at most.

### 5. Style & conventions

Most style is enforced by `clang-format` (`/format`) and `clang-tidy` (`/lint`); see "Formatting / Style Nits" for where tidy doesn't run. Beyond that, flag:

- **`namespace monad { … }` written directly** instead of `MONAD_NAMESPACE_BEGIN/END` from `<category/core/config.hpp>` in a directory that uses the macros. `category/vm/` opens `namespace monad::vm` directly everywhere, and some directories mix both; match the neighbouring files.
- **Header guards (`#ifndef`/`#define`/`#endif`)** instead of `#pragma once`.
- **Include paths without the `category/` prefix** — e.g. `#include "hex.hpp"` instead of `#include <category/core/hex.hpp>`.
- **New private members without a trailing underscore** — e.g. `int count;` instead of `int count_;`. Some older code violates this; new code should not.
- **Forward declarations.** The team has no settled preference between a forward declaration and an include; flag only a forward declaration next to an include of the header that defines it.
- **Naming** — `snake_case` for functions, `PascalCase` for types (noting that older code has `snake_case` types; match the surrounding file). A type is C or C++, not both: a C type is `monad_snake_case` in a `.h` under `extern "C"` with only C members; a C++ type is `PascalCase` in a `monad::` namespace in a `.hpp`. Flag a `.h` that uses C++-only constructs outside `#ifdef __cplusplus`.
- **Comment calibration.** The team removes comments; new code defaults to none. Flag comments the diff adds that restate the code or an assert, narrate history ("previously", "the bug we fixed", "load-bearing"), repeat the same design explanation at several sites, annotate one entry of a table whose neighbours have none, or add rationale to existing code the PR doesn't otherwise change. Trait flags in `traits.hpp` take no comment unless the name can't carry the meaning. A comment that explains a non-obvious why (an invariant, an ordering requirement, a deliberate divergence from the spec or from geth) is wanted; if it is long, at most suggest tightening it. Don't ask authors to add comments except to document an FFI contract (§2). Implementation rationale goes in the `.cpp`; the caller-facing contract goes on the header declaration. Post one comment per PR listing the lines to trim.
- **Stale references.** When the diff renames, moves or deletes a function, type, field, file, script, CMake option, trait flag or dependency, grep the whole tree for the old name — code comments, `*.md`, `CLAUDE.md`, `.claude/`, `.clang-tidy`, CMake, Dockerfiles and `.github/workflows/` — and flag each survivor. Also flag comments the diff adds or leaves that contradict the adjacent code: an inverted condition, a wrong bound, a named caller that doesn't call it.
- **Orphaned code.** Flag functions, overloads and wrappers whose last caller the diff removed, members only tests read, parameters the body ignores (including an unused `template <Traits traits>` parameter, which compilers don't warn on), enumerators nothing returns, and CMake dependencies nothing uses. `extern "C"` entry points consumed from Rust count as called. "Used in a follow-up PR" is not a caller.
- **Monad vocabulary.** Outside direct evmc API calls, new code uses `Address`, `bytes32_t`, `byte_string` / `byte_string_view`, `uint256_t`, `monad::from_hex`, `monad::literals` (`_address`, `_bytes32`, `_u256`) and `load_be` / `store_be_as` from `category/core/int.hpp` — not `evmc::address`, `evmc::bytes32`, `std::basic_string<uint8_t>`, `intx::`, `evmc::from_hex`, `evmc::literals` or hand-rolled byte-order loops.

### 6. PR hygiene

See [`CLAUDE.md`](./CLAUDE.md) § "PR Conventions".

- **Single-commit PR** unless the PR contains genuinely distinct changes (e.g. an unrelated lint fix preceding a feature). Multi-commit PRs with "fix review comments" or "wip" commits should be squashed.
- **Rebased on `origin/main`** with no merge commits.
- **Pre-merge checks passing**: `/format`, `/lint` (`check-clang-tidy.sh` + `check-trait-instantiations.py`), and `/test`. If CI is red, the PR is not ready regardless of what the diff looks like.
- **Scope discipline** — call out unrelated refactors or cleanups that should be in their own PR. Flag as `[P3]` unless the scope creep obscures the intended change.

### 7. Security

For anything that parses untrusted input (network messages, RLP decoders, EVM opcode implementations, RPC request parsing), apply extra scrutiny:

- Input-length validation before indexing.
- Integer overflow on length / size fields coming from the wire.
- Recursion depth bounds (RLP, nested EVM calls, trie traversal).
- Resource exhaustion (unbounded allocation driven by a network-controlled size).
- Timing side channels in signature verification, key comparison, etc.
- **Execution must never reject what consensus accepts.** Consensus finalizes a block before execution runs it, so a new or tightened rejection in execution — a new `TransactionError` / `BlockError` / `MonadTransactionError` / `MonadBlockError` path in `validate_*.cpp`, a stricter decoder in `category/execution/ethereum/core/rlp/`, a lower limit trait, a moved activation timestamp, an assert or throw on block contents — halts every node unless consensus enforces the same rule at the same revision. For a revision that has an activation timestamp on mainnet or testnet, flag it as P1 unless the PR names the consensus-side counterpart; for `MONAD_NEXT`-only behaviour, note it once in the summary. The converse (consensus stricter than execution) is only hygiene. Values both sides compute (limits, delays, header fields) cite their counterpart or assert agreement.
- Decoders check lengths before calling helpers like `to_bytes`, `unaligned_load` or `.at()`, and reject trailing bytes (#2370). `decode_unsigned<T>` uses the declared type of the field it fills: fee, value, `chain_id` and signature fields are `uint256_t`.
- Accepted encodings are canonical: re-encoding gives the same bytes, and anything geth or alloy rejects is rejected here too (#2245, #1364).
- Charge gas before doing work, and bound any work gas doesn't price (#2027). Don't copy an attacker-sized input to read a fixed-size prefix for the gas computation.
- Precompile input shorter than a field is right-padded with zeros, and the gas and execute functions read the same padded view (#2045). An input-handling fix applies to every precompile sharing the pattern, including the `zkvm/` shadows.
- Monad's stateful precompiles (`StakingContract`, `ReserveBalanceContract`): new methods start with `function_not_payable` unless meant to take value, get their gas in `precompile_dispatch`, and fail with a `Result` error (which reverts), never a `MONAD_ASSERT` or unchecked arithmetic on stored values. Don't relax the kind/flags rejection in `check_call_monad_precompile`.
- Reserve balance (`category/execution/monad/reserve_balance.cpp`, the `ChainContext` sender sets, the `revert_transaction` calls in `execute_message.cpp`): the check must cover both top-level paths (create and call), every account whose balance the transaction can lower (including EIP-7702 authorities and delegated accounts), and must not assert on balances, which can differ under speculative execution from what consensus checked (#2096).
- In `category/vm/compiler/`, any deployable bytecode is input: a condition some contract can trigger must not be a `MONAD_ASSERT` / `MONAD_ABORT`. Throw `Emitter::Error` or `Nativecode::SizeEstimateOutOfBounds` so compilation falls back to the interpreter.
- zkVM witness decoders (`rlp/execution_witness.*`, `db/offset_trie.*`, `db/partial_trie_db.*`, `mpt/merkle/compact_encode.hpp`): every length, offset and tag is prover-controlled; bounds-check before any `memcpy` or view. An abort only yields no proof; a read past the blob is a soundness bug.
- Hash tables keyed by attacker-chosen data use the per-process seeded hash, `seeded_fast_hash` (#2462).
- Lengths passed across `extern "C"` are checked against the buffer they describe (#2203).
- High-s signatures are rejected everywhere except the `ecrecover` and P256 precompiles, whose specs accept them (#2026).

`SECURITY.md` at the repo root has the disclosure policy; findings with security impact should also be flagged on the PR.

### 8. Subsystem notes

- **VM x86 emitter (`category/vm/compiler/ir/x86/`).** Gas decrements clobber EFLAGS: call `discharge_deferred_comparison()` before emitting one while a deferred comparison is live, and don't branch on flags after a zero-gas decrement (it emits nothing). Work that scales with an operand is charged and checked before it runs. Constants use `bin<N>`, not `Bin::unsafe_from`.
- **MPT metadata (`category/mpt/detail/db_metadata.hpp`).** It is mmapped and read concurrently by read-only processes: every field access goes through the `std::atomic_ref` accessors (release on publish, acquire on read), never a plain load/store or `reinterpret_cast<std::atomic<T> *>`. The history fields (`version_lower_bound`, `next_version`, `auto_expire_version`, compaction offsets) have several writers — the upsert path in `update_aux.cpp`, `move_trie_version_forward`, `rewind_to_version`, the `monad-mpt` CLI and statesync. When a PR changes one, check the others keep the version window and the `INVALID_*` sentinels consistent, and ask for a `category/mpt/test/` case.

---

## Overall Verdict

End the review with an explicit correctness verdict:

> **Verdict:** CORRECT _or_ NEEDS CHANGES

`CORRECT` means: existing code and tests will not break, and the patch is free of P0 / P1 bugs. Non-blocking issues (style, formatting, typos, documentation, nits) do not make a patch incorrect.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
