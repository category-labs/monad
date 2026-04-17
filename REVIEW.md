# Code Review Guide

This document is the review policy for the `monad` C++ repository. It is consumed by:

- The `claude.yml` GitHub Action, which runs Claude as an automated reviewer on PRs.
- Local developers invoking `/review` or asking Claude to review staged changes or a specific PR.

It complements (does not replace) the `/review` and `/security-review` plugin commands. Those skills cover general review mechanics; this file encodes monad-specific expectations.

See also: [`CLAUDE.md`](./CLAUDE.md) for the canonical descriptions of the traits system, PR conventions, and known pitfalls. When this file and `CLAUDE.md` disagree, `CLAUDE.md` wins.

## Review Process

You are acting as a reviewer for a proposed code change made by another engineer. Review the pull request and provide inline feedback using the GitHub review system. For each finding, post an inline comment on the specific line(s) of code. After all inline comments, submit an overall review summary with your verdict.

- Submit as `COMMENT` if the patch is correct with only minor issues.
- Submit as `REQUEST_CHANGES` only if there are P0 or P1 blocking issues.

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

These are defaults; more specific guidance elsewhere in a developer message, user message, file, or this document overrides them.

## Number of Findings

Output all findings that the original author would fix if they knew about them. If no such finding exists, output none — don't pad. Do not stop at the first qualifying finding.

## Priority Levels

Tag each finding with a priority at the start of the title, e.g. `[P1] Un-padding slices along wrong tensor dimensions`.

- `[P0]` — Drop everything. Blocks release, operations, or major usage. Reserved for issues that hold under any reasonable input/environment.
- `[P1]` — Urgent. Must be addressed before merge.
- `[P2]` — Normal. Fix eventually.
- `[P3]` — Nice to have.

## Comment Guidelines

- Clearly state why it's a bug and what scenario/input triggers it.
- Tone: matter-of-fact. Not accusatory, not gushing. No "Great job" or "Thanks for …".
- One paragraph max per comment, no internal line breaks unless needed for a code fragment.
- No code chunks longer than 3 lines. Wrap short snippets in inline code or a block.
- Keep the line range short — ideally the exact line, and never more than 10 lines.
- Use ` ```suggestion` blocks only for concrete replacement code, with no commentary inside. Preserve the exact leading whitespace (spaces vs tabs, count) of the lines being replaced. Do not change outer indentation levels unless that is the fix itself.

## Formatting / Style Nits

Ignore trivial style unless it obscures meaning or violates a documented standard in `CLAUDE.md` or the `.clang-format` / `.clang-tidy` configs. Formatting is enforced by `/format` and `/lint`; don't duplicate what the tools catch.

---

## Repo-Specific Review Areas

The following sections override the generic guidance above for monad-specific concerns. Anything here is explicitly in-scope for this repo.

### 1. Traits system

See [`CLAUDE.md`](./CLAUDE.md) (§ "Traits and Explicit Instantiation") for the full rules.

Flag the following:

- **Instantiation macros in header files.** Macros like `EXPLICIT_EVM_TRAITS` must only appear in `.cpp` files. In a header they cause ODR violations.
- **Same function instantiated by the same macro in multiple TUs.** `check-trait-instantiations.py` catches this, but if it appears in a diff it's worth pointing out early. The `EvmTraits` in one TU + `MonadTraits` in another pattern (the ethereum/ vs monad/ split) is allowed and expected.
- **Wrong macro granularity.** Use `EXPLICIT_EVM_TRAITS` for EVM-only, `EXPLICIT_MONAD_TRAITS` for Monad-only, `EXPLICIT_TRAITS` only when the same implementation serves both. A needlessly broad macro instantiates code that will never be called.
- **Branching on `is_monad_trait_v<traits>` / `is_evm_trait_v<traits>` inside `category/execution/ethereum/`.** The correct pattern is separate instantiations in `ethereum/*.cpp` and `monad/*.cpp`. A narrow exception exists for one-line initialization guards (see `execute_transaction.cpp`, `execute_block.cpp`) — those are acceptable but should be rare.
- **Runtime checks where `if constexpr (traits::feature_active())` would work.** All trait methods are `consteval`; missing the `constexpr` lets the dead branch leak into the binary.
- **New `ChainContext<traits>` fields added without the right `requires` constraint.** Fields specific to Monad belong in the `is_monad_trait_v<T>` specialization, not the generic struct.
- **Runtime `evmc_revision` / `monad_revision` values dispatched without `SWITCH_EVM_TRAITS` / `SWITCH_MONAD_TRAITS`.** Hand-rolled switches are easy to miss a revision on when new forks are added.

### 2. FFI boundary (C++ ↔ Rust)

The C headers in `category/rpc/monad_executor.h`, `category/statesync/statesync_*.h`, and the TrieDB driver are consumed by Rust via bindgen. Breakage here manifests as Rust compile failures (best case) or silent UB across the ABI boundary (worst case).

Flag:

- **Changes to `extern "C"` struct layout, function signatures, or enum values** without a corresponding update in `monad-bft/` — especially adding/removing/reordering fields. Layout changes are ABI breaks.
- **C++ exceptions propagating across an `extern "C"` boundary.** Any function exposed via the C ABI must catch all exceptions internally and report errors via return code / out-parameter. `noexcept` on the declaration is preferable.
- **Ownership ambiguity at the boundary.** Who frees the memory? If a C function returns a pointer, the header comment must say whether the caller is responsible for freeing it and with what.
- **RLP encoding changes** for protocol-level types (Block, Transaction, Header, consensus block headers). These serialize across the FFI and across the network; a silent change can desync nodes.
- **Callback pointers without lifetime discipline.** If C++ stores a Rust callback, the Rust side must outlive the C++ side. Flag patterns that don't make this obvious.

### 3. C++ correctness

The usual C++ landmines, ordered roughly by how often they bite in this repo:

- **Lifetimes** — dangling references from functions returning references to locals or temporaries; `std::string_view` / `std::span` outliving its backing storage; references captured in lambdas that outlive the caller's stack frame; range-based `for` over a temporary container.
- **Undefined behavior** — signed-integer overflow, OOB indexing (especially in `byte_string`, `Bytes32` / `Address` conversions), reads of uninitialized members, strict-aliasing violations via `reinterpret_cast`, misuse of `std::bit_cast` across types that differ in size or aren't trivially copyable.
- **Integer arithmetic** — overflow in `uint64_t` gas math, silent narrowing from `size_t` to `int` / `uint32_t`, mixing signed and unsigned in comparisons, forgetting that `uint256_t` arithmetic wraps mod 2²⁵⁶.
- **Move semantics** — moved-from objects reused without reassignment; `std::move` on `const` (no-op, silently copies); returning a moved local (usually pessimization, occasionally inhibits NRVO).
- **`const` correctness** — accessor methods that should be `const`; parameters passed by non-const reference when not mutated; `const_cast` uses.
- **Exception safety** — functions that allocate or lock mid-construction without ensuring cleanup on throw; missing `noexcept` on move constructors (breaks `std::vector` strong guarantees).
- **`[[nodiscard]]`** — add it to new factory/checked-result functions where ignoring the return value is a bug.
- **Thread safety** — data races on shared state; missing synchronization on fields accessed from multiple fibers or threads; `std::atomic` used with non-default memory orders (often wrong). TSAN builds exist for a reason.
- **VM interpreter `must-tail` discipline** — any change in `category/vm/` that converts a tail call into a non-tail call risks stack overflow on long bytecode chains. Flag changes that move work after a recursive/dispatched call.
- **Sanitizer compatibility** — code that deliberately trips UBSAN/ASAN (e.g. overaligned placement new, `reinterpret_cast` through unrelated types) needs a comment explaining why.

### 4. Testing

- **New source under `category/` should have a matching `*_test.cpp`** (same directory) unless it's a trivial change or covered by an existing cross-cutting test in `test/`.
- **Use `monad_add_test` / `monad_add_test_folder` / `monad_add_test_death`** — don't reinvent the test wiring. See `CLAUDE.md` § "Adding Tests".
- **Test resource paths** should go through `test_resource::test_data_dir` etc., not hardcoded relative paths.
- **Sanitizer-specific tests** (ASAN/TSAN/UBSAN) must be tagged so they're excluded from builds where the sanitizer breaks (e.g. ASAN + VM interpreter under GCC).
- **Flaky tests** introduced as `DISABLED_*` should have a linked issue or TODO identifying the owner.

### 5. Style & conventions

Most style is enforced by `clang-format` (`/format`) and `clang-tidy` (`/lint`). Beyond that, flag:

- **`namespace monad { … }` written directly** instead of `MONAD_NAMESPACE_BEGIN/END` from `<category/core/config.hpp>`.
- **Header guards (`#ifndef`/`#define`/`#endif`)** instead of `#pragma once`.
- **Include paths without the `category/` prefix** — e.g. `#include "hex.hpp"` instead of `#include <category/core/hex.hpp>`.
- **New private members without a trailing underscore** — e.g. `int count;` instead of `int count_;`. Some older code violates this; new code should not.
- **Forward declarations where an `#include` would do** — especially for friend types. Prefer including the header.
- **Naming** — `snake_case` for functions, `PascalCase` for types (noting that older code has `snake_case` types; match the surrounding file).
- **Comments that restate the code.** Good comments explain *why*; they don't narrate *what*. Flag multi-line comment blocks that add nothing a reader couldn't derive from the identifier.

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

`SECURITY.md` at the repo root has the disclosure policy; findings with security impact should also be flagged on the PR.

---

## Overall Verdict

End the review with an explicit correctness verdict:

> **Verdict:** CORRECT _or_ NEEDS CHANGES

`CORRECT` means: existing code and tests will not break, and the patch is free of P0 / P1 bugs. Non-blocking issues (style, formatting, typos, documentation, nits) do not make a patch incorrect.

🤖 Generated with [Claude Code](https://claude.com/claude-code)
