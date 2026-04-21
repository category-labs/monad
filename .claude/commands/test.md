Run tests for the monad C++ project.

## Arguments

The user may pass arguments like:
- A test filter string — passed as `-R <filter>` to ctest (e.g., `monad_trie`, `EvmcHost`)
- No arguments — run all tests

## Instructions

You are running tests for the monad C++ project located at $CWD.

### Prerequisites

A build must exist in `build/`. If it doesn't, tell the user to run `/build` first.

### Steps

1. **Run ctest:**
   ```bash
   ctest --test-dir build --output-on-failure --timeout 500 --parallel
   ```
   If the user specified a test filter, add `-R <filter>`.

2. **Run the Python test layer:**
   ```bash
   pytest-3 category/core/monad/tests/
   ```
   This runs additional tests (e.g., disassembly validation). If pytest-3 is not installed, treat it as a failure and tell the user — this is a required part of the pre-PR test gate.

### Error handling

- If tests fail, show which tests failed and their output
- If `build/` doesn't exist, tell the user to run `/build` first

### Important

- Always run commands from the project root directory: $CWD
- Do NOT modify any source files
