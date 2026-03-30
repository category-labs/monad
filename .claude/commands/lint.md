Run clang-tidy and trait instantiation checks on the monad C++ project.

## Arguments

The user may pass arguments like:
- `--fix` — apply clang-tidy fixes in-place (requires clean git state)
- No arguments — check only, report issues without modifying files

## Instructions

You are running lint checks for the monad C++ project located at $CWD.

### Build requirements

Linting requires a specific build configuration to match CI. All of these must be true, otherwise tell the user and offer to reconfigure:
- Clang 19 compiler
- Debug build type
- `MONAD_COMPILER_TESTING=ON` and `MONAD_COMPILER_BENCHMARKS=ON`
- `UTILS_CLANG_TIDY_AUTO_CONST=ON`
- `third_party/evmone` must be present (see `/build` for evmone setup instructions)

### Steps

1. **Check build configuration.** Verify `build/compile_commands.json` exists and was generated with the right settings. If the build doesn't exist or doesn't match, configure it:
   ```bash
   CC=clang-19 CXX=clang++-19 cmake -G Ninja -B build \
     -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
     -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
     -DCMAKE_BUILD_TYPE=Debug \
     -DMONAD_COMPILER_TESTING=ON \
     -DMONAD_COMPILER_BENCHMARKS=ON \
     -DUTILS_CLANG_TIDY_AUTO_CONST=ON
   ```

2. **Build the const-correctness plugin:**
   ```bash
   cmake --build build --target ConstCorrectnessChecks
   ```
   This produces `build/utils/clang-tidy-auto-const/libConstCorrectnessChecks.so`, which `check-clang-tidy.sh` automatically loads if present. Without this plugin, the custom `misc-auto-const-correctness` check won't run and lint results will differ from CI.

3. **Run clang-tidy:**
   - **Check only** (no `--fix`): `scripts/check-clang-tidy.sh -p build`
   - **Fix mode** (`--fix`): `scripts/apply-clang-tidy-fixes.sh build` — this requires a clean git working tree (no uncommitted changes) and will error otherwise.

4. **Run trait instantiation check:**
   ```bash
   python3 scripts/check-trait-instantiations.py
   ```
   Checks that explicit template instantiation macros (`EXPLICIT_EVM_TRAITS*`, `EXPLICIT_MONAD_TRAITS*`, `EXPLICIT_TRAITS*`) don't overlap across translation units and are only used in `.cpp` files (not headers). No build required for this check. It has no auto-fix — report issues for manual resolution.

The project's `.clang-tidy` config treats all warnings as errors and covers bugprone, clang-analyzer, modernize, performance, and readability checks.

### Error handling

- If `build/` doesn't exist or was configured with the wrong compiler/build type, reconfigure as shown above
- If `third_party/evmone` is missing, tell the user to set it up (see `/build` for instructions)
- If `--fix` is used with uncommitted changes, the fix script will error — tell the user to commit or stash first

### Important

- Always run commands from the project root directory: $CWD
- Do NOT modify source files unless the user explicitly requested `--fix`
