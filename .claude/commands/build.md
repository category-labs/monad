Configure and build the monad C++ project.

## Arguments

The user may pass arguments like:
- `configure` — only run cmake configure step
- `build` — only run the build step (configure first if build/ doesn't exist)
- `clean` — remove the build directory and reconfigure from scratch
- `<target>` — build a specific cmake target (e.g., `monad`, `monad-cli`, a test name)
- Compiler selection: `--clang` to use Clang 19+ instead of GCC 15+ (default)
- CMake options as flags: `--llvm`, `--debug`, `--release`, `--asan`, `--tsan`, `--ubsan`, `--coverage`, `--avx512`

If no arguments are given, run the full cycle: configure (if needed) + build.

## Instructions

You are helping the user configure and build the monad C++ project located at $CWD.

### Build system details

- Generator: Ninja
- Build directory: `build/` (relative to project root)
- Default build type: `RelWithDebInfo`
- Compiler requirements: GCC 15+ or Clang 19+
- CPU architecture: `-march=haswell` minimum (x86-64-v3)
- Toolchain files: `category/core/toolchains/` — these set architecture and sanitizer flags

### Available toolchain files

| Toolchain | Use case |
|-----------|----------|
| `category/core/toolchains/gcc-avx2.cmake` | **Default** — `-march=haswell` (AVX2). Works with both GCC and Clang. |
| `category/core/toolchains/gcc-avx512.cmake` | `-march=skylake-avx512`. Works with both GCC and Clang. |
| `category/core/toolchains/gcc-asan.cmake` | ASAN + UBSAN (includes `-march=haswell`). **GCC only — do not use with Clang** (use `clang-fuzz.cmake` instead). |
| `category/core/toolchains/gcc-tsan.cmake` | TSAN (includes `-march=haswell`). **GCC only.** |
| `category/core/toolchains/clang-tsan.cmake` | TSAN (includes `-march=haswell`). **Clang only.** Note: currently hard-codes a `-fsanitize-blacklist` path that may not exist on all machines. |
| `category/core/toolchains/clang-fuzz.cmake` | ASAN + UBSAN + fuzzing coverage instrumentation. **Clang only.** Note: includes fuzzing flags (`-fsanitize-coverage`, `-DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION`), so this is more than plain ASAN. There is no plain Clang ASAN toolchain — warn the user about the extra flags if they just asked for `--asan --clang`. |

### CMake options available

**Build type and linking:**

| Option | Default | Description |
|--------|---------|-------------|
| `CMAKE_BUILD_TYPE` | `RelWithDebInfo` | Build type (Debug, Release, RelWithDebInfo, MinSizeRel) |
| `BUILD_SHARED_LIBS` | OFF | Build with shared libraries (also enables `-fPIC`) |

**JIT compiler options** (defined in root `CMakeLists.txt`):

| Option | Default | Description |
|--------|---------|-------------|
| `MONAD_COMPILER_LLVM` | OFF | Build LLVM JIT backend (requires LLVM 19.1.7 installed) |
| `MONAD_COMPILER_COVERAGE` | OFF | Build with coverage instrumentation |
| `MONAD_COMPILER_TESTING` | OFF | Build compiler tests (requires `third_party/evmone` — see evmone note below) |
| `MONAD_COMPILER_BENCHMARKS` | OFF | Build compiler benchmarks (requires `third_party/evmone` — see evmone note below) |
| `MONAD_COMPILER_DUMP_ASM` | OFF | Dump assembly files into `build/asm` |
| `MONAD_COMPILER_STATS` | OFF | Print JIT compiler statistics |
| `MONAD_COMPILER_HOT_PATH_STATS` | OFF | Print VM hot-path statistics |

**Core options** (defined in `category/core/CMakeLists.txt`):

| Option | Default | Description |
|--------|---------|-------------|
| `MONAD_CORE_FORCE_DEBUG_ASSERT` | OFF | Enable `MONAD_DEBUG_ASSERT` in any build mode (normally Debug-only) |

**VM interpreter options** (defined in `category/vm/interpreter/CMakeLists.txt`):

| Option | Default | Description |
|--------|---------|-------------|
| `MONAD_VM_INTERPRETER_DEBUG` | OFF | Trace every instruction executed by the interpreter |
| `MONAD_VM_INTERPRETER_STATS` | OFF | Print opcode statistics as CSV on exit (not thread-safe, benchmarking only) |

**Event subsystem options** (defined in `category/event/CMakeLists.txt`):

| Option | Default | Description |
|--------|---------|-------------|
| `MONAD_EVENT_USE_LIBHUGETLBFS` | ON (Linux) | Build with libhugetlbfs support for huge-page-backed event rings |
| `MONAD_EVENT_BUILD_EXAMPLE` | ON | Build the event API example program |

**Environment variables:**

| Variable | Description |
|----------|-------------|
| `GIT_COMMIT_HASH` | Override the commit hash baked into `monad` and `monad-cli` binaries (defaults to `git rev-parse HEAD`) |

### Step-by-step behavior

1. **Parse the user's arguments** (provided as $ARGUMENTS) and determine which steps to run and which options to set.

2. **Ensure submodules are initialized**:
   - Check if `third_party/asmjit/CMakeLists.txt` exists (a quick proxy for submodule state)
   - If not, run `git submodule update --init --recursive` before configuring
   - This is especially important in fresh clones and git worktrees

3. **Check system dependencies** (only when running the configure step):
   - Run the following checks and collect all missing items before reporting:
     ```bash
     # Tools (check via which)
     which cmake ninja pkg-config
     # Compiler (check whichever was selected)
     which gcc-15 g++-15    # GCC (default)
     which clang-19 clang++-19  # Clang (if --clang)
     # Key dev libraries (check via pkg-config — TBB uses find_package, not pkg-config)
     pkg-config --exists liburing libzstd libcrypto++ gmp
     # TBB: cmake's find_package(TBB) looks for TBBConfig.cmake; check via dpkg
     dpkg -s libtbb-dev 2>/dev/null | grep -q "Status: install ok installed"
     # Additional dev packages (check via dpkg)
     dpkg -s libgtest-dev libgmock-dev libboost1.83-dev libhugetlbfs-dev libcli11-dev libbenchmark-dev libarchive-dev libbrotli-dev libcap-dev 2>/dev/null | grep -c "Status: install ok installed"
     ```
   - If anything is missing, list all missing items and suggest the apt install command. Reference `scripts/ubuntu-build/` for the full Docker install scripts.
   - Do not proceed to configure until dependencies are resolved.

4. **Configure step** (`cmake -G Ninja -B build ...`):
   - **Compiler selection**: The system default compiler may be too old. Explicitly set the compiler:
     - GCC (default): `CC=gcc-15 CXX=g++-15`
     - Clang (`--clang` flag): `CC=clang-19 CXX=clang++-19`
   - Ensure the required architecture flags are set (`-march=haswell` minimum) so that C/C++ and assembly sources (e.g., `keccak_impl.S`) compile correctly. The recommended way is to pass `-DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/<toolchain>.cmake`. Alternatively, `CFLAGS`, `CXXFLAGS`, and `ASMFLAGS` environment variables can provide the same flags.
   - Always pass `-G Ninja`
   - Always pass `-DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE`
   - Set `CMAKE_BUILD_TYPE` based on flags: `--debug` -> Debug, `--release` -> Release, default -> RelWithDebInfo
   - Select toolchain based on compiler and sanitizer flags:
     - **GCC (default)**:
       - Default (no sanitizer flags): `gcc-avx2.cmake`
       - `--avx512`: `gcc-avx512.cmake`
       - `--asan`: `gcc-asan.cmake` (includes ASAN + UBSAN + `-march=haswell`). **Warning:** GCC ASAN breaks the must-tail calling convention used by the VM interpreter. CI excludes the GCC+ASAN combination for VM tests. If the user is working on VM code, recommend `--asan --clang` instead.
       - `--tsan`: `gcc-tsan.cmake` (includes TSAN + `-march=haswell`)
       - `--ubsan`: `gcc-asan.cmake` (UBSAN is bundled with ASAN in this toolchain)
     - **Clang (`--clang`)**:
       - Default (no sanitizer flags): `gcc-avx2.cmake` (arch-only flags are compiler-agnostic)
       - `--avx512`: `gcc-avx512.cmake` (arch-only flags are compiler-agnostic)
       - `--tsan`: `clang-tsan.cmake`
       - `--asan` / `--ubsan`: `clang-fuzz.cmake`. **Warn the user** that this toolchain also includes fuzzing instrumentation flags (sanitize-coverage, `-DFUZZING_BUILD_MODE_UNSAFE_FOR_PRODUCTION`). There is no plain Clang ASAN toolchain. If they only want ASAN without fuzzing flags, they would need to create a custom toolchain file.
   - Map `--llvm` to `-DMONAD_COMPILER_LLVM=ON`
   - Map `--coverage` to `-DMONAD_COMPILER_COVERAGE=ON`
   - Skip if `build/` already exists and user didn't request `configure` or `clean` explicitly, **unless** the user passed configuration-affecting flags (`--clang`, `--asan`, `--tsan`, `--ubsan`, `--avx512`, `--debug`, `--release`, `--llvm`, `--coverage`). These flags change the toolchain, compiler, or build type — silently reusing a stale `build/` will produce a broken or mismatched build. In that case, reconfigure (wipe `build/CMakeCache.txt` first if the compiler changed, since CMake does not allow switching compilers in-place).

5. **Build step** (`cmake --build build --parallel`):
   - Default target: `all`
   - If user specified a specific target, pass `--target <target>`
   - If build fails, read the error output carefully and diagnose the issue

6. **Clean step**:
   - Remove the `build/` directory
   - Then run configure and build (i.e., proceed to steps 3–5)

### evmone (custom fork — not a submodule)

`third_party/evmone/` is gitignored and must be cloned manually from the Category Labs fork. It is required for `MONAD_COMPILER_TESTING=ON`, `MONAD_COMPILER_BENCHMARKS=ON`, `/lint`, and `/fuzz`. Not needed for standard builds.

**To set up** (run from the project root):
```bash
git clone git@github.com:category-labs/evmone.git third_party/evmone
git -C third_party/evmone checkout v0.18.0-category
```
**Do not `cd` into the evmone directory** — subsequent cmake commands use relative paths that break if the working directory has changed.

The branch `v0.18.0-category` is the current stable fork used in CI. Check `.github/workflows/test-vm.yml` for the latest ref if in doubt. This requires SSH access to the `category-labs` GitHub organization.

### Example configure commands

Default GCC build:
```bash
CC=gcc-15 CXX=g++-15 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo
```

Clang build:
```bash
CC=clang-19 CXX=clang++-19 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-avx2.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo
```

GCC ASAN build (not recommended for VM code — see step 3 warning):
```bash
CC=gcc-15 CXX=g++-15 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/gcc-asan.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=Debug
```

Clang ASAN build (includes fuzzing instrumentation — no plain Clang ASAN toolchain exists):
```bash
CC=clang-19 CXX=clang++-19 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/clang-fuzz.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=Debug
```

Clang TSAN build:
```bash
CC=clang-19 CXX=clang++-19 cmake -G Ninja -B build \
  -DCMAKE_TOOLCHAIN_FILE=category/core/toolchains/clang-tsan.cmake \
  -DCMAKE_EXPORT_COMPILE_COMMANDS:BOOL=TRUE \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo
```

### Error handling

- If cmake configure fails, check for missing dependencies and suggest install commands
- If configure fails with "GCC version 15 or higher is required", ensure `CC=gcc-15 CXX=g++-15` is set (or use `CC=clang-19 CXX=clang++-19` for Clang)
- If configure fails with missing `CMakeLists.txt` in `third_party/`, run `git submodule update --init --recursive`
- If build fails with `#error avx2 or avx512 required`, ensure a toolchain file is being used
- If configure fails with "third_party/evmone to be present", the custom evmone fork needs to be cloned — see the evmone section above
- If the evmone clone fails with a permission error, the user needs SSH access to the `category-labs` GitHub organization
- If build fails, show the relevant error lines and suggest fixes

### Important

- Always run commands from the project root directory: $CWD
- Show the user what commands you're running before executing them
- After a successful build, briefly note the key artifacts produced (e.g., `build/cmd/monad`, `build/cmd/monad-cli`)
- Do NOT modify any source files — this skill is only for building
