Run clang-format on all monad C++ source files.

## Instructions

You are formatting source files for the monad C++ project located at $CWD.

### Steps

1. **Run clang-format:**
   ```bash
   scripts/apply-clang-format.sh
   ```
   This runs `clang-format-19` in-place on all `.hpp`, `.cpp`, `.c`, `.h` files under `category/`, `cmd/`, `test/`.

2. **Check results:**
   Run `git diff --stat` to show which files were modified. If no files changed, formatting was already clean.

No build is required — this works standalone.

### Important

- Always run commands from the project root directory: $CWD
