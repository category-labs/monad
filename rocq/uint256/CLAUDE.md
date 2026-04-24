# Build System

This project uses a **local opam switch** (`_opam/` in this directory).
Do not search for the switch or change directories to find it.

- **Build a file:** `opam exec -- dune build theories/Foo.vo`
- **Build everything:** `opam exec -- dune build`
- **Rocq compiler:** `opam exec -- rocq` (not `coqc`)
- **Toolchain:** Rocq 9.1.1, OCaml 5.4.1, Dune 3.22.0

Do not use `cd`, `find`, or `which` to locate build tools.
Always prefix with `opam exec --` from the project root.

# Interactive Proof Development

Follow the `rocq-skills` workflow and use `rocq-mcp` to prove theorems interactively.
