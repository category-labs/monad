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

# Semantic Blockers

The only semantic blockers that matter for this development are discrepancies
where the C++ implementation itself disagrees with the intended mathematical
operation.  When such a blocker is claimed, first encode a concrete Rocq
counterexample against the executable/model definitions.  Prefer adding such
checks to `theories/BarrettExecutableChecks.v`.

Only document the issue as a semantic discrepancy after the concrete Rocq
counterexample demonstrates the mismatch.  If the check does not reproduce the
issue, downgrade the note to a candidate or failed counterexample and do not
treat it as blocking proof work.

If the mismatch is between the Rocq model and the C++ implementation, do not
treat it as a semantic blocker.  Update the Rocq model to match the C++
control flow and behavior, then continue the proof work.
