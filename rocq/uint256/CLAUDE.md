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

When developing Rocq proofs, use Proof General in Emacs interactively
via Emacs. Step through tactics one at a time and check
goals after each step. Do not write large blocks of untested tactics —
this wastes time fixing cascading errors.  Do not delegate tasks to
subagents unless explicitly told to do so.  Do not use worktrees unless
explicitly told to do so.

When working in a live Proof General session, preserve the existing
locked region whenever possible. Treat the live Emacs buffer state as
authoritative: do not call `revert-buffer` during normal proof repair,
and do not call `proof-retract-buffer` unless you intentionally want a
larger reset.

For local proof edits, navigate relative to the current proof position
instead of jumping back to the top of the file. Retract only locally:
move to around 10 lines before the anticipated edit point, then use
`proof-goto-point` and resume stepping forward. When moving back by one
command, move point to the preceding command and use `proof-goto-point`
to get a local retraction rather than restarting the Coq process.

When a `.v` file is under active Proof General control, do not edit it
externally on disk. In particular, do not use `apply_patch` or other
non-Emacs file-rewrite tools on that file while the PG session is live.
Make the edit in the live Emacs buffer, save it there, then use local
`proof-goto-point` retraction to replay the affected region. This is an
explicit exception to the general preference for patch-based edits.

When facing a new goal, try the automation cascade through PG before writing
manual tactics. Step each one and check if it closes the goal:

    reflexivity → auto → trivial → ring → lia → lra → nia → nra →
    tauto → firstorder → intuition → eauto → decide

Only write structural tactics (destruct, induction, rewrite, replace) after
the cascade fails on the current goal.

# Arithmetic Proof Workflow

For proof files such as `ArithmeticProofs.v`, `RuntimeMulProofs.v`,
`DivisionProofs.v`, and other parameterized developments under `theories/`,
use a live Proof General session as the primary workflow.

- Open the target `.v` file in Emacs and step to the theorem of interest.
- Edit in the live buffer, save there, and retract locally with
  `proof-goto-point`.
- Prefer small tactic steps with goal inspection after each step.
- Use `Search`, `Check`, and `Print` from the Rocq toplevel / Proof General
  when you need local context-aware exploration.
- Validate each edited file with `opam exec -- dune build theories/Foo.vo`.
- If a proof attempt gets blocked, do **not** just drop back to `Admitted`
  and move on. First leave the in-progress script in the file as a commented
  block immediately above the theorem, with a short note about where it
  stalled. Then restore a buildable state with `Admitted` and only then move
  on to the next lemma. This rule is mandatory for future proof work in this
  project.

If you need a concrete sanity-check file for computation or reduction, keep it
separate from the generic proof file.  Do not rewrite the generic development
around tool limitations unless explicitly asked.

# Rocq MCP Status

The Rocq MCP launcher can be configured to start correctly in this project, but
the remaining blocker is theorem reopening, not process startup.

Current findings:

- `rocq_start` / `rocq_check` work on some simple top-level theorems.
- The theorem-reopen path does **not** work reliably for parameterized
  developments in this repo.
- The failure reproduces with:
  - module functors over `Uint64`
  - `Section` variables
  - first-class records such as `UintR`
- The failing pattern is theorem statements that depend on:
  - functor parameters or section parameters
  - record interfaces such as `UintR`
  - projections such as `width`
  - local definitions built from those parameters/projections
- Position-based `rocq_start(file, line, character)` has not been a reliable
  workaround in these files; it often returns `proof_finished = true` with no
  usable local proof state.

Representative repro files in this repo:

- `theories/McpFunctorRepro.v`
- `theories/McpRecordRepro.v`
- `rocq-mcp-functor-repro.md`
- `rocq-mcp-record-repro.md`

Practical guidance:

- Do not spend time retrying MCP interactive proof sessions in
  `ArithmeticProofs.v`, `RuntimeMulProofs.v`, `UintRecordsMetatheorems.v`, or
  similar parameterized files.
- Use Proof General via Emacs for all real interactive proof development.
- MCP is still acceptable for:
  - `rocq_toc`
  - `rocq_compile_file`
  - small standalone `rocq_query` calls with an explicit preamble
  - tiny non-parameterized toy files used only for reproducing tool bugs
