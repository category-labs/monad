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
via the `/emacs` skill. Step through tactics one at a time and check
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

When facing a new goal, try the automation cascade through PG before writing
manual tactics. Step each one and check if it closes the goal:

    reflexivity → auto → trivial → ring → lia → lra → nia → nra →
    tauto → firstorder → intuition → eauto → decide

Only write structural tactics (destruct, induction, rewrite, replace) after
the cascade fails on the current goal.

# MCP Limitation

The Rocq MCP tools (`rocq_start_proof`, `rocq_check`, `rocq_step_multi`) do
not work reliably with this codebase due to its module functor structure:

```coq
Module MakeProofs (Import U64 : Uint64).
Include RuntimeMul.Make(U64).
Module WL := WordsLemmas.MakeProofs(U64).
```

Do not waste time retrying MCP proof sessions. Use Proof General via Emacs
for all interactive proof development. MCP `rocq_query` may still work for
standalone `Search`/`Check`/`Print` commands that don't require the module
context.
