# Slot → Page Storage Migration — Operator Runbook

Operational procedure for migrating a Monad node's on-disk MPT database from the
**slot-encoded** layout to the **page-encoded** (page-store) layout, online,
without resyncing from genesis.

> **Audience:** node operators / devops running validators and full nodes.
> Assumes familiarity with starting/stopping a node and locating its triedb.

---

## 1. What this migration is

The page-store change replaces the per-storage-slot trie encoding with a
page-packed encoding (a bitmap plus packed values, bucketed by page key). Rather
than rewrite the live database in place, migration runs a **dual-timeline**
window:

- The node keeps its existing **slot** database as the *primary* timeline.
- It stamps and populates a second **page** database as the *secondary* timeline.
- For a window it **dual-writes** every committed block to both.
- At a scheduled chain fork the **canonical** state root flips from slot to page.
- After the fork the operator **promotes** the page secondary to primary and
  **deactivates** the now-stale slot timeline, leaving a single page database.

State-machine kinds, as named on the CLI:

| Kind on CLI | Encoding | Role during migration |
|-------------|----------|-----------------------|
| `ethereum`  | slot     | the pre-migration primary |
| `monad`     | page     | the secondary you activate, then promote to primary |

### The fork is the hinge

The page-store fork is a scheduled protocol upgrade defined by the chain config —
a single timestamp, identical across the whole cluster. Canonical state
selection is driven entirely by whether a block is before or after it:

- **Before the fork** — the slot primary owns the canonical `state_root` stamped
  into the block header; the page secondary shadows it.
- **At/after the fork** — the page secondary owns the canonical `state_root`; the
  slot primary shadows it.

Which database is "on disk primary" (the thing `--promote-secondary` changes) is
**independent of which timeline is canonical**: pre-fork the slot is canonical no
matter which ring is on-disk primary, post-fork the page is. That independence is
what lets promote be staggered across a cluster (§4.2).

---

## 2. The one invariant you must not violate

**Every node must activate AND populate its page secondary before the chain
crosses the fork.**

A node still slot-only when block timestamps cross the fork aborts on its first
post-fork commit with:

```
read_storage_page is only valid on a page-encoded TrieDb
```

This is fail-stop (it takes the node down cleanly, with no silent corruption),
but recovery is then forward only: the node must activate its secondary and
rejoin via statesync. **Promote and deactivate, by contrast, may happen any time
after the fork and may be staggered freely.**

Plan the rollout so that **activate + populate (Phase A) completes on every node
with comfortable margin before the fork timestamp.** Size that margin against
snapshot dump/load duration on a *real* database (§7), which can be minutes.

---

## 3. Prerequisites

- **Page-store-enabled binaries.** `monad-mpt` and `monad-cli` must be the
  release/image that introduces page storage. The `--state-machine monad` kind,
  the snapshot `--secondary` flag, and dual-database boot do not exist on an
  older slot-only build. Stage the binaries/image on every node first.
- **A scheduled, chain-wide fork.** The page-store fork timestamp must be agreed
  and identical across the cluster before you begin.
- **Node DB path.** Every command targets the *stopped* node's triedb. Below,
  `$TRIEDB` is that storage path — substitute your node's actual path.
- **Quorum headroom (clusters).** You take one node offline at a time; the
  validator set must retain quorum with one node down.
- **The node must be STOPPED** before any `monad-mpt` / `monad-cli` command.
  Running a DB tool against a live node's storage is rejected.

---

## 4. Procedure

The per-node command sequence (§4.1) is the same whether you migrate a single
node or roll it across a cluster (§4.2). For a cluster you run §4.1's two offline
groups — activate/populate first, then promote/deactivate — one node at a time,
with the fork crossing in between.

### 4.1 Per-node sequence

Let `$TRIEDB` be the stopped node's storage path.

**Step 1 — Stop the node.**

**Step 2 — Activate the page secondary (stamps an empty page timeline).**

```bash
monad-mpt --activate-secondary --state-machine monad --storage "$TRIEDB"
```
- Success line: `Activated secondary timeline`
- The command also prints the database's latest finalized version:
  `Latest finalized is <N>`. **Use that `<N>`** for the snapshot below — do not
  estimate it from the chain tip. Under load the gap between the consensus tip
  and the latest *finalized* execution version can be large; an unfinalized
  version makes the dump fail with `Could not query block header`.
- This must run **before** the snapshot load: the load needs the secondary's
  state-machine kind already stamped on disk.

**Step 3 — Dump a binary snapshot of the primary at version `<N>`.**

```bash
monad-cli --version <N> --dump-binary-snapshot /path/to/snapshot --db "$TRIEDB"
```
- Success line: `snapshot dump success=true`

**Step 4 — Load the snapshot into the page secondary (re-encodes slot → page).**

```bash
monad-cli --version <N> --load-binary-snapshot /path/to/snapshot --secondary --db "$TRIEDB"
```
- Success line: `load_to_secondary=true`
- This re-encodes all state at version `<N>` from slot form into page form; the
  empty secondary now holds the full state.

**Step 5 — Restart the node → dual-write mode.**
The node now commits every block to both the slot primary and the page secondary.
Wait for it to rejoin and catch up, and confirm block production resumes.

> Optional safety: boot with `--dual-db-migration-mode` to cross-check every read
> against both timelines during the dual-write window. It costs read latency — use
> it to build confidence on the first nodes rather than fleet-wide.

**Step 6 — Cross the fork.** No operator action: block timestamps reach the
configured fork time and the canonical state root flips to the page secondary.
From here the page timeline is the source of truth.

**Step 7 — Stop the node** (now post-fork).

**Step 8 — Promote the page secondary to on-disk primary.**

```bash
monad-mpt --promote-secondary --storage "$TRIEDB"
```
- Success line: `Promoted secondary timeline to primary`

**Step 9 — Deactivate the demoted slot timeline (drops it, reclaims its space).**

```bash
monad-mpt --deactivate-secondary --storage "$TRIEDB"
```
- Success line: `Deactivated secondary timeline`

**Step 10 — Restart the node → single-database, page-encoded, post-fork.**
Confirm it resumes and commits new blocks without the `read_storage_page` abort.

### 4.2 Cluster rolling migration

Drive §4.1 across the cluster in phases, one node offline at a time, keeping
quorum throughout.

- **Phase A — Rolling activate + populate (Steps 1–5), node by node.**
  For each node: stop → activate → snapshot dump → snapshot load → restart →
  wait for it to rejoin and the cluster's latest block to advance, *then* move to
  the next node. **This phase must finish on every node before the fork time**
  (§2). Keep load flowing; the cluster keeps producing blocks throughout.

- **Phase B — Cross the fork.** Once Phase A is complete fleet-wide, let the
  chain cross the configured fork time. Every node is now dual-writing and flips
  canonical to page together at the fork.

- **Phase C — Rolling promote + deactivate (Steps 7–10), node by node.** Safe to
  **stagger freely** post-fork — promote one node, then the next some time later,
  and so on. For each node: stop → promote → deactivate → restart → wait to
  rejoin. Quorum is preserved because only one node is down at a time and
  canonical selection does not depend on the ring flip.

- **Phase D — Done.** All nodes are single-database page-encoded post-fork. Run
  the verification in §5.

**Service-interruption budget.** Each node goes offline twice (once in A, once in
C); the dominant cost is the snapshot dump+load in Phase A. If the dump+load keeps
a node down long enough to fall far behind the chain, it may catch up via
statesync on restart, extending its down window further (§7).

---

## 5. Verification / success criteria

The migration is correct only if state is byte-identical across the promote.
Check, per node and at the cluster level:

- **Block production never stalls** beyond your interruption budget; transactions
  submitted during the migration confirm (allow a small in-flight tolerance).
- **Account state matches** across the promote — spot-check `eth_getBalance`,
  account nonce, and contract code for known accounts before Phase A and after
  Phase C; they must be identical.
- **Contract storage matches** — `eth_getStorageAt` for representative slots,
  including contracts with dense/multi-page storage, returns identical values
  pre- and post-migration. This exercises the page encoding directly and is where
  a silent encoding bug would surface.
- **State-root continuity** — the canonical `state_root` at the last pre-promote
  block, read back from the promoted page primary, matches what was committed.
- **Historical queries still resolve** — queries at pre-fork block heights still
  answer after the page primary takes over.
- **First post-fork commit succeeds** — the node commits a post-fork block
  without `read_storage_page is only valid on a page-encoded TrieDb`.

---

## 6. Failure handling, rollback, and guard rails

### Interrupted offline command → just re-run it
`--activate-secondary`, `--promote-secondary`, and `--deactivate-secondary` are
crash-safe and idempotent. If a `monad-mpt` command is killed mid-flight, the
next start heals the on-disk metadata, and **re-running the same command is
safe.** A node killed mid-promote reopens cleanly and rejoins. (Durability
assumes power-loss-protected, enterprise-class SSDs.)

### Abort a migration (only before the fork)
Before the fork you can abandon cleanly: stop the node and run
`monad-mpt --deactivate-secondary` to drop the page secondary and revert to
slot-only. **After the fork there is no rollback** — page is canonical and
recovery is forward only.

### A node missed activation before the fork
It fail-stops on `read_storage_page` (no corruption). Recover forward: activate
its secondary and let it rejoin via statesync. Do not attempt to run it slot-only
past the fork.

### Operations the tools reject (guard rails — expect these to fail loudly)

| Attempted operation | Result |
|---|---|
| `--promote-secondary` **before** the fork | Rejected — it would leave a page primary being written with the slot encoding. Cross the fork first. |
| `--deactivate-secondary` without a prior promote | Rejected |
| `--activate-secondary` when a secondary is already active | Rejected |
| `--dual-db-migration-mode` with no secondary present | Rejected |
| Any DB tool against a **running** node | Rejected |

---

## 7. Cautions at production scale

These behaviors only appear at mainnet scale, load, or duration. Validate them on
a large-scale test network before a production rollout — small clusters cannot
produce representative numbers:

- **Snapshot dump/load duration.** Minutes on a real validator database. This
  sets each node's Phase-A offline window and therefore both the fork-time margin
  (§2) and the statesync-on-rejoin risk (below).
- **Statesync on rejoin.** If snapshot dump/load keeps a node offline long enough
  to fall far behind, it may catch up via statesync on restart rather than a fast
  resume, extending the down window further.
- **Queryable-history pressure.** A lagging secondary can pin old data while the
  node trims history under disk pressure. Watch disk headroom during the
  dual-write window.
- **Migration-window ceiling.** The page secondary retains only a bounded amount
  of history (on the order of ~3 months at sub-second block times). The
  dual-write window — activate through promote — must complete well within that
  bound.
- **Dual-write throughput impact.** Running both timelines can reduce TPS during
  the window; account for it when scheduling the migration relative to expected
  load.

---

## 8. Quick reference

```bash
# --- Phase A: per node, BEFORE the fork (node stopped) ---
monad-mpt --activate-secondary --state-machine monad --storage "$TRIEDB"        # -> "Activated secondary timeline" + "Latest finalized is N"
monad-cli --version N --dump-binary-snapshot /snap --db "$TRIEDB"               # -> "snapshot dump success=true"
monad-cli --version N --load-binary-snapshot /snap --secondary --db "$TRIEDB"   # -> "load_to_secondary=true"
# restart -> dual-write

# --- fork crosses: canonical flips slot -> page (no operator action) ---

# --- Phase C: per node, AFTER the fork (node stopped), stagger freely ---
monad-mpt --promote-secondary    --storage "$TRIEDB"   # -> "Promoted secondary timeline to primary"
monad-mpt --deactivate-secondary --storage "$TRIEDB"   # -> "Deactivated secondary timeline"
# restart -> single-database page-encoded
```
