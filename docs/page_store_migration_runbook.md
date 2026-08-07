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
  **deactivates** the now-stale slot timeline, leaving a single page-encoded
  database.

State-machine kinds, as named on the CLI:

| Kind on CLI | Encoding | Role during migration |
|-------------|----------|-----------------------|
| `ethereum`  | slot     | the pre-migration primary |
| `monad`     | page     | the secondary you activate, then promote to primary |

### The fork is the hinge

The page-store fork is a scheduled protocol upgrade defined by the chain config —
a single timestamp, identical across the whole cluster. It is not set by the
operator: it ships in a later release, once every node has migrated to
dual-timeline and verification (§4) passes. Canonical state selection is driven
entirely by whether a block is before or after it:

- **Before the fork** — the slot primary owns the canonical `state_root` stamped
  into the block header; the page secondary shadows it.
- **At/after the fork** — the page secondary owns the canonical `state_root`; the
  slot primary shadows it.

Which database is "on disk primary" (the thing `--promote-secondary` changes) is
**independent of which timeline is canonical**: pre-fork the slot is canonical no
matter which ring is on-disk primary, post-fork the page is. That independence is
what lets promote be staggered across a cluster (§3.2).

---

## 2. The one invariant you must not violate

**Every node must activate AND populate its page secondary before the chain
crosses the fork.**

A node still slot-only when the chain crosses the fork cannot follow the
now-canonical page timeline: it fail-stops — the process crashes cleanly, with no
data corruption. Recovery is then forward only: the node must activate its
secondary and rejoin via statesync. **Promote and deactivate, by contrast, may
happen any time after the fork and may be staggered freely.**

Because the fork point ships in a separate release (§1, §3.2), this is not a race
against a fixed deadline: migrate and verify the whole fleet first, and only then
does the fork-setting release go out. The constraint is ordering — that release
must not ship while any node is still slot-only.

---

## 3. Procedure

Every node needs the page-store-enabled `monad-mpt` and `monad-cli` staged first —
the `--state-machine monad` kind and the snapshot `--secondary` flag do not exist
on an older slot-only build.

The per-node command sequence (§3.1) is the same whether you migrate a single
node or roll it across a cluster (§3.2). For a cluster you run §3.1's two offline
groups — activate/populate first, then promote/deactivate — one node at a time,
with the fork crossing in between.

### 3.1 Per-node sequence

Let `$TRIEDB` be the stopped node's storage path.

**Step 1 — Stop the node.**

```bash
systemctl stop monad-execution monad-rpc monad-bft
```

**Step 2 — Activate the page secondary (stamps an empty page timeline).**

```bash
monad-mpt --activate-secondary --state-machine monad --storage "$TRIEDB"
```
- Success line: `Activated secondary timeline; stamped state-machine kind.`
- This must run **before** the snapshot load: the load needs the secondary's
  state-machine kind already stamped on disk.

**Step 3 — Dump a binary snapshot of the primary at the latest finalized version.**

```bash
monad-cli --version latest_finalized --dump-binary-snapshot /path/to/snapshot --db "$TRIEDB"
```
- Success line: `snapshot dump success=true`
- `latest_finalized` resolves to the database's own latest finalized version, so
  there is no block number to look up. (Passing an explicit, unfinalized version
  instead would fail the dump with `Could not query block header`.)

**Step 4 — Load the snapshot into the page secondary (re-encodes slot → page).**

```bash
monad-cli --version latest_finalized --load-binary-snapshot /path/to/snapshot --secondary --db "$TRIEDB"
```
- Success line: `load_to_secondary=true`
- The node is stopped, so this resolves to the same version the dump used. It
  re-encodes all state at that version from slot form into page form; the empty
  secondary now holds the full state.

**Step 5 — Restart the node → dual-write mode.**

```bash
systemctl start monad-execution monad-rpc monad-bft
```
The node now commits every block to both the slot primary and the page secondary
(running both timelines carries a throughput cost — §6). Wait for it to rejoin and
catch up, then confirm it is healthy on the usual node health metrics.

**Step 6 — Cross the fork.** The fork point arrives in a separate release (§3.2
Phase B), applied as a normal rolling upgrade. No action in this sequence: when its
timestamp is reached the canonical state root flips to the page secondary, and the
page timeline becomes the source of truth.

> Steps 7–10 are not time-sensitive. After the fork the node keeps dual-writing
> with the page timeline canonical, so the promote can be scheduled whenever
> convenient — it need not follow the fork immediately. The only counter-pressure
> is the dual-write window's cost and its history ceiling (§6), so don't defer it
> indefinitely.

**Step 7 — Stop the node** (now post-fork).

**Step 8 — Promote the page secondary to on-disk primary.**

```bash
monad-mpt --promote-secondary --storage "$TRIEDB"
```
- Success line: `Promoted secondary timeline to primary (primary_ring_idx flipped).`

**Step 9 — Deactivate the demoted slot timeline (drops it, reclaims its space).**

```bash
monad-mpt --deactivate-secondary --storage "$TRIEDB"
```
- Success line: `Deactivated secondary timeline.`

**Step 10 — Restart the node → single-database, page-encoded, post-fork.**
Confirm it returns to healthy on the usual node health metrics.

### 3.2 Cluster rolling migration

Drive §3.1 across the cluster in phases, one node offline at a time, keeping
quorum throughout.

- **Phase A — Rolling activate + populate (Steps 1–5), node by node.**
  For each node: stop → activate → snapshot dump → snapshot load → restart →
  wait for it to rejoin and the cluster's latest block to advance, *then* move to
  the next node. Per-node offline time is dominated by the snapshot dump/load
  (≈ 8m at mainnet scale — §6). **This must finish on every node before the
  fork-setting release ships** (§2).

- **Phase B — Verify, then ship the fork.** Once Phase A is complete fleet-wide
  and §4 passes on every node, a later release sets the fork point. Operators apply
  it as a normal rolling upgrade (no DB tooling); the chain then crosses the fork
  automatically at the encoded timestamp, flipping every node to page together. No
  node *decides* to cross — the fork point is encoded in the release.

- **Phase C — Rolling promote + deactivate (Steps 7–10), node by node.** Safe to
  **stagger freely** post-fork — promote one node, then the next some time later,
  and so on. For each node: stop → promote → deactivate → restart → wait to
  rejoin. Quorum is preserved because only one node is down at a time and
  canonical selection does not depend on the ring flip.

- **Phase D — Done.** All nodes are single-database page-encoded post-fork. Run
  the post-promote sanity checks in §4.

**Service-interruption budget.** Each node goes offline twice (once in A, once in
C); the dominant cost is the snapshot dump+load in Phase A. If the dump+load keeps
a node down long enough to fall far behind the chain, it may catch up via
statesync on restart, extending its down window further (§6).

### 3.3 Adding a new node or hard-resetting a failed node

§3.1–3.2 migrate an existing database *in place*. A brand-new node, or a failed
node you hard-reset, has no database to migrate — it is rebuilt from a snapshot.
The shape matches normal recovery — reset the DB, restore the latest official
snapshot, start the node, let it statesync/blocksync to the tip — but the
migration changes *which timeline(s)* the rebuilt database carries and how you
stamp it, and that depends on whether the chain has crossed the fork.

> **Restore version.** When loading into a freshly created (empty) database, pass
> the snapshot's own block number as `--version`.

**Before the fork — create both timelines and restore both from the snapshot.**
The node must reach the fork with both timelines populated (§2). Set up both
timelines from the snapshot before the first start; a node started with both
timelines present **statesyncs both to the tip together**:

1. Create the slot primary, then activate the page secondary:

   ```bash
   monad-mpt --create-empty --storage "$TRIEDB"                              # slot primary (default --state-machine ethereum)
   monad-mpt --activate-secondary --state-machine monad --storage "$TRIEDB"  # page secondary
   ```

2. Restore the official snapshot into both timelines (the `--secondary` load
   re-encodes slot → page):

   ```bash
   monad-cli --version <snapshot_block> --load-binary-snapshot /snap --db "$TRIEDB"
   monad-cli --version <snapshot_block> --load-binary-snapshot /snap --secondary --db "$TRIEDB"
   ```

3. Start the node once; it catches up both timelines, then dual-writes.

It is now an ordinary dual-write node: it crosses the fork with the cluster and is
promoted later in Phase C. Both timelines must be created and restored before the
node reaches the fork (§2); budget for the snapshot loads (§6). A node that reaches
the fork without its page timeline fail-stops cleanly (§5).

**After the fork — build a page-only node directly.** Past the fork the slot
timeline is no longer needed — page is canonical — so a rebuilt node needs only
the page primary and never dual-writes. Skip the secondary entirely:

1. Create the DB with the page primary stamped (add your standard storage-sizing
   flags — `--chunk-capacity`, etc.; the migration-specific part is only
   `--state-machine monad`):

   ```bash
   monad-mpt --create-empty --state-machine monad --storage "$TRIEDB"
   ```

2. Restore a snapshot into the primary:

   ```bash
   monad-cli --version <snapshot_block> --load-binary-snapshot /snap --db "$TRIEDB"
   ```

   The snapshot is logical state (accounts/storage/code); the load re-encodes it
   into page form because the primary is stamped `monad`. **The snapshot may
   predate the fork** — an existing slot-era official snapshot loads into a page
   primary just fine, so you need not wait for a post-fork snapshot to add nodes.

3. Start the node; it statesyncs/blocksyncs to the tip as a page-only node.

This same path also recovers a node that fail-stopped at the fork: hard-reset it
and rebuild it as a page-only node.

---

## 4. Verification

The dual-write window exists to prove the page timeline correct **before** the
fork makes it canonical. Run the load-bearing check before the fork: once past
the fork the page state root *is* the consensus `state_root`, so divergence
between nodes halts the chain with no rollback (§5). The check below must pass
fleet-wide before the fork-setting release ships (§3.2 Phase B).

**Before the fork — cross-check the page state root across the cluster.**

While dual-writing, each node logs both timelines' roots every block:

```
block=<n>, block_id=<id> state_root primary=<slot root> secondary=<page root>
```

Grep this line for the same block number on every node and confirm the
`secondary=` (page) root is identical fleet-wide. That page root becomes the
canonical `state_root` at the fork, so cluster-wide agreement is the gate: a
mismatch would halt the chain the moment it crosses, and a non-deterministic or
buggy encoding surfaces here while it is still recoverable. The same line also
confirms, per node, that the secondary is tracking the primary block-for-block
(the two roots differ by encoding, but both must advance together).

The fork-setting release must not ship until the page root agrees on every node.

**After promote — sanity:**

- Block production continues without stalls and in-flight transactions confirm.
- Historical queries at pre-fork heights still resolve through the promoted page
  primary.
- The canonical `state_root` is continuous across the promote.

---

## 5. Failure handling, rollback, and guard rails

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

### Rebuild a secondary before the fork
Before the fork the page timeline is a shadow — dual-written every block but not
yet canonical — so a secondary found to be wrong (the cross-cluster root check (§4)
fails, or an encoding fix ships) can be dropped and rebuilt with no effect on the
canonical slot timeline or the chain. On each affected node: deactivate it (as in
*Abort*, above), apply the fix as a normal rolling upgrade, then redo Steps 2–5 to
re-populate, and re-run the §4 check before the fork-setting release ships.

### A node missed activation before the fork
It fail-stops cleanly (no corruption). A slot-only node cannot continue past the
fork, so recover it forward: either activate its secondary, populate it (§3.1
Steps 2–4), promote, and rejoin; or simpler, hard-reset it and rebuild it directly
as a page-only node (§3.3, after-fork path).

### Never promote before the fork
`--promote-secondary` does not check fork state — it succeeds whenever a secondary
is active. But promoting before the chain crosses the fork makes the page the
on-disk primary while blocks are still committed with the slot encoding, and the
node fail-stops on its next commit. Always wait until the chain is past the fork
(Step 6) before promoting.

### Operations the tools reject (guard rails — expect these to fail loudly)

The DB tools print to stderr and return non-zero for each of these:

| Attempted operation | Message |
|---|---|
| `--activate-secondary` when a secondary is already active | `Secondary timeline already active; nothing to do.` |
| `--deactivate-secondary` when no secondary is active | `Secondary timeline is not active; nothing to do.` |
| `--promote-secondary` when no secondary is active | `Secondary timeline is not active; cannot promote.` |
| Any DB tool run against a **running** node | the storage pool is held exclusively, so the open fails |

---

## 6. Cautions at production scale

These behaviors only appear at mainnet scale, load, or duration. Validate them on
a large-scale test network before a production rollout — small clusters cannot
produce representative numbers:

- **Snapshot dump/load duration.** Minutes on a real validator database, growing
  with state size — on a mainnet snapshot at block 78,929,901, dump took ~5m6s and
  load ~3m15s (≈ 8m of offline work per node). This sets each node's Phase-A
  offline window — and so the overall migration duration and the
  statesync-on-rejoin risk (below).
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

## 7. Quick reference

```bash
# --- Phase A: per node, BEFORE the fork (node stopped) ---
monad-mpt --activate-secondary --state-machine monad --storage "$TRIEDB"                       # -> "Activated secondary timeline; ..."
monad-cli --version latest_finalized --dump-binary-snapshot /snap --db "$TRIEDB"               # -> "snapshot dump success=true"
monad-cli --version latest_finalized --load-binary-snapshot /snap --secondary --db "$TRIEDB"   # -> "load_to_secondary=true"
# restart -> dual-write

# --- fork point ships in a separate release; chain crosses automatically: canonical flips slot -> page ---

# --- Phase C: per node, AFTER the fork (node stopped), stagger freely ---
monad-mpt --promote-secondary    --storage "$TRIEDB"   # -> "Promoted secondary timeline to primary (primary_ring_idx flipped)."
monad-mpt --deactivate-secondary --storage "$TRIEDB"   # -> "Deactivated secondary timeline."
# restart -> single-database page-encoded
```

Adding / hard-resetting a node (§3.3; pass the snapshot's block number as
`--version`):

```bash
# --- BEFORE the fork: create BOTH timelines, restore BOTH, start once (statesyncs both) ---
monad-mpt --create-empty --storage "$TRIEDB"                                                  # slot primary
monad-mpt --activate-secondary --state-machine monad --storage "$TRIEDB"                      # page secondary
monad-cli --version <snapshot_block> --load-binary-snapshot /snap --db "$TRIEDB"
monad-cli --version <snapshot_block> --load-binary-snapshot /snap --secondary --db "$TRIEDB"
# restart -> dual-write; statesyncs both timelines to tip

# --- AFTER the fork: build a page-only node directly (pre-fork snapshot is fine) ---
monad-mpt --create-empty --state-machine monad --storage "$TRIEDB"
monad-cli --version <snapshot_block> --load-binary-snapshot /snap --db "$TRIEDB"
# restart -> single-database page-encoded; statesync/blocksync to tip
```
