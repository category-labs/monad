# V2 State Caching — Final Spec (Implementation Handoff)

> **Status: final verdict, ready for implementation.** Self-contained; design rationale, alternatives, and attack derivations live in `design-v2.md`. Gas constants per `monad/category/vm/evm/traits.hpp` pricing version 1. Code references are to the current `monad/` checkout.

## 0. Verdict

Ship **implicit deterministic multi-block caching**: every account and storage page carries a consensus **stamp** (last-qualifying-access block number) held on its DbCache entry; the protocol warm set is the most recent stamps that fit a fixed per-cache budget; warm-set hits are charged `1000` instead of the cold cost. Reads are lazily re-stamped (amortized), value-changing writes stamp immediately, the window boundary is computed from committed per-block counts (never from physical cache state), and persistence is a per-block sequential blob — **zero trie writes from reads, zero MPT changes**.

Rejected (rationale in `design-v2.md` §11–§12): explicit cache ops / auctions / contract-granular warmth (public-good free-riding; payment is the wrong selector), probabilistic amortization (grindable PRF + bad UX), stamps as trie leaf versions (write amplification), fixed C = 256 (organic FIFO flip at ~72% block utilization), event counting (write-churn window compression), binding per-block inclusion caps (pay-cold-get-nothing), adaptive K (gas already adapts; adds a consensus feedback surface for no benefit).

## 1. Parameters

| Name | Value | Notes |
| --- | --- | --- |
| `WARM_GAS` | `100` | unchanged (per-tx EIP-2929 / MIP-8 page set) |
| `CACHED_ACCESS_GAS` | `1000` | total first-access price for a warm-set account or storage page; replaces the cold cost, one unified value |
| Cold costs | `8100` storage / `10100` account | unchanged (pricing v1) |
| `ACCOUNT_WINDOW_BUDGET` | `5,000,000` entries (proposal) | count-denominated; physical accounts LRU = 10M entries → 2× margin |
| `STORAGE_WINDOW_BUDGET` | `128 MB` weight (proposal) | byte-denominated, weight = `storage_page_t::byte_size()`. **Physical cache size is node-local config (currently 1 GiB on the branch); the budget is consensus** — freeze it at ≤ half the *minimum* spec'd validator configuration, with negatives and speculative pollution counted in the margin. Validate against replay (§7) before freezing |
| `ALPHA` | `1/2` (implement as shift) | refresh-eligibility fraction of the live window |
| `C_MIN` | `64` blocks | eligibility floor; must stay < α·D(max load) ≈ 92 |
| `K_STAMP_CEILING` | `262,144` stamps/block (2^18) | **non-binding** hard ceiling, above the gas-feasible max (~150k all-refresh); exists only to decouple client I/O provisioning from future gas-limit raises. Never lower it into binding range |

Two independent windows: accounts (count) and storage (bytes), each with its own ring buffer and boundary `E_a` / `E_s`, same rules.

## 2. Consensus rules

All rules evaluate against the **parent block's committed state** (`E`, stamps as of block N−1 — which may be an undecided proposal; use its overlay), so every price is fixed at block start and parallel execution is unaffected.

**Charging (first access to an item in a tx; per-tx warm rules unchanged):**
1. In the tx access set / `read_accessed_pages` → `100`.
2. Else if `stamp(item) ≥ E` (as of parent block) → `1000`, add to tx access set.
3. Else → full cold schedule. (Whether a refresh fires never changes the charge — exactly three tiers.)

**Stamping (side effects, applied at finalize in commit order):**
- **Cold access** (rule 3, item has a live leaf): `stamp := N` (entry enters the warm set).
- **Warm read** (rule 2): re-stamp `stamp := N` **iff** `stamp < N − max(ALPHA·(N − E), C_MIN)`; otherwise nothing.
- **Value-changing write**: `stamp := N` unconditionally. Implementation: the immediate-stamp set is exactly the block's `ProposalPostState` / `StateDeltas` — no filtering needed, since no-op writes (`P0 == P1`) produce no delta under MIP-8.
- **No-op writes are read-class**: their load step reads the page like any read, so they follow the lazy rule (refresh iff stale) with no special-casing. This is safe because any re-stamp path costs at least the `1000` first-access charge (the 100-gas rate only exists after the page's first touch in a tx, and stamps are idempotent per block) — only *unconditional* no-op stamping was ever exploitable, and it is excluded by construction above.
- **Reads of nonexistent items** (no leaf: absent account, empty page) never stamp; they are always cold-priced. Physical negative caching is unaffected.
- Stamps are idempotent within a block. **Revert semantics are atomic and uniform with EIP-2929**: read-stamp candidates are journaled alongside the per-tx access sets, popped on frame revert, and discarded on transaction failure (write-stamps are atomic by construction — the immediate set is the post-state deltas, which exclude reverted writes). Reverted-frame touches may leave items physically cached but protocol-cold; that is the safe overcharge direction. Keys are `(address)` / `(address, incarnation, page_key)` — incarnation death drops warmth.
- Deterministic order for the (non-binding) ceiling: `(txn_index, key sort within txn)` — no access-sequence recording needed.

**Window boundary (per cache, exact counting):**
- Ring buffer `count[b]` = entries (accounts) or bytes (storage) whose **current** stamp is block `b`. On stamp: `count[N] += w; count[prev_stamp] −= w` (`prev_stamp` is in the entry being touched). **These are in-memory array ops on a KB-sized, L1-resident buffer — never persisted, never committed** (derivable from the blob stream; rebuilt on restart). The only durable write per stamp is its ~40 B record in the per-block sequential blob. On delete/incarnation death: decrement. An `SSTORE` growing occupancy of a warm page adds the new words' weight to `count[N]`.
- `E` = smallest block such that `Σ count[b] for b in [E, N]` ≤ budget (all-or-nothing at block granularity), **clamped monotone: `E_N = max(E_{N−1}, computed E)`**. The clamp is consensus-critical: deletions (zeroed slots, incarnation death) shrink window mass, and an E retreat would re-warm entries some nodes already evicted (eviction timing is node-local), diverging pricing. Deletions therefore leave the window transiently under-full — the safe direction. Recompute once per block; advance amortized O(1); buckets older than `E` are discardable.
- **Warm-eviction impossibility (per cache)**: cold entries form a contiguous tail segment (list order = stamp order), so eviction consumes cold mass first, and a warm victim requires warm mass ≥ physical capacity — excluded by `BUDGET + slack < M`, slack = in-flight unstamped inserts (front-of-list, bounded per unfinalized window) + abandoned-proposal orphans (bounded post-Cadence). Enforced by the per-eviction assert (§3).

## 3. Data structures & code integration

| Change | Where | Notes |
| --- | --- | --- |
| Single u64 field replacing `lru_time_` = the consensus stamp | `lru_cache.hpp` / `lru_weight_cache` | Main cache holds live entries only (negatives moved to the side-cache), so the field has one meaning: the consensus stamp, written ONLY at stamp application in finalize order (audit: today's `find()` writes `lru_time_` — that write must not exist in the main cache; `find()` becomes read-only, no clock call, no list op). The negative side-cache keeps its own local recency (wall-clock or block, non-consensus) |
| Read-stamp collection during execution | per-txn access data | record cold-insert (`MissResolved`) and stale-warm-read keys; write set already exists |
| Stamp application at finalize | `DbCache::on_finalize` → `insert_in_lru_caches` path | single-threaded, commit order: set stamps, update ring buffers, append blob. Write-stamps come from the post-state itself; read-stamps from the collected list carried on `ProposalPostState` (`CommitBuilder::take_proposal_post_state()` in `trie_db.cpp`) |
| Proposal overlays | `Proposals` | stamp deltas ride `ProposalPostState`; warmth lookups resolve through the proposal chain exactly as value reads do; discarded proposals discard their stamp overlays (post-Cadence, undecided proposals are bounded and held in memory) |
| Eviction safety **by construction — no pinning mechanism** | `LruCache` + `DbCache` | Two preconditions: (1) **negatives are list-segregated: one map, two lists**. A *negative entry* is a cached "this key holds nothing" result (nullopt account, empty page). Negatives never stamp, so on a shared eviction list their inserts (~18.5k/blk adversarial) would push warm entries toward eviction. Keep a single hash map (one lookup; coherence by construction — a creation flips the same entry in place at finalize, no cross-cache invalidation), but the entry's list node lives on either the **live list** (stamp-ordered, finalize-promoted, own budget — the eviction theorem applies) or the **negative list** (own small budget and recency policy, evicted independently); a negative flood can only churn the negative list. Transitions (create/delete) are O(1) delink/relink on the shared entry; (2) **live entries are promoted only at stamp application** (finalize, commit order). Then main-cache list order = stamp order (deterministic, restored identically by restart replay), the tail is always the oldest-stamped entry, cold (stamp < E) entries always sit behind all warm ones, and a warm eviction requires warm ≥ physical capacity — impossible while `budget + in-flight slack < M`. `evict()` stays the original pop-tail plus `MONAD_ASSERT(victim.stamp < finalized_E)` as an invariant check. The old 2× margin (promotion drift, order non-determinism) is obsolete; required slack = unstamped in-flight inserts + weight granularity |
| Histogram | in-memory arrays, ~D buckets each | KBs; never persisted; rebuilt from blobs on restart |
| `E_a`, `E_s`, thresholds | computed once per block at start | one shift + compare per access thereafter |

**Hot-path budget (acceptance criterion):** warm hit = 2 integer compares on in-hand data, zero locks, zero writes; stale/cold/write paths add one in-memory vector append + two array ops at finalize; per block one sequential blob append + one hash. No new trie writes anywhere.

## 4. Persistence & recovery

- **Blob per block**: canonical serialization of all stamp changes `(key, prev_stamp)` (reads and writes; one unified stream). Organic ~120–240 KB, ceiling-capped ≤ ~10 MB. Append sequentially; drop whole files older than the window.
- **Commitment**: 32-byte blob hash committed per block (placement — header field vs. one leaf-per-block rolling structure — is a consensus-team decision; content is fixed). This is what makes pricing reconstructible/verifiable for a bootstrapping node.
- **Restart**: rebuild stamp table + histograms + `E` by last-writer-wins replay of the last-D blobs (warm set = keys with latest stamp ≥ E; every warm item appears in the window by definition). Sequential, ~150 MB organic, seconds. This replay also enumerates what to prefetch into the physical cache.
- **Truncation**: post-Cadence, bounded undecided proposals keep all overlays in memory — no special handling beyond discarding overlays. (Blob replay is for process restarts, which Cadence does not remove.)
- **Bootstrap/statesync**: fetch the window's blobs, verify each against its committed hash, replay. Optional later: a periodic O(1)-maintained table-level multiset hash to cap sync depth. Not a launch blocker per current priorities.

## 5. Invariants (enforce and test)

1. **Safe direction**: every protocol failure mode overcharges. Never charge `1000` for an item the node cannot serve from memory — the invariant `stamp ≥ E ⇒ physically resident` holds by construction (stamp-order eviction + budget < capacity, §3) and is asserted at every eviction; a violation is a consensus bug, not a perf bug.
2. **Determinism**: stamps, ring buffers, and E are pure functions of committed execution — identical across nodes regardless of scheduling; never influenced by `lru_time_`, physical LRU order, or speculative execution. Test: same block set under different thread counts/schedules ⇒ byte-identical blobs.
3. **Replay equivalence**: stamp table rebuilt from blobs == live table, every block (fuzz with restarts mid-stream).
4. **Three prices only**: refresh firing must not change any charge.
5. **Exact counting**: Σ live bucket counts == live warm-entry count/weight, exactly, under concurrent-block churn and incarnation deaths.

## 6. Bounds the implementation must uphold (from `design-v2.md` §3)

| Quantity | Bound |
| --- | --- |
| Stamps per block | ≤ `K_STAMP_CEILING` (262k); gas-feasible max ~150k; organic ~3–6k |
| Blob volume | ≤ ~10 MB/block ceiling; ~4 MB gas-capped; ~0.2 MB organic |
| Sustained refresh rate | ≤ budget/C_MIN (accounts: ~78k/blk) — self-capped by eligibility |
| Honest warmth floor under max attack | ≈ C_MIN blocks (~26 s), vs. ~12 min organic |
| FIFO degeneration / capacity spiral | unreachable (needs ≥ budget/C_MIN distinct churn vs. ~21k gas cap; exact counting) |

## 7. Validation plan (replay harness, before freezing constants)

1. Per-cache stamp rate and window depth distribution (organic + synthetic attack) → confirm budgets, ALPHA, C_MIN margins.
2. Inter-touch gap distribution of cached-tier accesses → confirms α = ½ vs ¼ coverage tradeoff.
3. Fraction of cold accesses to nonexistent leaves → sizes the accepted empty-read gap.
4. Physical eviction of protocol-warm entries at current physical sizes under adversarial churn → validates the 2× margins and pinning pressure.
5. Coverage: warm-hit share and gas saved vs. RW-track expectation (~75% of access gas) with lazy refresh enabled.
6. Determinism fuzz (invariant 2) and restart-replay fuzz (invariant 3).

## 8. Open items (flag, don't decide, during implementation)

- Final `ACCOUNT_WINDOW_BUDGET` / `STORAGE_WINDOW_BUDGET` values after §7.1/7.4.
- Blob-hash commitment placement (consensus team).
- Interaction with MIP-8 page encoding rollout (this spec assumes page-keyed storage; the current slot-keyed DbCache works with per-slot keys until then).
- Contract code warmth: `read_code` bypasses DbCache today — out of scope; revisit separately.
- RPC endpoint exposing an item's stamp and current E (estimator support; wallets default to cold).
- Fee-estimation guidance and docs (no duration guarantees exist — recency ordering only).
