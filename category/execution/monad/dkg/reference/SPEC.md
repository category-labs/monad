# DKG contract specification

## Stored state

- `STAKING` is the immutable staking precompile.
- Two reusable `DkgState` slots retain only `active = current staking epoch` and `next = active + 1`. Each slot has exactly five mappings: validator-ID-keyed registrations, separate typed PC-QC and BVE-QC collections, and dealer-keyed PC/BVE markers. It also holds at most one result.
- Native execution initializes the slots from block prelude, configures `next` from the authenticated staking snapshot hook, and promotes it from the staking epoch-change hook. User transactions only verify that DKG and staking lifecycle state agree and fail closed on a mismatch. The Solidity reference still performs the equivalent synchronization lazily because it cannot receive native system hooks.
- Slot reset sets the slot epoch and zeroes counters in constant time. Each registered-party value and deduplication marker carries that epoch, so stale mapping entries are ignored after reuse. The authenticated caller's canonical compact `PartyId` is obtained during the required party-set scan, without another staking lookup and must equal the QC dealer. Both markers are dealer-keyed (at most `maxPartyCount` per slot). The two QC mappings reuse collection indexes and overwrite dynamic signatures incrementally. No rollover copies a mapping-containing struct or clears an unbounded array.
- The contract stores evidence, not finality or activation policy. Consumers must read finalized state.

## Mutable methods

### `register(epoch, registration)`

- **Validate:** registration targets the synchronized `next` slot (`currentEpoch + 1`), before staking enters its delay period; the authenticated caller has a nonzero validator ID; that validator ID is not already registered in the slot's epoch.
- **Update/output:** store the registration. Registrations are consumed from finalized state, not logs.
- **External use:** after the validator set locks, runners read registrations in staking order to derive the common `PartyId -> validator` mapping. Invalid keys or proofs are retained in that canonical mapping and counted as Byzantine weight by the protocol. Consume only finalized state.

### `postPcQc(epoch, qc)`

- **Validate:** `epoch` is the active slot, or the next slot during staking delay; caller belongs to that epoch's party set and is `qc.dealer`; no result is recorded; signatures are nonempty, strictly signer-sorted, distinct, and in range. Cryptographic QC validity is checked by protocol consumers, not this method.
- **Update/output:** the dealer's first submission is appended to the typed PC-QC collection and emits `PcQcPosted`; a repeat is a successful no-op.
- **External use:** finalized events drive VSS delivery/recovery. The event carries the PC collection index; recovery reads `pcQcs` pages in collection order.

### `postBveQc(epoch, qc)`

- **Validate:** same party, terminal-state, dealer, and canonical-signature checks as `postPcQc`; the caller must equal `qc.dealer`, and that dealer must have posted its PC-QC. Cryptographic validity remains an off-chain protocol responsibility.
- **Update/output:** the dealer's first BVE-QC is appended to the typed BVE-QC collection and emits `BveQcPosted`; duplicates are no-ops.
- **External use:** finalized events drive ACS common-set selection and BVE recovery. The event carries the BVE collection index; recovery reads `bveQcs` pages in collection order.

### `submitResult(epoch, result)`

- **Validate:** caller belongs to the epoch party set; no prior result exists; signers are canonical; every secp256k1 signature authenticates the exact domain-separated `(epoch, sessionId, bteKey)` transcript; signed exact staking weight is strictly greater than two thirds of the registered target-epoch parties.
- **Update/output:** mark the epoch terminal; store the slot's single Done QC; emit `DkgResultPosted` without a round.
- **External use:** never activate from a submitted transaction or unfinalized event. Recovery obtains the same Done QC from `dkgResult`. Timing and activation are external policy; the contract does not reject a result by round.

## Read API and activation rule

- `registrationOf(epoch, validatorId)` returns the validator-ID-keyed registration from a retained slot. Clients resolve party addresses to validator IDs through staking first. `pcQcs(epoch, start, limit)` and `bveQcs(epoch, start, limit)` return separate typed pages. `dkgResult(epoch)` returns the one optional Done QC and the execution block that recorded it. Retired epochs read as empty.
- Recovery reads one finalized execution snapshot and replays PC QCs in collection order, then BVE QCs in collection order, then the optional result. Cross-collection posting order is not protocol state.
- For a proposal at execution block `B`, consensus uses only state readable through `B - executionDelay - 1`. It waits until the DKG scanner has caught up to that block, then selects `Active` only if the result's recorded block is at or before it; otherwise it selects `Inactive`. Active additionally requires the locally reconstructed context for that epoch.
- RPC reads the public BTE key directly from finalized `dkgResult(epoch)` state. It rejects encryption/submission while that result is absent.

## DoS and safety constraints

- Two logical slots do not erase every historical mapping key from the trie. Generation tags make stale keys unreachable and recurring validator IDs are overwritten, but validator-ID churn can still grow physical storage. Check target eligibility or cap registrations.
- `_partySet` derives its exact allocation from the bounded staking set instead of the potentially unbounded registration set. The contract intentionally relies on staking's validator-count bound and does not extend the staking ABI to duplicate it. Two paginated scans are currently required per protocol write. Result verification also performs per-party staking calls; benchmark the maximum validator set against the block gas limit, or cache/finalize the party set or move verification to a bounded precompile.
- PC and BVE records are each bounded to `partyCount`: only the dealer may post either QC, and BVE posting additionally requires that dealer's PC-QC. A dealer can still submit structurally valid but cryptographically invalid evidence; every record is paid for by its submitting transaction, and protocol consumers must reject invalid evidence.
- `pcQcs` and `bveQcs` treat `limit` as a caller-selected maximum. Solidity execution gas bounds its work. Native execution may return a smaller nonempty page to enforce internal record/signature budgets; recovery follows `next` until `total`.
- Events are untrusted until their block is finalized.

## Required work items

- **Execution—prototype:** staking signing-address-to-validator-ID access (`e0278f57d`).
- **Execution—required:** land validator-ID lookup and the native DKG contract/lifecycle hooks in production.
- **Contract—required:** version/deploy the ABI and test worst-case gas at staking's maximum validator count.
- **Runner—done:** finalized event decoding and triedb recovery read the two typed QC collections plus the single result. Live and recovery release `DkgBteContext` once the result is finalized and the local context is available. Missing results remain pending.
- **Consensus/node—done:** gate DKG use from one deterministic execution-readable state per consensus block. Local event-observation time does not decide activation.
- **RPC/txpool—done:** RPC reads finalized contract state directly and rejects encryption/submission when the epoch has no result.
- **Tests/docs—partly done:** runner tests cover execution-scan lag, missing DKG, live/recovery equivalence, and fixed-execution-delay activation. Full encrypted-transaction chaos coverage remains required.
