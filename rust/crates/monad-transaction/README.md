# Native and Ethereum transaction envelopes

This crate is the shared Rust boundary for the baseline Monad `0x40` development profile. It lives in the execution repository's existing Rust workspace, alongside the separate `monad-alloy` client crate. Execution event readers, the execution bridge, consensus/RPC and the client adapter consume this one implementation. The crate has no provider, transport, C++ or node build dependency.

The authoritative input is the main injection-based universal transaction draft (SHA-256 `79ce4f8c4910a71e3a2932c1083312577e2ef99774a98ddba081bf20face1cb9`). The approved phase-0 amendment (2026-11-16) limits outer chain IDs to uint64 and both fee caps to uint128. Values and signature scalars remain uint256; nonce and gas remain uint64. Baseline execution is still restricted to development chain 20143. This deliberately narrows the draft's uint256 fee domain; the preserved draft is unchanged.

- `TxMonad` holds required features 1, 2, 3, 6 and 7, with optional access-list feature 4. The signature is stored in `Signed<TxMonad>` and injected into feature 6 during canonical serialization.
- `TxEnvelope` preserves existing signed Alloy variants and adds the native variant. Both envelopes implement Alloy 2.0.4's `Transaction`; `TxMonad` also implements `SignableTransaction<Signature>`. Import those traits for their accessors and signing methods.
- `encoded_for_signing()` encodes `0x40 || RLP([chainId, features])`, with feature 6's value replaced by the RLP empty list.
- `Encodable2718` and `Decodable2718` use the two-field signed canonical envelope. The signed hash is its Keccak-256 digest.
- `Encodable`/`Decodable` and `network_encode`/`network_decode` use block/IPC RLP framing: legacy envelopes are lists, typed envelopes are byte strings containing the raw canonical envelope. Both transaction and receipt decoders bound the item before decoding and require exact consumption. They reject unwrapped typed bytes, incorrect lengths, nested wrappers and extra payload bytes. Use `decode_2718_exact` for raw canonical bytes; network framing never contributes to the transaction hash or signing digest.
- `TxMonad::encode_submission(signature)`, `TxEnvelope::encode_submission()` and `TxEnvelope::decode_submission()` are the RPC-only three-field form with empty auxiliary data. The canonical parser rejects submission bytes and vice versa.
- The native receipt has five fields: status, cumulative gas, bloom, logs and an empty extension list.
- RPC aliases reuse Alloy's `Transaction<TxEnvelope>`, `TransactionReceipt<ReceiptEnvelope<Log>>`, `Block` and `FeeHistory`. Native fees/rewards are uint128, serialized as hex quantities. A native JSON `gasPrice` above uint128 is rejected before Alloy can clamp metadata; Ethereum metadata retains Alloy's existing behavior. Missing/null receipt prices and the `gasPrice` alias retain Alloy's zero default.

Node decoders reject unknown features and authorization-list feature 5, including an empty list. Sponsorship and batching are not implemented. Access-list absence is distinct from an explicitly empty list for both signing and transaction identity. Decoding preserves signatures; recovery and validity reject high-s rather than rewriting received bytes. Activation, intrinsic gas, maximum executable nonce and balance/cost validity belong to the node's validation layers.

Storage framing belongs to the paired BFT database adapters. C++ TrieDB records contain raw EIP-2718 bytes inside a byte string; existing Rust archive records contain network RLP bytes inside that field. Those adapters explicitly support both representations with exact record/field bounds. Archive writes retain their existing format; this compatibility does not relax block or IPC parsing.

Tests use the [SDK fixtures](tests/fixtures/monad_type40_vectors.json), generated from Viem commit `40e3a58c1c8c9c0326558eee8991992173059ea4`, plus malformed-input regressions. The vectors are included in the crate so tests do not require an execution checkout. From the workspace root:

```sh
cargo test --locked -p monad-transaction
python3 ../scripts/fixtures/check-monad-rust-fixtures.py
```

Regenerate the vectors using execution's `scripts/fixtures/generate-monad-transactions.cjs`, then deliberately update both workspace snapshots and rerun Rust/C++ comparisons. The fixture check detects drift between the copies. The paired node development profile records the required MONAD_TEN/pre-NEXT setting and execution-event schema requirements; this extraction does not change them.

## Numeric bounds and compatibility

Rust canonical/submission/JSON decoders reject fee caps at or above `2^128` and outer chain IDs at or above `2^64`. C++ transaction storage and its structural RLP decoder remain uint256; static validation rejects the same oversized native inputs before execution. Existing Ethereum validation is unchanged. Gas × fee and balance calculations still use uint256. For all in-range inputs, canonical bytes, signing digests, transaction hashes and receipt commitments are unchanged.

The C++ event writer, layout, schema and fingerprint are unchanged by this amendment. The Rust reader uses checked conversions for the three narrowed fields, with invariant failures for invalid committed events, matching the existing Ethereum reader's approach. Wide historical native transactions cannot be reconstructed with the narrower Rust type; audit stored data or start a fresh devnet before deployment. This change has not been deployed to the shared devnet.

The preserved wide-fee and wide-chain SDK fixtures now test Rust rejection and C++ structural decoding plus validation rejection. Other vectors continue to check identical bytes, hashes, signing digests and recovered senders. Additional boundary tests cover uint128/uint64 maxima, one-above-max rejection, uint256 call values, RPC quantities and event reconstruction.

The amended source passed category-box validation on 2026-11-16: 19 shared-crate tests, 31 C++ codec/validation tests, and 4 execution-event tests plus its documentation test (2 existing snapshot tests remain ignored). The paired BFT checkout also passed its policy/pool/type suites, 14 Ethereum RPC wire tests, all 193 RPC unit tests and workspace Clippy. See the paired development profile for source revisions and retained logs.

An independent review exercised 480 freshly signed boundary cases. The 180 in-range cases matched Rust and C++ on canonical bytes, signing preimages/digests, hashes and sender recovery; all 300 oversized cases were rejected by Rust decoding and C++ validation. RPC round trips and effective-fee calculations also passed. The probe and results are retained under the category-box validation directory's `review/` subdirectory.

The companion [`monad-alloy`](../monad-alloy/) crate supplies the network/request/provider adapter. It preserves explicit native type selection and applies `encode_submission()` to wallet and signed-envelope sends; Alloy's default signed-send path emits canonical bytes. `TypedTransaction` supplies the shared unsigned union required by Alloy wallets. New native wallet signatures normalize to low-s and recompute their canonical hash, while decoders preserve received bytes. Viem and Rabby's SDK bounds are a separate follow-up: their existing in-range transactions remain compatible, but they can still construct oversized transactions which these nodes reject.
