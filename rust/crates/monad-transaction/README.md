# Native and Ethereum transaction envelopes

This crate is the shared Rust boundary for the baseline Monad `0x40` development profile. It lives in the execution repository so its transaction codec, event readers, execution bridge and the parent `monad-bft` checkout use one implementation.

The authoritative input is the main injection-based universal transaction draft (SHA-256 `79ce4f8c4910a71e3a2932c1083312577e2ef99774a98ddba081bf20face1cb9`). Baseline validity is restricted to development chain 20143; the codec preserves uint256 chain IDs and fee/value quantities without narrowing. Nonce and gas are uint64.

- `TxMonad` holds required features 1, 2, 3, 6 and 7, with optional access-list feature 4. The signature is stored in `Signed<TxMonad>` and injected into feature 6 during canonical serialization.
- `TxEnvelope` preserves existing signed Alloy variants and adds the native variant. It deliberately does not implement Alloy's `Transaction` trait, whose fee methods return uint128.
- `encoded_for_signing()` encodes `0x40 || RLP([chainId, features])`, with feature 6's value replaced by the RLP empty list.
- `Encodable2718` and `Decodable2718` use the two-field signed canonical envelope. The signed hash is its Keccak-256 digest.
- `Encodable`/`Decodable` and `network_encode`/`network_decode` use block/IPC RLP framing: legacy envelopes are lists, typed envelopes are byte strings containing the raw canonical envelope. Both transaction and receipt decoders bound the item before decoding and require exact consumption. They reject unwrapped typed bytes, incorrect lengths, nested wrappers and extra payload bytes. Use `decode_2718_exact` for raw canonical bytes; network framing never contributes to the transaction hash or signing digest.
- `encode_submission()` and `TxEnvelope::decode_submission()` are the RPC-only three-field form with empty auxiliary data. The canonical parser rejects submission bytes and vice versa.
- The native receipt has five fields: status, cumulative gas, bloom, logs and an empty extension list.
- Full-width RPC wrappers preserve normal Ethereum JSON fields; native fees and fee-history rewards remain uint256.

Node decoders reject unknown features and authorization-list feature 5, including an empty list. Sponsorship and batching are not implemented. Access-list absence is distinct from an explicitly empty list for both signing and transaction identity. Decoding preserves signatures; recovery and validity reject high-s rather than rewriting received bytes. Activation, intrinsic gas, maximum executable nonce and balance/cost validity belong to the node's validation layers.

Storage framing belongs to the paired BFT database adapters. C++ TrieDB records contain raw EIP-2718 bytes inside a byte string; existing Rust archive records contain network RLP bytes inside that field. Those adapters explicitly support both representations with exact record/field bounds. Archive writes retain their existing format; this compatibility does not relax block or IPC parsing.

Tests use the [SDK fixtures](../../../category/execution/ethereum/core/test/monad_type40_vectors.json), generated from Viem commit `40e3a58c1c8c9c0326558eee8991992173059ea4`, and malformed-input regressions. Regenerate from the execution root with:

```sh
node scripts/fixtures/generate-monad-transactions.cjs /path/to/built/viem-monad
cargo test --manifest-path rust/Cargo.toml -p monad-transaction
scripts/test-monad-type40.sh
```

The C++ script runs the independent execution codecs and static validators on Linux x86-64/AVX2 with Clang 19 and C++26, matching the execution toolchain. Activation tests cover Monad revisions before and after Prague, reject Ethereum traits and unknown transaction types, and retain chain 20143 as the only enabled network. Neither codec vectors nor static validation tests establish a live executed transaction. See the paired BFT branch's `docs/monad-type-40.md` for the required pre-NEXT devnet configuration and full integration boundaries.

Execution event producers and readers must use the same checkout and a fresh ring. The native access-list presence flag remains part of the event schema; its fingerprint is derived from the current `eth_ctypes.h`, `exec_event_ctypes.h` and `monad_ctypes.h` contents, in that order. The Rust bridge uses the current `monad_address`/`monad_bytes32` C types.
