# Monad Rust transaction support

The execution repository owns two separate Rust crates for phase-0 `0x40` transaction support and Alloy client integration. It uses upstream Alloy 2.0.4 without a fork. Execution Rust adapters and consensus/RPC depend on `monad-transaction`; applications use `monad-alloy`.

| Crate | Responsibility |
| --- | --- |
| [`monad-transaction`](crates/monad-transaction/) | Canonical transaction and receipt types, signing payloads, hashing, strict RLP codecs, RPC submission encoding and aliases for Alloy RPC response types. No provider, transport or node build dependency. |
| [`monad-alloy`](crates/monad-alloy/) | `MonadNetwork`, request validation, Alloy wallet integration, fee/nonce/chain fillers, native submission and typed RPC reads. Depends on the protocol crate. |

The dependency direction is `monad-alloy → monad-transaction → Alloy primitives/consensus/RPC types`. Both node repositories also depend directly on `monad-transaction`. These two crates can be built and tested without compiling C++ or other node crates. The surrounding execution workspace also contains the existing node adapters.

## Supported profile

Native transactions are explicit opt-in: `MonadTransactionRequest::native()`. Default requests retain Ethereum type inference. Phase 0 supports a sender-paid single call or creation, with optional access lists. Sponsorship, batching, native authorization lists, blob fields and nonempty auxiliary data are rejected. Nodes enable this experimental profile only on development chain **20143**; the generic codec represents any uint64 chain ID.

The authoritative format is the main universal transaction draft, SHA-256 `79ce4f8c4910a71e3a2932c1083312577e2ef99774a98ddba081bf20face1cb9`, with the approved 2026-11-16 amendment: uint128 fee caps and uint64 outer chain IDs. Values and signature scalars remain uint256. Access-list omission and an explicitly empty access list have different commitments.

```text
signing preimage = 0x40 || RLP([chainId, features with signature feature 0x06 = []])
canonical       = 0x40 || RLP([chainId, signedFeatures])
transactionHash = keccak256(canonical)
RPC submission  = 0x40 || RLP([chainId, signedFeatures, []])
```

Blocks, transaction identity and signing use canonical bytes. RPC submission alone adds the empty auxiliary list. New wallet signatures are normalized to low-s; received signatures are never rewritten. Native signature recovery rejects high-s and invalid scalars.

See the [client guide](crates/monad-alloy/README.md) for signing, sending, reading and the distinction between envelope and raw-byte submission.

## Build and test

Run these commands from `rust/`, using its existing Rust toolchain and lockfile. Selecting the two crates does not require the C++ toolchain or a running RPC.

```sh
cargo test --locked -p monad-transaction -p monad-alloy --all-targets
cargo test --locked -p monad-transaction -p monad-alloy --doc
cargo clippy --locked -p monad-transaction -p monad-alloy --all-targets -- -D warnings
cargo +nightly-2025-12-09 fmt -p monad-transaction -p monad-alloy --check
python3 ../scripts/fixtures/check-monad-rust-fixtures.py
```

HTTP tests inspect the actual RPC requests and responses: explicit native type, fillers, signed and raw submissions, async/sync sends, canonical hash verification, receipts and full blocks. Request tests cover unsupported fields, duplicates, numeric overflow, creation/access-list presence, Viem vector parity and Ethereum signing compatibility. The protocol suite retains strict decoding, framing and RPC compatibility regressions.

On 2026-11-17, all 44 protocol/client tests, the client documentation example and Clippy passed with the existing Rust 1.91.1 toolchain locally and Rust 1.97.1 on Linux. Paired Linux checks also passed the execution-event tests, 14 Ethereum RPC wire regressions and the full BFT workspace check. The existing execution toolchain and all previously locked package versions are retained.

The read-only example verifies the transaction, receipt and full block returned by an RPC:

```sh
cargo run --locked -p monad-alloy --example inspect -- RPC_URL TRANSACTION_HASH
```

## Ownership and dependency boundaries

Both crates are members of this repository's existing Rust workspace:

```text
monad/
  rust/
    crates/
      monad-transaction/
      monad-alloy/
```

`monad-exec-events`, `monad-cxx` and BFT depend on `monad-transaction`. They do not depend on `monad-alloy` or its provider/transport dependencies. BFT uses `./monad-execution/rust/crates/monad-transaction` through its existing execution submodule, so one execution revision identifies the shared implementation. A standalone execution checkout needs no sibling repository or path override.

The protocol/client separation is a crate boundary within the execution repository. It requires no new repository or additional git pin. The existing Rust CI includes the client crate through the workspace, and checks all three fixture snapshots. Both crates retain GPL-3.0-or-later. If registry publishing is added later, publish `monad-transaction` before `monad-alloy`; publishing is not required to build these branches.

C++ codecs, execution-event readers/writers, event layouts, storage formats and RPC wire contracts are unchanged. The shared devnet has not been redeployed with the client-crate changes.
