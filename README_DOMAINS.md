# Private Domain Execution

This branch supports state-changing domains only through the private,
L1-sequenced execution path. Read-only `eth_call` requests may simulate an
inner transaction directly. Ordinary Monad transactions always execute against
root state.

Domain lifecycle and commitment are an external smart-contract concern. The
[monad-domains](https://github.com/eerkaijun/monad-domains) contracts
provide that layer; the execution client does not include a native domain
bridge or commit private domain roots into root EVM storage.

## What Changed

- Ordinary transactions must use the configured network chain ID. A domain
  chain ID is rejected with `TransactionError::WrongChainId`.
- `MonadConsensusBlockBody` has exactly three fields: transactions, ommers,
  and withdrawals. The optional signed domain-batch field was removed, and
  a four-field body is rejected during RLP decoding.
- The native domain bridge at `0x1002` was removed from the precompile
  registry. Native registration, ownership, deposits, withdrawals, commitment
  reads, deferred mints, and block-end commitment writes no longer exist.
- `eth_call` can simulate an inner private transaction directly: a
  domain-qualified `chainId` selects that domain's state and gasless
  execution rules. Other RPC simulation and tracing paths execute ordinary
  transactions only against root state.
- State sync verifies and syncs root state without discovering domain roots
  through bridge storage.
- Native-only C++, Python, and fixture coverage was removed. The remaining
  domain integration suite exercises private gasless execution.

## What Stays The Same

- Private domains use independent account and storage tries keyed by a
  64-bit domain ID.
- A private domain ID must differ from the network chain ID, fit in
  `uint64_t`, and have the same low 16 bits as the network chain ID.
- Nodes opt into assigned domains and provide their domain-local
  DomainSpoke address and receiver key with repeatable
  `--private-domain <chain_id> <spoke_address> <private_key_pem_path>`
  mappings, and configure the L1 sequencing contract with
  `--private-domain-sequencer <address>`.
- The runloop scans successful or reverted outer L1 calls by destination and
  calldata. Matching `sequenceToDomain(uint64,bytes)` payloads for locally
  assigned domains are HPKE-decrypted and decoded into gasless inner
  transactions.
- Private domain state, transactions, receipts, sender metadata, and
  transaction-hash locations remain persisted in domain-specific database
  branches.
- Runtime reverts remain stored with failed receipts. Transactions rejected
  before execution are omitted from private transaction and receipt tables.
- `monad-cli --dump-state` continues to enumerate root accounts and private
  domain state.
- Finalized `DomainStateUpdated` events emitted by the configured external
  contract are still checked against the corresponding historical private
  domain root when that root is locally available.

## Configuration

Private domain configuration is validated at startup:

- At least one `--private-domain` requires a nonzero
  `--private-domain-sequencer`.
- The network chain ID must fit in 16 bits when private domains are enabled.
- Every private domain ID must pass the suffix rule above.
- Every DomainSpoke address must be a nonzero 20-byte address.
- IDs are sorted before execution, and duplicate mappings are rejected.
- Every mapping must load an unencrypted P-256 private key.

Example:

```text
monad \
  --private-domain 0x0051000000004eaf 0xabcd000000000000000000000000000000001234 /secure/domain-51-private.pem \
  --private-domain-sequencer 0x1234000000000000000000000000000000005678 \
  ...
```

The sequencer address is the L1 DomainHub-compatible contract. The address
inside each `--private-domain` mapping is the DomainSpoke deployed in
that domain. The client invokes `canCall(address,address,bytes)` on the
spoke before every EVM call and fails closed if the spoke is absent or returns
anything other than canonical ABI `true`. During `canCall`, the spoke may make
direct static subcalls, but those callees may not make further calls. Any such
second-hop call attempt denies domain access, even if its failure is caught.

Generate the unencrypted P-256 PKCS#8 PEM private key and matching public key
with OpenSSL:

```text
openssl genpkey -algorithm EC \
  -pkeyopt ec_paramgen_curve:P-256 \
  -out domain-private.pem \
  -outpubkey domain-public.pem
chmod 600 domain-private.pem
```

Encrypted private-key PEM files are not supported. Back up the private key and
retain it for historical replay. Public-key distribution to producers is an
authenticated external operational concern; the client does not print
receiver public keys. Use a distinct key for each domain to preserve
confidentiality isolation; the client does not enforce key uniqueness.

The fixed encryption profile is RFC 9180 Base mode:

- KEM: DHKEM(P-256, HKDF-SHA256), ID `0x0010`
- KDF: HKDF-SHA256, ID `0x0001`
- AEAD: AES-128-GCM, ID `0x0001`
- `info`: exact ASCII `private-domain-hpke-rfc9180-v1`
- AAD: empty

The ABI bytes value is `enc || ciphertext_and_tag`, where `enc` is a 65-byte
uncompressed SEC1 P-256 point. The authenticated plaintext is
`0x01 || signed_transaction_bytes`; the signed bytes include any EIP-2718 type
prefix and are not placed in an additional RLP wrapper. A fresh Base-mode HPKE
context and sequence number zero are used for every transaction.

## Execution Flow

For each L1 block, the client:

1. Scans ordinary root transactions whose destination is the configured
   sequencer and whose calldata matches
   `sequenceToDomain(uint64,bytes)`.
2. Filters calls to the domains assigned to the local node.
3. Decrypts the opaque bytes with the selected domain key, authenticates
   the empty-AAD ciphertext, and checks the `0x01` frame version.
4. RLP-decodes each recovered signed transaction and verifies that its signed
   chain ID is the selected private domain ID.
5. Executes eligible inner transactions as gasless transactions against the
   domain state at the L1 parent version.
6. Executes the ordinary L1 block exclusively against root state.
7. If both paths succeed, commits the private domain deltas and aligned
   domain transaction/receipt metadata alongside the L1 block.

The private path is staged: if ordinary L1 execution fails, its domain
changes and domain block-table entries are discarded.

Private domain roots are not written into root EVM state by the client. The
external contract system may publish commitments and emit
`DomainStateUpdated`; local validation compares those events to previously
committed domain trie roots.

## Transaction Rules

Outer sequencing transactions are ordinary L1 transactions and therefore use
the network chain ID.

An embedded private transaction:

- must have the selected private domain ID as its signed chain ID;
- must be signed and recoverable;
- must have zero value;
- must have a gas limit no greater than its outer L1 envelope;
- is subject to normal nonce, intrinsic-gas, and execution validation.

The inner sender pays no gas. Gas use is still metered and recorded in its
private receipt.

### Direct `eth_call` simulation

The normal `eth_call` transaction object may contain a domain-qualified
`chainId` to simulate the corresponding inner L2 transaction without building
or encrypting an outer L1 envelope. The call executes against the domain
state at the selected L1 block version and uses the private gasless rules: the
sender is not charged for gas, `value` must be zero, and the `CHAINID` opcode
returns the domain-qualified ID. The standard `from` field selects the
simulated sender; a signed raw transaction is not required.

An omitted, zero, or network `chainId` retains the ordinary root-state
`eth_call` behavior. Structurally valid domains with no local history are
treated as empty state, and state overrides are applied within the selected
domain. Invalid domain IDs are rejected as wrong-chain-ID errors.

HPKE Base mode hides transaction details from parties without the receiver
key, but it does not authenticate the producer. Empty AAD intentionally does
not bind a ciphertext to outer chain ID, domain ID, L1 nonce, or gas limit.
An authenticated ciphertext can therefore be moved to another envelope using
the same receiver key, including one with more gas. The signed inner chain ID
and nonce are the execution replay boundary; a future-nonce ciphertext can be
submitted again until that nonce is consumed. Receiver-key compromise exposes
historical ciphertext, and decrypted transactions are stored in the local
database. Optional `--exec-event-ring` traces can also contain transaction
calldata and call-frame inputs and must be protected like the database.

Every replica that executes a domain must use the same receiver private
key; this single-recipient profile does not support distinct per-replica keys.
Because reverted outer calls are still scanned, DomainHub authorization is
not a producer-authentication boundary: anyone with the public key can submit
a signed inner transaction. Deployments must treat this unauthenticated
gasless work as part of their denial-of-service threat model.

## Database Layout

Root account state retains the standard branch:

```text
STATE_NIBBLE + keccak(address)[64] + keccak(storage_key)[64]
```

Private domain state uses:

```text
DOMAIN_STATE_NIBBLE + domain_id_be64[16] + keccak(address)[64]
DOMAIN_STATE_NIBBLE + domain_id_be64[16] + keccak(address)[64] + keccak(storage_key)[64]
```

Private block data uses:

```text
DOMAIN_TRANSACTION_NIBBLE + domain_id_be64[16] + rlp(transaction_index)
DOMAIN_RECEIPT_NIBBLE + domain_id_be64[16] + rlp(transaction_index)
DOMAIN_TX_HASH_NIBBLE + domain_id_be64[16] + keccak(rlp(transaction))
```

Transaction and receipt indices are local to a domain's L1 block and restart
at zero. Hash-index entries persist and store
`rlp([block_number, domain_transaction_index])`.

Contract bytecode remains in the shared code table and is addressed by
`code_hash`; account state and storage remain isolated by domain.

## State Dumps And Validation

```text
monad-cli --db <triedb-path> --version <block_number> --dump-state <output.json>
```

The dump contains root `accounts` plus a `domains` object keyed by the
big-endian domain ID. The Python state-root helper independently recomputes
the root state root and every dumped private domain root. It does not expect
a bridge account or a root-state commitment slot.

## Tests

Focused C++ coverage includes chain-ID validation, private scanning, private
execution, block-body decoding, storage migration, RPC behavior, and state
sync. The Python end-to-end suite covers gasless deployment and calls, invalid
payload filtering, cross-library HPKE production, authentication and framing
failures, replay behavior, runtime failure receipts, domain isolation,
persistence across restarts, staging rollback, and finalized-root validation:

```text
uv venv /tmp/monad-domain-tests
uv pip install --python /tmp/monad-domain-tests/bin/python \
  -r test/python/domain_integration/requirements.txt
/tmp/monad-domain-tests/bin/python -m pytest \
  test/python/domain_integration/ -n 4 -v
```

## Compatibility

Blocks that contain the removed fourth consensus-body field are not accepted.
Ordinary submitted transactions that attempt to select domain execution by
using a domain chain ID directly are rejected. Direct domain selection
is supported only for read-only `eth_call` simulation; state-changing private
transactions must be published through the configured external sequencer
contract.
Plaintext `sequenceToDomain` payloads are no longer accepted, so historical
plaintext domain blocks cannot be replayed or rebuilt by this version.
