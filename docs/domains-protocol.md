# Domain protocol format

A private domain is a chain whose blocks are derived from the L1. Domain blocks advance in lock-step with the L1: an L1 block yields a block for a domain exactly when it registers the domain or carries at least one of the domain's hub events, and never more than one. Replaying a domain's blocks from genesis rebuilds its state.

This document specifies derivation:

- `derive(l1_block, l1_receipts, previous_header, domain_config) -> Option<DomainBlock>`: what goes in a domain block. It needs no domain state.

Derivation produces each block's proposed header and its transactions; the sequence of `DomainBlock`s is the domain's canonical history. Anyone holding the domain key and configuration can derive it, and all of a domain's replicas must use the same configuration. Nodes configured for a domain derive and store its blocks with every L1 block.

What a block does when it executes, and how its result is attested on L1, are not specified here yet.

# Chain IDs

```rust
/// A domain is identified by a 64-bit chain id whose low 16 bits are the L1 chain id.
///   chain_id == L1_CHAIN_ID                                  -> L1 transaction
///   chain_id < 2^64 && chain_id & 0xFFFF == L1_CHAIN_ID       -> domain `chain_id`
///   otherwise                                                -> invalid
/// L1 consensus rejects a transaction carrying a domain chain id.
/// The L1 chain id must therefore fit in 16 bits.
pub type DomainChainId = u64;
```

# DomainBlock

```rust
/// Output of derivation. Contains everything execution needs and nothing execution produces.
/// The sequence of DomainBlocks from genesis is the domain's canonical history.
#[derive(RlpEncodable, RlpDecodable)]
pub struct DomainBlock {
    pub header: ProposedDomainHeader,
    pub body: DomainBlockBody,
}
```

## ProposedDomainHeader

Populated by derivation. Nothing in it comes from execution.

```rust
#[derive(RlpEncodable, RlpDecodable)]
pub struct ProposedDomainHeader {
    pub domain_chain_id: u64,
    /// domain block height: genesis is 0, then +1 per derived block.
    /// It is NOT the L1 block number. The EVM's NUMBER opcode returns this value
    pub number: u64,
    /// L1 block this domain block was derived from
    pub l1_block_number: u64,
    /// L1 consensus block id of that block
    pub l1_block_id: [u8; 32],
    /// the L1 block's timestamp
    pub timestamp: u64,
    /// the L1 block's mix_hash (EVM PREVRANDAO)
    pub mix_hash: [u8; 32],
    /// DOMAIN_BLOCK_GAS_LIMIT. The hub sells at most this much gas per domain per
    /// L1 block, so the gas limits in a body never sum to more
    pub gas_limit: u64,
    /// DOMAIN_GAS_PRICE, the price paid on L1 for each unit of domain gas. Transactions
    /// are validated against it as a floor; nothing is charged on the domain
    pub base_fee_per_gas: u256,
    /// ordered trie root of body.transactions
    pub transactions_root: [u8; 32],
}
```

## DomainBlockBody

```rust
#[derive(RlpEncodable, RlpDecodable)]
pub struct DomainBlockBody {
    /// sequenced transactions first, in L1 order, then system delivery transactions
    /// in hub nonce order. See Derivation. May be empty
    pub transactions: Vec<TransactionSigned>,
    /// always empty
    pub ommers: Vec<Ommer>,
    /// always empty
    pub withdrawals: Vec<Withdrawal>,
}
```

## Genesis

```rust
/// Domain block 0 is derived from the L1 block whose receipts hold the domain's
///   event DomainRegistered(uint64 indexed domainChainId, address indexed feeRecipient,
///       uint64 checkpointInterval)
///   topic0 = 0x4d67e4de635f33a3a94b18cf726b1240bc94791b6b822e421b8c0902cddde3b7
/// number = 0, l1_block_number/l1_block_id/timestamp/mix_hash = that L1 block's.
/// Its body holds the domain's other hub events in that L1 block, derived like any
/// other block's, so it is usually empty.
///
/// A node derives a domain only from its registration onward: one configured for a domain
/// whose registration it never derived drops that domain's events with an error log.
```

## Derivation state

Derivation needs no domain state. Its inputs beyond the L1 block and its receipts are:

- `previous_header`: the domain's latest `ProposedDomainHeader` (none before genesis). The next block gets `number + 1`.
- `domain_config`: the domain's chain ID, the hub address, the spoke address and the domain key. System transactions are addressed to the spoke, so replicas configured with different spokes derive different blocks.

# Derivation

`derive` is a pure function of the L1 block, its receipts, `previous_header` and `domain_config`. Each step below happens in order. An item rejected at any step is dropped and leaves nothing in the domain block, but its hub event still counts toward block existence (step 3).

Both kinds of hub event carry the `fee` paid for them on L1. The fee buys domain gas at a fixed price:

```rust
/// Mirrors DomainHub.DOMAIN_GAS_PRICE and DomainHub.DOMAIN_BLOCK_GAS_LIMIT.
pub fn purchased_gas(fee: u256) -> u64 {
    min(fee / DOMAIN_GAS_PRICE, DOMAIN_BLOCK_GAS_LIMIT)
}
```

## 1. Sequenced transactions

```rust
/// DomainHub.sequenceToDomain(uint64 domainChainId, bytes rlpTx), payable, selector 0xc791e98a
///
/// The source is the hub's event, not L1 calldata:
///   event DomainTransactionSequenced(uint64 indexed domainChainId, bytes rlpTx, uint256 fee)
///   topic0 = 0x840905264e95f5c327ec724710cb5708abafd6f5070886668d62fc66d4cf34dc
/// Only calls that succeeded produce the event, so reverted calls are excluded and calls
/// routed through other contracts are included.
///
/// Events are taken in (L1 tx index, log index) order. An item is kept iff:
///   - log.address == DOMAIN_HUB && topics[1] == domainChainId
///   - rlpTx opens under the domain key (see Encryption)
///   - the plaintext is a valid EIP-2718 transaction with tx.chain_id == domainChainId
///   - the sender recovers and sender != DOMAIN_SYSTEM_RELAYER
///   - no authorization in tx recovers to DOMAIN_SYSTEM_RELAYER
///   - tx.gas_limit <= purchased_gas(fee)
```

## 2. L1 → domain messages

```rust
/// Taken from hub events in the same L1 block's receipts, in log order (= hub nonce order):
///   event L1MessageRecorded(uint64 indexed domainChainId, uint64 sourceChainId,
///       address indexed from, address indexed to, bytes data, uint256 nonce, uint256 fee,
///       bytes32 messageHash)
///   topic0 = 0x5407b49426d6ce93eaf2b804f06575113f1ce26f67ada45a1307db40662a528a
/// sourceChainId/from are the L1 chain and the hub's caller, or the source domain and
/// sender of a domain message the hub relayed.
/// The hub's EncryptedL1MessageRecorded event is not derived.
///
/// Each message becomes one system transaction:
pub fn system_transaction(msg) -> TransactionSigned {
    TransactionSigned {
        type: Legacy,
        chain_id: domainChainId,
        /// the hub's message nonce, so derivation needs no domain state.
        /// A message whose nonce does not fit in u64 is dropped
        nonce: msg.nonce,
        gas_price: DOMAIN_GAS_PRICE,
        gas_limit: purchased_gas(msg.fee),
        /// the domain's DomainSpoke, configured per domain on the node
        to: spoke,
        value: 0,
        /// relayL1Message(uint64 sourceChainId, address from, address to, bytes data, uint256 nonce)
        data: abi_encode(relayL1Message, msg.sourceChainId, msg.from, msg.to, msg.data, msg.nonce),
        /// signed with DOMAIN_SYSTEM_KEY using RFC 6979 nonces, so every node derives the
        /// same bytes and the sender recovers to DOMAIN_SYSTEM_RELAYER
        signature: sign(DOMAIN_SYSTEM_KEY),
    }
}
```

## 3. Block existence

```rust
/// Lock-step: a domain block exists for this L1 block iff the L1 block registers the
/// domain (genesis) or holds at least one of the domain's DomainTransactionSequenced or
/// L1MessageRecorded events, whether or not steps 1 and 2 keep anything from them. The hub
/// emits every one of these events, so it can count a domain's blocks without reading
/// any ciphertext.
```

# Encryption

Sequenced transactions are the only thing the protocol decrypts in derivation. L1 → domain messages are plaintext; an application that needs to hide a message's content seals it inside the message data itself.

Each domain has one X25519 key pair. The client opens payloads with the HPKE implementation built into AWS-LC, which supports DHKEM(X25519) but not DHKEM(P-256).

```rust
/// HPKE, RFC 9180, Base mode
///   KEM  = DHKEM(X25519, HKDF-SHA256)  (0x0020)
///   KDF  = HKDF-SHA256                 (0x0001)
///   AEAD = AES-128-GCM                 (0x0001)
///   info = "" (empty)
///
/// rlpTx = enc[32] || ciphertext || tag[16]
///   enc is the sender's ephemeral X25519 public key
///   The profile is fixed, so the payload carries no version, scheme or key tag.
///
/// sealed plaintext = FRAME_VERSION || signed EIP-2718 transaction
///   FRAME_VERSION = 0x01, checked and stripped only after the tag verifies; it versions
///   the plaintext layout.
///
/// ad = abi.encode("monad-transaction-encryption-v1", uint64 domainChainId)
///   The ad is never sent: the sender builds it before encrypting and derivation rebuilds
///   it from the event's domainChainId. The label keeps a transaction ciphertext from
///   opening as anything else sealed to the domain key, and the chain id keeps it in its
///   domain should two domains share a key. Its low 16 bits are the L1 chain id, so it
///   also keeps it on its network.
///   No sender is bound: the payer of sequenceToDomain may be a sponsor unknown when the
///   transaction is encrypted, and the signed transaction already authenticates its
///   sender. Resubmitting someone's ciphertext only replays a transaction whose nonce is
///   then spent.
///
/// The node loads each domain's private key from an unencrypted PKCS#8 PEM file.
```

# Constants

```rust
/// the L1 system sender. Mirrors DomainSpoke.SYSTEM_RELAYER
pub const DOMAIN_SYSTEM_RELAYER: [u8; 20] = 0x6f49a8F621353f12378d0046E7d7e4b9B249DC9e;
/// the L1 system sender's private key, which is public by design
pub const DOMAIN_SYSTEM_KEY: [u8; 32] = 0xb0358e6d701a955d9926676f227e40172763296b317ff554e49cdf2c2c35f8a7;
/// price of one unit of domain gas, in L1 wei. Mirrors DomainHub.DOMAIN_GAS_PRICE
pub const DOMAIN_GAS_PRICE: u256 = 50_000_000_000;
/// most gas the hub sells per domain per L1 block. Mirrors DomainHub.DOMAIN_BLOCK_GAS_LIMIT
pub const DOMAIN_BLOCK_GAS_LIMIT: u64 = 150_000_000;
/// the L1 DomainHub, configured on the node
pub const DOMAIN_HUB: [u8; 20];
pub const HPKE_INFO: &[u8] = b"";
pub const FRAME_VERSION: u8 = 0x01;
pub const TRANSACTION_AD_LABEL: &str = "monad-transaction-encryption-v1";
```

# Design choices

- **Derivation never reads domain state.** The system transaction nonce comes from the hub, so domain blocks can be built and stored by a node that never executes them, and execution can run separately, later, or on another machine.
- **Deriving from events instead of calldata** handles reverted and nested `sequenceToDomain` calls with no special cases. The cost is that derivation needs the L1 receipts, so it must run after L1 execution.
- **Lock-step and genesis.** Counting every hub event toward block existence, even one whose payload is dropped, makes block numbering depend only on what the hub saw. Putting the registration block's other events into block 0 means no paid-for event is ever dropped for timing.
- **Fees buy gas, at a fixed base fee.** A transaction may use at most the gas its fee bought, and the hub caps the gas sold per domain per L1 block. Setting the base fee to `DOMAIN_GAS_PRICE` instead of copying the L1's means a signer always knows the floor its transaction is validated against.
- **No protocol encryption for L1 → domain messages.** The hub's L1 side is public, and a message's sender is authenticated by the hub, so the protocol has nothing to hide there; an application that needs privacy seals its own data. This removes a second decryption path, and the attacks where a copied ciphertext is resent from another sender.
- **X25519 rather than P-256.** None of the design documents fixes a curve. X25519 has the same security level, is the most widely used HPKE KEM, and needs no point validation; above all, AWS-LC's HPKE supports it, so the client uses a reviewed implementation rather than one assembled from primitives. P-256 would only matter if domain keys had to live in FIPS modules, HSMs or cloud key services, which they do not today.
