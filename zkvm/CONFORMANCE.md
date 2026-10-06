# What the protocol fixes, and where this tree differs

Behaviour the execution client or the contracts already determine. None of it is
a choice; all of it is work. Choices live in [DECISIONS.md](DECISIONS.md).

The client is
[`monad-private@domains`](https://github.com/category-labs/monad-private/tree/domains)
and the contracts are
[`monad-domains`](https://github.com/category-labs/monad-domains). Where the two
disagree the disagreement is recorded here and the client is followed, per
decision 6.

---

## A domain block is not a block

The client never builds one. Domain transactions execute against the **L1
header** — `number`, `timestamp`, `beneficiary`, `prev_randao`, `gas_limit`,
`base_fee_per_gas` are the L1 block's — and the only domain header that exists is
a two-field record written at commit time:

```cpp
BlockHeader{.state_root = state_root, .number = header.number}
```

Everything else is zero. It exists so finalized-root validation has something to
compare against, nothing more.

What follows, **now done** — the witness carries a domain body rather than a
block ([`domain_body.hpp`](guest/domain_body.hpp)):

- no transactions root over ciphertexts — they arrive as a list, not a block
  body — and no ommers or withdrawals to reject, because nothing can carry them;
- no receipts root committed anywhere, so `gas_used` is not committed either, and
  gas accounting matters only where it moves balances or changes control flow.
  The block-shaped epilogue checks are gated off this path: taken from an L1
  header they would describe the L1 block;
- no parent-hash continuity, and no `static_validate_block_with_parent`: the hub
  orders transitions with `stateNonces` and a strictly increasing block number,
  and the pre-state commitment is what it chains on;
- `BLOCKHASH` is served from **L1** hashes, so the witness carries 32-byte
  hashes, not 544-byte ancestor headers — about 470 bytes a block smaller on the
  scenarios, and more wherever a block ships a longer run;
- the body carries the previous **domain** block's number, which is not
  `number - 1`: the sequence is sparse.

What it costs is recorded in [DECISIONS.md](DECISIONS.md) under what authorises
the L1 inputs: the header and the ancestor run are the prover's, and nothing
published commits to either.

## The trait family is Monad, not EVM

`execute_private_domain_blocks` is `requires is_monad_trait_v<traits>` and
`EXPLICIT_MONAD_TRAITS`. The client's gasless path carries

```cpp
static_assert(!gasless || is_monad_trait_v<traits>);
```

so `EvmTraits<PARIS>` with unpriced gas is a combination its own source refuses to
compile. Monad pricing, reserve balance, cold-access costs and code-size limits
all follow, and all move the state root.

## `canCall` runs on every EVM call

In `pre_call`, so on every message and not only the top-level one: a STATIC call
to the spoke's `canCall(address,address,bytes)` with a 30,000 gas stipend charged
to the caller (`msg.gas -= stipend - gas_left`), failing closed on anything but
canonical ABI `true`. The denial flag is sticky for the whole transaction so a
caller cannot swallow the revert by catching it, and a depth rule makes the
check's callees leaves — a second hop arms the denial.

It changes the gas available to every call, so it moves out-of-gas boundaries and
therefore the state root. It is in the hottest path of the guest.

## Five pre-execution drop rules decide the transaction set

Silent in the client — a log warning, nothing more:

1. HPKE decryption failed;
2. payload malformed after decryption;
3. inner `gas_limit` above the outer L1 envelope's;
4. sender not recoverable;
5. signed chain id is not the domain's.

The first three are **done**, in `decode_domain_body`, and the witness carries
the outer L1 gas limit per payload for the third. The last two sit downstream in
execution and are not yet the silent skips the client makes them. Whether a
reverted outer call is in the set at all is unresolved — see DECISIONS.md,
"Do reverted sequencing calls count?".

## Gas is metered and not priced, but `GASPRICE` is not pricing

The client gates exactly five things behind `if constexpr (!gasless)`: the up-front
purchase and blob fee in `irrevocable_change`, the refund credit, the EIP-7623
balance adjustment, and the beneficiary award in `execute_final`. This tree's
`gas_is_priced()` covers the same five. That part is right.

Two divergences:

**`GASPRICE`.** This tree returns `tx.max_fee_per_gas` raw. The client applies no
gasless branch to `tx_context` at all — it changes only the `chain_id`, so
`CHAINID` reports the domain — and so returns the ordinary effective price
computed against the L1 header's base fee. They differ for essentially every
EIP-1559 transaction, and the sender-side helper sets `maxFeePerGas` to twice the
base fee, so the gap is the normal case rather than an edge one. A contract
reading `GASPRICE` branches differently and moves the state root. What a contract
can observe is an execution input, not economics.

**The EIP-7623 floor** — **fixed.** The client applies it to `gas_used` whether
or not gas is priced and gates only the balance side; this tree dropped it
entirely. Only the debit is economics, so the raise is ungated now and `gas_used`
reports the floor either way. It reads oddly — an unpriced transaction can report
more gas than it consumed — but a receipt that disagrees with the one every
replica stores is a difference nothing here would catch.

Under `EvmTraits<PARIS>` the floor is compiled out entirely, so this is inert
today; it stops being inert the moment the trait family moves.

**The validation gates** — **audited, four divergences fixed.** The client gates
by a template parameter where this tree gates by a build-wide predicate, so the
two sets had to be compared site by site rather than mechanically. Three checks
this tree skipped and the client makes regardless are now ungated: `max_fee <
base_fee`, `max_priority_fee > max_fee`, and the `gas_limit * max_fee` overflow.
A domain transaction is an ordinary EIP-1559 transaction and passes the ordinary
validity rules even though its execution is sponsored — skipping them accepted
transactions the client drops, which is a different transaction set and so a
different state root. The EIP-7623 gate against `gas_limit` is ungated with the
floor it guards.

A fifth: the client's gasless path rejects a transaction with no signed chain id
at all, because a domain-qualified id is what selects the domain's state. This
tree only compared the id when one was present, so an unprotected pre-EIP-155
transaction passed. It is now required.

In the other direction, `v0` is zero when gas is unpriced rather than `tx.value`,
and both balance checks it feeds are skipped, which is what the client's gasless
path does. What the sponsored path cannot pay for, execution fails on.

What the client keeps on both paths and so does this tree: the nonce checks and
the EOA / EIP-7702 delegation check.

## The cipher profile is fixed

RFC 9180 Base mode, exactly:

| | |
|---|---|
| KEM | DHKEM(P-256, HKDF-SHA256), `0x0010` |
| KDF | HKDF-SHA256, `0x0001` |
| AEAD | AES-128-GCM, `0x0001` |
| `info` | ASCII `private-domain-hpke-rfc9180-v1` |
| AAD | empty |
| wire | `enc ‖ ciphertext_and_tag`, `enc` a 65-byte uncompressed SEC1 P-256 point |
| plaintext | `0x01 ‖ signed_transaction_bytes` |

A fresh context and sequence number zero for every transaction. The
`l2_cipher_suite.hpp` seam exists for this swap and the `plaintext` suite stays as
the measurement control; the secp256k1 ECDH with Poseidon2 masks and tag goes.

**No epoch exists.** Keys are per-message from the encapsulated ephemeral, and
neither repo defines an epoch anywhere. `MONAD_ZKVM_L2_EPOCH_BLOCKS` and
`ctx.epoch = number / EPOCH_BLOCKS` correspond to nothing.

**Nor does `NAMESPACE_ID`.** The protocol knows only `domainChainId`.

## Poseidon2 tries and signatures are not deployable

The client requires ordinary signed Ethereum transactions — signed, recoverable,
RLP-decoded with EIP-2718 prefixes, so keccak signatures from stock wallets — and
its database is keyed `keccak(address)` / `keccak(storage_key)`, which is what
finalized-root validation compares. `MONAD_ZKVM_L2_TRIE_HASH=poseidon2` and
`SIGNATURE_HASH=poseidon2` are therefore measurement arms, not configurations that
can ship, and a material share of the savings measured in this tree is unavailable
without changing the client too. Worth saying here so it is not discovered from a
benchmark table.

## Stale constants, which fail quietly

This tree's own vocabulary is the protocol's now — the anchor module, its API,
the spoke constant and the published field all say *domain*. What still says
*namespace* is what names the vendored contract, because that contract has not
moved: the spoke is vendored from `eerkaijun/monad-namespaces` at
`e6012d8cebf4`, from before the rename, and re-vendoring needs solc and brings
`DomainSpoke`'s access-control layer with it.

**The event topic changed.**
`NamespaceMessageRecorded(address,address,bytes,uint256,bytes32)` is
`0x2013a1d0b9a3c17ead41b5433daeef9f5b301d7abece37308528e70113a678df`, which is
what `domain_anchor.hpp` `static_assert`s. `DomainMessageRecorded(...)` with
identical parameter types is
`0x8f2b779508ea0cb38e5b78dbe9c7a04c3ce671ba697fdce1a46dc794e2dd650e`. Against a
real spoke the harvest finds no logs at all.

The pending-length assertion turns that into a loud block failure rather than a
well-formed anchor over an empty leaf set — the case it was written for. It does
not cover a block that sent no messages, where an empty anchor is correct anyway.

**The rest:**

- the pending array is still slot 1 by reading (`_nonce` at 0,
  `_pendingDomainMessages` at 1, no base contract carrying storage), to be
  reconfirmed with `forge inspect`. It is the one pinned constant the rename did
  not have to move;
- the spoke is now intended as a protocol predeploy at a fixed address rather than
  a `CREATE` deployment, so deriving it from a deployer key no longer makes sense;
- `DomainSpoke` gained an access-control layer (`policyOwners`, `accessControl`,
  `approvedReaders`, `canCall`) and a `deployContract` entry point through which
  contract creation passes.

## Where the client and the contracts disagree

**The derivation source.** The hub documents its event as it —
"Domain validators derive their blocks from these events" — while the client scans
the calldata of outer transactions by destination and selector, including reverted
ones, and says so twice. A reverted call emits no log.

**The block number.** The client writes the L1 block number; the reference
end-to-end submits `committedBn + 1`.

**The state commitment.** The client hard-asserts the raw state root with
`MONAD_ASSERT_PRINTF`, so a mismatch stops the node; the reference end-to-end
signs `zeroHash` for it.

## Not implemented anywhere: L1 to domain system transactions

`DomainSpoke.relayL1Message` is `onlySystem`, delivered from
`SYSTEM_RELAYER = 0xffffFFFfFFffffffffffffffFfFFFfffFFFfFFfE` with a fixed
`DELIVERY_GAS_STIPEND` of 2,000,000 so delivery success is deterministic across
replicas, derived by the client from the hub's `L1MessageRecorded` and
`EncryptedL1MessageRecorded` events, nonces strictly increasing, a gap meaning an
undecryptable message consumed for good, failures retryable via `retryL1Message`.

None of it exists in the client: `L1MessageRecorded`, `SYSTEM_RELAYER` and
`relayL1Message` appear nowhere in `monad-private/category/`. The matches for
"system transaction" there are Monad's pre-existing consensus mechanism.

Guest and client agree today by both omitting it. When it lands it is an in-block
state change ahead of user transactions, so it moves the state root, the receipts
and the anchor's leaf ordering.
