# Decisions the specification does not make

Where the protocol leaves a question open, this file records what this guest
chose and why. Only that: a behaviour the client or the contracts already fix is
not a decision, it is conformance, and those live in
[CONFORMANCE.md](CONFORMANCE.md).

The test for an entry here is that someone could reasonably have chosen
otherwise. So each one says what the specification leaves undetermined, what was
chosen, and what that rules out — the alternatives being the part that gets lost,
after which the decision either gets relitigated every six months or becomes
untouchable, both bad.

The two sources this is read against are
[`monad-domains`](https://github.com/category-labs/monad-domains) for the L1 and
[`monad-private@domains`](https://github.com/category-labs/monad-private/tree/domains)
for the execution client.

Choices we deliberately did *not* make are at the end, under
[Left open](#left-open). They are not oversights; they are questions we do not
own.

---

## 1. A sequencing anchor binds the input set

**What is undetermined.** Nothing in the protocol binds a state transition to the
transactions it was computed from. The hub stores a root and an anchor; neither
says which ciphertexts produced them. With a validator quorum the gap is covered
socially — independent replicas read the same L1 calldata and will not sign a
root obtained from a different set. A single proof replacing that quorum removes
the cover, and a prover that executes a subset, or a permutation, produces a root
that is perfectly valid for *that* computation and that the hub cannot
distinguish. An ordinary chain gets this free from the block hash covering
`transactions_root`; this chain has no domain block header.

**Chosen.** The guest publishes a fifth value, a digest over every ciphertext the
L1 sequenced for this domain at this block, in L1 order, before any drop rule is
applied:

```
anchor = keccak256("monad-domain/sequencing-anchor/v1" ‖ chainId_be64 ‖ number_be64
                   ‖ keccak256(ct_1) ‖ … ‖ keccak256(ct_n))
```

Implemented in [`sequencing_anchor.hpp`](../category/execution/ethereum/sequencing_anchor.hpp),
beside the message anchor and for its reason: the rule has to match what the L1
computes bit for bit, and the guest, the corpus generator and eventually the node
all need it.

Four sub-choices, each of which could have gone the other way:

**Over ciphertexts, not decrypted transactions.** The hub never sees plaintext, so
a digest over decrypted transactions is checkable only by someone already holding
the viewing key — which binds nothing from the L1's point of view.

**Over the sequenced set, not the executed set.** The drop rules are exactly where
a dishonest prover would cheat, so a digest taken after them lets the prover
certify its own choices. The input is committed as handed over; the rules are then
applied deterministically inside the proof. The statement becomes "here is the
input I was given, here is the root after applying the protocol's rules" rather
than "here is what I decided to run".

**keccak256, not Poseidon2**, against the grain of every other hash in this tree,
because the verifier is the EVM — see 4. The cost moves the other way in the
circuit and is small: a block's ciphertexts are a few kilobytes, so a few dozen
keccak-f permutations, negligible beside execution.

**One sponge, not a hash chained one leaf at a time.** Measured rather than
asserted: the two differ by `1 - 32/136` = **0.765 keccak permutations per
sequenced transaction**, the chained form paying a whole 64-byte permutation per
leaf where this one absorbs 32 bytes into a sponge already running. Everything
else cancels, since both hash each leaf once. For a 250-transaction block that is
about 191 permutations.

Under the Keccakf precompile that difference is *free*: a block of 1 to 250
transactions runs a hundred to nine thousand permutations and ZisK proves a whole
14,462-permutation instance either way, so the plan is identical. Under
`MONAD_ZKVM_KECCAKF_SOFTWARE` a permutation is 4,138 steps and it is not free,
and that is what decided it.

The cost of deciding it this way is recorded under
[How the hub obtains the input set](#how-the-hub-obtains-the-input-set): the EVM's
`keccak256` is all-or-nothing over a memory range, so this form cannot be
maintained incrementally by an L1 accumulator, and the hub must hold every leaf
hash at once.

Each leaf is still hashed before being absorbed, which is orthogonal and not
negotiable: it keeps every element a fixed 32 bytes and removes the splitting
ambiguity a raw concatenation of variable-length leaves carries, where `ab`,`c`
and `a`,`bc` hash alike.

The preamble binds the domain and the number, so a digest cannot replay across
domains or across blocks of one domain. A block that sequenced nothing anchors to
the preamble alone rather than to zero, which keeps "nothing at this height" a
statement the proof makes rather than a value indistinguishable from an unset
field.

**Rules out.** Poseidon2 here; a digest over the executed set; a chained digest,
and with it the incremental L1 accumulator below.

**Narrows** [How the hub obtains the input set](#how-the-hub-obtains-the-input-set),
which is otherwise open.

---

## 2. The state commitment is blinded

**What is undetermined.** The contracts and the client assume `newStateRoot` is a
state root in the clear, and nothing says the domain's state should be private.
But nothing says it should be public either: no contract opens the value, and the
confidentiality the rest of the design buys — HPKE on every payload, a viewing key
held only by replicas — is defeated at the last step if the root is published
plainly.

**Chosen.** Publish `H(salt(domainChainId, number) ‖ state_root)`, the blinder
secret a private witness input checked against a registered commitment.

The state is enumerable from public data — participants registered on the L1,
deposits public L1 transfers, ciphertexts sequenced through the L1 — and a
commitment to a guessable value confirms guesses. Preimage resistance is no
defence; nothing is being inverted.

The domain id belongs in the salt label because the client does not enforce that
each domain has a distinct viewing key, so two domains sharing a secret would
otherwise derive the same salt at the same height.

**What it does not buy.** The message anchor stays in the clear and cannot be
blinded — the L1 opens it to release withdrawals. The blinder protects the
**state**, not the **messages**.

Implemented as `l2_state_commitment` in [`l2_config.hpp`](guest/l2_config.hpp)
and published in place of any root; the blinder no longer rides in the header's
`extra_data`, because with no block hash published there is nothing there for it
to protect. The output's seven values and their offsets are in the README's
[public output](README.md#the-public-output) section — 177 bytes of ZisK's 256 —
and dropping the block hash also dropped the sealing, so the L2 arm no longer
encodes and hashes a header it would not publish.

**Rules out.** Publishing the raw root, which is what both other repos assume.

**Costs elsewhere.** No contract change: `newStateRoot` is written to
`_commitments`, read back by `readCommitment`, and never opened — not by a merkle
proof, not by the bridge, which works off `domainAnchors`. Checked across the
whole of `monad-domains`. The execution client does need a change: it compares the
raw root today.

---

## 3. The block number is the L1 block number

**What is undetermined.** The two sources disagree. The client writes the L1 block
number into the synthetic domain header; the reference end-to-end submits
`committedBn + 1`, a counter of its own.

**Chosen.** The L1 block number, following the client.

It is the only one of the two that something recomputes, and it makes the
sequence a function of the L1 rather than of submission history. The sequence is
then sparse — an L1 block that sequences nothing for a domain produces no domain
block — which the hub's rule accommodates, since it requires strictly increasing
numbers and not contiguous ones.

**Rules out.** A domain-local height, and with it any reading where domain blocks
are counted rather than derived.

---

## 4. What the L1 recomputes stays keccak256

**What is undetermined.** The protocol names no hash but keccak256, because it has
no reason to consider another. Every Poseidon2 substitution in this tree is
therefore ours, and nothing external says where the boundary falls.

**Chosen.** A hash may be Poseidon2 only if this chain is the only thing that
computes it. Anything the EVM, a contract or the L1 hub recomputes stays
keccak256: the `KECCAK256` opcode, code hashes, `CREATE`/`CREATE2` addresses,
transaction hashes, the message anchor, and the sequencing anchor of 1.

The rule exists because the alternative is deciding it case by case, and the case
that gets decided wrong is the one where a cheap in-circuit hash turns into
thousands of gas per permutation in Solidity, paid on the L1 at every transition.

**Rules out.** Poseidon2 for anything the L1 opens. It also makes
`MONAD_ZKVM_L2_TRIE_HASH=poseidon2` and `SIGNATURE_HASH=poseidon2` measurement
arms rather than deployable configurations — the client requires keccak signatures
and keccak-keyed tries — which is recorded in CONFORMANCE.md because the reason is
the client's, not ours.

---

## 5. Rotatable values are public inputs, not compiled constants

**What is undetermined.** The protocol says where the viewing key lives
operationally — a PEM per domain, rotation an operational matter — but says
nothing about where a *prover* gets it, because it has no prover.

**Chosen.** The viewing public key and the blinder commitment are public inputs,
checked by the hub against what is registered for the domain. Per-domain values
that never rotate may stay compiled, which means an ELF per domain.

A compiled key makes rotation a rebuild, and a rebuild changes the verification
key — so every rotation would invalidate the hub's registration of the prover. The
binding cannot simply be dropped either: without the check that the supplied
secret matches the domain's published key, a prover supplies any secret, decrypts
to a different set of transactions, and proves a valid post-state for a block
nobody wrote.

The guest publishes both at the end of its output. What does not exist is the
other half: the hub comparing them against a registration.

**Rules out.** Compiling either value in, and dropping the binding.

**Costs elsewhere.** `registerDomain` has no field for either. That is the same
contract change a proof mode needs, so they travel together.

---

## 6. Where the client and the written specification disagree, the client wins

**What is undetermined.** They disagree in at least three places — the derivation
source for domain blocks, the block number, and whether reverted sequencing calls
count — and nothing arbitrates.

**Chosen.** Match the client's behaviour, and record the disagreement rather than
resolving it silently.

A proof that faithfully attests the wrong definition is indistinguishable from a
correct one: it verifies, the root is self-consistent, and it corresponds to
nothing any replica would compute. The client is what every replica runs, so it is
the only definition a disagreement can be detected against.

**Rules out.** Implementing from the contracts' documentation where the two differ.
Each instance is listed in CONFORMANCE.md.

---

## 7. The public inputs are the transition, both ends of it

**What is undetermined.** `stateTransitionDigest` names one root, the new one.
A validator signing it is trusted to have started from the right state; nothing
in the digest says which. A proof replacing that validator inherits the gap: it
can attest a perfectly valid transition out of a state the hub never accepted,
and the hub cannot tell.

**Chosen.** Publish both ends, around the inputs that join them:

```
pre-state commitment │ sequencing anchor │ post-state commitment
```

The pre-state commitment is blinded with the **parent's** number, so it is byte
for byte what that block's own run published as its final state. The hub's
check is then one equality against what it already holds, with no derivation of
its own and no second secret.

This is also what makes the continuity safe to drop from the circuit. Today the
guest ties its pre-state root to an ancestor header the prover also supplied,
which is internal consistency and not a link to anything the hub accepted; once
the hub compares the published commitment, that walk is no longer carrying the
argument -- which matters, because reshaping the witness removes the ancestor
headers it walks.

**Rules out.** Publishing only the final state, and with it any reading where
the hub trusts the prover's choice of starting point.

---

# Left open

Not oversights. Questions we do not own, recorded so the decisions above can be
read against them.

## What authorises the L1 inputs the prover supplies

Reshaping the witness made this one sharper, and it should not be discovered
later. The guest is handed the L1 header it executes against -- number,
timestamp, beneficiary, prev_randao, gas_limit, base_fee_per_gas -- and a run of
ancestor hashes that `BLOCKHASH` is served from. **Nothing published commits to
any of them.** The sequencing anchor binds the ciphertexts and only those.

Before the reshape the ancestor run was self-chaining: each header named the one
before it and the newest hashed to the block's own parent hash, so a prover had
to supply a consistent run even if nothing tied it to the real L1. The run is
now a positional list of hashes, so even that is gone -- a short or gapped run
shifts every entry to a height that is not its own, silently, and any hash at
all can be returned from `BLOCKHASH`.

The fix is cheap whenever it is wanted, and it is worth writing down now: absorb
`keccak256(header_rlp)` and the ancestor hashes into the sequencing anchor's
preamble. The hub holds all of them already -- it *is* the L1 -- so it costs one
more comparison there and a few permutations here, and it closes the header and
the ancestors in the same value that already closes the inputs.

Not done, because it widens what decision 1 settled and that is worth doing
deliberately rather than in passing.

## How the hub obtains the input set

Decision 1 fixes what the guest publishes, not what the hub compares it to — and
having taken the single-sponge form, it rules one of the two answers out.

**A running keccak in storage**, updated in `sequenceToDomain`, is no longer
available. The EVM's `keccak256` is all-or-nothing over a memory range, so the
hub cannot absorb one leaf per call and carry the sponge state between
transactions. Choosing it would mean going back to a chained digest and paying
0.765 permutations per transaction in the circuit.

**The L1 block hash published by the proof**, compared against `blockhash(N)`,
is therefore the live option: no L1 cost, but the guest must verify an L1 header
and its transactions root, and `blockhash` reaches back only 256 blocks — on a
fast L1 a window of minutes, inside which the proof must be produced *and*
submitted or the transition becomes unverifiable.

**The operator supplies the leaf list as calldata** and the hub hashes it, which
is cheap but only moves the question: something still has to establish that the
list is complete, and nothing in the hub does.

So this is the decision that is genuinely still open, and decision 1 has made it
narrower rather than easier. If the time window proves unworkable, the way back
is to revisit decision 1's last sub-choice, not to patch around it here.

**Settled for the guest's purposes: the list is supplied raw.** The guest does
not verify an L1 block -- it is handed the payloads and executes them -- so the
witness carries only this domain's. That is what made the witness reshape
possible. It is not an answer to how the hub comes to hold its own half, which
is still open.

## Do reverted sequencing calls count?

The hub documents its own event as the derivation source — "Domain validators
derive their blocks from these events". The client derives from the calldata of
outer transactions **including reverted ones**, deliberately and documented twice.
A reverted call emits no log, so the two give different transaction sets.

This is upstream of the drop rules: it decides not just how inputs are bound but
which transactions compose the block. Decision 6 says follow the client, but that
is a stopgap over a contradiction somebody has to resolve.

## Which `stateVerificationMode` means "proof"

`MAX_STATE_VERIFICATION_MODE = 2`, so three modes are reserved. The value is
stored in `DomainConfig` and emitted in `DomainRegistered`, and never branched on
anywhere; both the deploy script and the setup tool pass `0`. No verification key
is registered per domain and `submitStateSignature` takes no proof argument.

The reference end-to-end signs `newStateRoot = zeroHash`, commented "demo value;
bridging only consumes the anchor". The state-commitment half of the protocol is a
placeholder — only the anchor and bridging path is exercised end to end. Decisions
1, 2 and 5 are therefore inputs to a design not yet written, rather than
constraints to conform to, and should be put to whoever owns `monad-domains` as
proposals.
