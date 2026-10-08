// Copyright (C) 2026 Category Labs, Inc.
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.

#include <zkvm/test/corpus/corpus_builder.hpp>
#include <zkvm/test/corpus/genesis_bulk.hpp>
#include <zkvm/test/corpus/spoke_code.hpp>
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/chain_hash.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
#include <category/execution/ethereum/core/rlp/transaction_rlp.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/db/witness_generator.hpp>
#include <category/execution/ethereum/execute_block.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/rlp/encode2.hpp>
#include <category/execution/ethereum/rlp/execution_witness.hpp>
#include <category/execution/ethereum/sequencing_anchor.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/state_tracer.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>

#include <ankerl/unordered_dense.h>

#include <atomic>
#include <cstring>
#include <limits>
#include <optional>
#include <utility>

#ifdef MONAD_ZKVM_L2
    #include <category/execution/ethereum/db/ordered_trie.hpp>
    #include <category/execution/ethereum/domain_anchor.hpp>
    #include <category/execution/monad/chain/monad_chain.hpp>
    #include <zkvm/guest/l2_cipher.hpp>
    #include <zkvm/guest/l2_config.hpp>
    #include <zkvm/guest/l2_ecdh.hpp>
    #include <zkvm/guest/monad_l2_chain.hpp>
#endif

MONAD_NAMESPACE_BEGIN

namespace corpus
{
#ifdef MONAD_ZKVM_L2
    /// What the guest runs. A corpus built under other rules records a state
    /// no guest computes: its post-state would differ, and its witness would
    /// be missing whatever nodes the guest's rules touch and its own do not.
    using CorpusTraits = MonadTraits<L2_REVISION>;
#else
    /// Paris. Matches what EthereumMainnet's schedule gives the block numbers
    /// and timestamps this builder chooses; if one moves the other must.
    using CorpusTraits = EvmTraits<MONAD_ETH_PARIS>;
#endif

    struct CorpusBuilder::Impl
    {
        /// One thread, one fiber: recover_senders fans out over this, and a
        /// corpus generator has no reason to want more.
        fiber::PriorityPool pool{1, 1};
        vm::VM vm;
#ifdef MONAD_ZKVM_L2
        MonadL2 chain;
#else
        EthereumMainnet chain;
#endif
    };

    namespace
    {
        /// Record the oldest BLOCKHASH read so Ancestors::Reached includes
        /// every hash the guest will need, through the parent.
        class RecordingBlockHashBuffer final : public BlockHashBuffer
        {
            BlockHashBuffer const &inner_;
            /// Atomic though the pool is one fiber: get() is const, and a
            /// plain member would be a data race the day the pool is not.
            mutable std::atomic<uint64_t> oldest_{
                std::numeric_limits<uint64_t>::max()};

        public:
            explicit RecordingBlockHashBuffer(BlockHashBuffer const &inner)
                : inner_{inner}
            {
            }

            uint64_t n() const override
            {
                return inner_.n();
            }

            bytes32_t const &get(uint64_t const n) const override
            {
                uint64_t seen = oldest_.load(std::memory_order_relaxed);
                while (n < seen && !oldest_.compare_exchange_weak(
                                       seen, n, std::memory_order_relaxed)) {
                }
                return inner_.get(n);
            }

            /// The oldest block whose hash was read, if any was.
            std::optional<uint64_t> oldest() const
            {
                uint64_t const o = oldest_.load(std::memory_order_relaxed);
                if (o == std::numeric_limits<uint64_t>::max()) {
                    return std::nullopt;
                }
                return o;
            }
        };

        /// The accounts subtrie as generate_witness wants it.
        mpt::NodeCursor
        accounts_cursor(mpt::Db &mdb, TrieDb &tdb, uint64_t const number)
        {
            auto res = mdb.find(
                tdb.get_root(),
                mpt::concat(FINALIZED_NIBBLE, STATE_NIBBLE),
                number);
            MONAD_ASSERT(res.has_value());
            return res.value();
        }

        /// Collect written code plus pre-state code for every touched
        /// account. BlockState::read_code only caches in the VM, so release()
        /// omits code that was read but not written. Convert its concurrent
        /// map to the segmented_map generate_witness expects.
        ankerl::unordered_dense::segmented_map<bytes32_t, vm::SharedIntercode>
        collect_codes(Code const &written, StateDeltas const &deltas, Db &db)
        {
            ankerl::unordered_dense::
                segmented_map<bytes32_t, vm::SharedIntercode>
                    out;
            out.reserve(written.size());
            for (auto const &kv : written) {
                out.emplace(kv.first, kv.second);
            }
            for (auto const &kv : deltas) {
                auto const &before = kv.second.account.first;
                if (!before.has_value() ||
                    before.value().code_hash == NULL_HASH) {
                    continue;
                }
                if (out.contains(before.value().code_hash)) {
                    continue;
                }
                // Still the pre-state db: generate_witness runs before the
                // commit, and so does this.
                auto code = db.read_code(before.value().code_hash);
                MONAD_ASSERT(code);
                out.emplace(before.value().code_hash, std::move(code));
            }
            return out;
        }
    }

#if defined(MONAD_L2_CIPHER_ECDH_POSEIDON2)
    namespace
    {
        /// Derive a distinct ephemeral scalar per leaf for reproducible
        /// corpora. Do not reuse the operator secret as r: repeated ECDH
        /// material and context would reuse masks. This deterministic
        /// generator is test-only.
        L2Scalar ephemeral(bytes32_t const &sk, uint64_t number, size_t index)
        {
            for (uint64_t salt = 0;; ++salt) {
                byte_string buf{sk.bytes, sizeof(sk.bytes)};
                for (uint64_t const v : {number, uint64_t{index}, salt}) {
                    for (unsigned i = 0; i < 8; ++i) {
                        buf.push_back(
                            static_cast<unsigned char>(v >> (56 - 8 * i)));
                    }
                }
                auto const h = to_bytes(keccak256(buf));
                auto const r = l2_scalar_from_be(
                    std::span<unsigned char const, 32>{h.bytes, 32});
                // Astronomically unlikely, but a scalar outside [1, n-1] is
                // not a key and l2_ecdh would return nullopt rather than say
                // why. Salting again costs nothing and keeps it total.
                if (l2_scalar_is_valid(r)) {
                    return r;
                }
            }
        }
    }
#endif

    CorpusBuilder::CorpusBuilder(
        std::function<void(State &)> const &seed, bytes32_t const &sk,
        bytes32_t const &salt_secret)
        : impl_{std::make_unique<Impl>()}
        , mdb_{std::make_unique<InMemoryMachine>()}
        , tdb_{mdb_}
        , sk_{sk}
        , salt_secret_{salt_secret}
    {
        check_operator_key();
        // Genesis goes in through a State so callers write
        // create_contract/set_code/add_to_balance/set_storage rather than
        // assembling StateDeltas by hand.
        BlockState bs{tdb_, impl_->vm};
        State state{bs, Incarnation{0, 0}};
        seed(state);
#ifdef MONAD_ZKVM_L2
        // Seed a missing domain spoke so canCall can authorize execution.
        // Preserve any spoke supplied by the scenario.
        if (!state.account_exists(L2_DOMAIN_SPOKE)) {
            seed_spoke_access(state);
        }
#endif
        MONAD_ASSERT(bs.can_merge(state));
        bs.merge(state);
        auto released = std::move(bs).release();

        BlockHeader genesis{
            .difficulty = 0,
            .number = GENESIS_NUMBER,
            .gas_limit = gas_limit_,
            .timestamp = GENESIS_TIMESTAMP,
            .base_fee_per_gas = uint256_t{0}};
#ifdef MONAD_ZKVM_L2
#endif

        test::commit_simple(
            tdb_,
            *released.state,
            released.code,
            commit_id(GENESIS_NUMBER),
            genesis);
        tdb_.finalize(GENESIS_NUMBER, commit_id(GENESIS_NUMBER));
        tdb_.set_block_and_prefix(GENESIS_NUMBER);

        seal_genesis(tdb_.read_eth_header());
    }

    CorpusBuilder::CorpusBuilder(
        std::function<void(GenesisSink &)> const &seed,
        size_t const chunk_accounts, uint64_t const gas_limit,
        bytes32_t const &sk, bytes32_t const &salt_secret)
        : impl_{std::make_unique<Impl>()}
        , mdb_{std::make_unique<InMemoryMachine>()}
        , tdb_{mdb_}
        , gas_limit_{gas_limit}
        , sk_{sk}
        , salt_secret_{salt_secret}
    {
        check_operator_key();

        BlockHeader genesis{
            .difficulty = 0,
            .number = GENESIS_NUMBER,
            .gas_limit = gas_limit_,
            .timestamp = GENESIS_TIMESTAMP,
            .base_fee_per_gas = uint256_t{0}};
#ifdef MONAD_ZKVM_L2
#endif
        // The sink commits as it fills, so the header is handed over only at
        // the end -- and it is handed over already stamped, because the
        // blinder has to be in extra_data before the commit hashes it.
        GenesisSink sink{tdb_, chunk_accounts};
        seed(sink);
        seal_genesis(sink.finish(genesis));
#ifdef MONAD_ZKVM_L2
        // Bulk seeds must include their own spoke: most state is already
        // committed when seed returns, so it cannot be added to genesis here.
        auto const spoke = tdb_.read_account(L2_DOMAIN_SPOKE);
        MONAD_ASSERT_PRINTF(
            spoke.has_value() && spoke->code_hash != NULL_HASH,
            "a domain genesis needs the spoke at MONAD_ZKVM_L2_SPOKE; a bulk "
            "seed brings it (corpus::seed_spoke_access)");
#endif
    }

    CorpusBuilder::~CorpusBuilder() = default;

    void CorpusBuilder::check_operator_key() const
    {
        // Only a suite with a key has one to check: the plaintext suite binds
        // no secret, so any corpus secret makes the same leaves.
#if defined(MONAD_L2_CIPHER_ECDH_POSEIDON2)
        // Check the secret against the configured operator key once. The
        // current cipher context does not depend on the header.
        BlockHeader probe{.number = GENESIS_NUMBER};
        auto const probe_ctx = l2_cipher_context(probe);
        MONAD_ASSERT_PRINTF(
            l2_check_operator_key(
                probe_ctx,
                l2_scalar_from_be(
                    std::span<unsigned char const, 32>{sk_.bytes, 32})),
            "the corpus secret does not match the compiled "
            "MONAD_ZKVM_L2_OPERATOR_PK_X");
#endif
    }

    void CorpusBuilder::seal_genesis(BlockHeader const &sealed)
    {
        sealed_.push_back(sealed);
        block_hashes_.set(
            GENESIS_NUMBER,
            to_bytes(header_hash(rlp::encode_block_header(sealed))));
    }

    Address CorpusBuilder::next_contract_address(Address const &deployer) const
    {
        auto const acct = const_cast<TrieDb &>(tdb_).read_account(deployer);
        uint64_t const nonce = acct.has_value() ? acct->nonce : 0;
        // YP (86): the CREATE address is keccak(rlp([sender, nonce]))[12:].
        byte_string const enc = rlp::encode_list2(
            rlp::encode_address(deployer), rlp::encode_unsigned(nonce));
        auto const hash = keccak256(enc);
        Address out;
        std::memcpy(out.bytes, hash.bytes + 12, sizeof(out.bytes));
        return out;
    }

    Emitted CorpusBuilder::add_block(BlockSpec spec)
    {
        MONAD_ASSERT(spec.txs.size() == spec.keys.size());

        uint64_t const number = next_number_;
        BlockHeader const &parent = sealed_.back();

        // --- the chosen fields; the computed ones stay zero until the commit
        BlockHeader header{
            .parent_hash =
                to_bytes(header_hash(rlp::encode_block_header(parent))),
            .difficulty = 0,
            .number = number,
            .gas_limit = gas_limit_,
            .timestamp = parent.timestamp + BLOCK_TIME,
            .beneficiary = spec.beneficiary,
            .base_fee_per_gas = uint256_t{0}};
#ifdef MONAD_ZKVM_L2
        // Before anything hashes the header: the blinder is a header field, so
        // it has to be in place for the block hash to be blinded, and the
        // guest refuses a header carrying any other value.
#endif

        // Set nonces before signing: they are part of the signing preimage.
        // Derive each sender address once and count repeats in a map to avoid
        // quadratic EC multiplications on large blocks.
        ankerl::unordered_dense::map<Address, uint64_t> sent;
        for (size_t i = 0; i < spec.txs.size(); ++i) {
            auto const sender = corpus::address_of(spec.keys[i]);
            auto const acct = tdb_.read_account(sender);
            uint64_t const base = acct.has_value() ? acct->nonce : 0;
            // A block may carry two transactions from one sender; the second
            // must see the first's nonce, which the db does not yet know.
            spec.txs[i].nonce = base + sent[sender]++;
            corpus::sign_transaction(spec.txs[i], spec.keys[i]);
        }

        Block block{.header = header, .transactions = std::move(spec.txs)};

        // --- the pre-state, captured before anything mutates
        bytes32_t const pre_root = tdb_.state_root();
        auto const pre_cursor = accounts_cursor(mdb_, tdb_, number - 1);

        // --- execute, through a recorder of the block hashes it reads
        RecordingBlockHashBuffer const recorder{block_hashes_};
        BlockState block_state{tdb_, impl_->vm};
        BlockMetrics metrics;
        auto const recovered = recover_senders(block.transactions, impl_->pool);
        auto const authorities =
            recover_authorities(block.transactions, impl_->pool);
        std::vector<Address> senders(block.transactions.size());
        for (size_t i = 0; i < recovered.size(); ++i) {
            MONAD_ASSERT(recovered[i].has_value());
            senders[i] = recovered[i].value();
        }

        std::vector<std::unique_ptr<CallTracerBase>> call_tracers(
            block.transactions.size());
        std::vector<std::unique_ptr<trace::StateTracer>> state_tracers(
            block.transactions.size());
        trace::StateTracer system_call_state_tracer{std::monostate{}};
        for (size_t i = 0; i < block.transactions.size(); ++i) {
            call_tracers[i] = std::make_unique<NoopCallTracer>();
            state_tracers[i] =
                std::make_unique<trace::StateTracer>(std::monostate{});
        }

#ifdef MONAD_ZKVM_L2
        // As the node builds it for a domain block: this block's senders and
        // authorities, and no ancestry. A domain's blocks are not pending
        // blocks of the L1 chain that carries them, so the two sets that
        // decide whether a sender may dip into its reserve are empty.
        auto const senders_and_authorities =
            combine_senders_and_authorities(senders, authorities);
        ankerl::unordered_dense::segmented_set<Address> const empty_history;
        ChainContext<CorpusTraits> const chain_context{
            .grandparent_senders_and_authorities = empty_history,
            .parent_senders_and_authorities = empty_history,
            .senders_and_authorities = senders_and_authorities,
            .senders = senders,
            .authorities = authorities};
#else
        ChainContext<CorpusTraits> const chain_context{};
#endif
        auto receipts_r = execute_block<CorpusTraits>(
            impl_->chain,
            block,
            senders,
            authorities,
            block_state,
            recorder,
            impl_->pool.fiber_group(),
            metrics,
            call_tracers,
            state_tracers,
            system_call_state_tracer,
            chain_context,
            nullptr);
        MONAD_ASSERT(receipts_r.has_value());
        auto receipts = std::move(receipts_r).assume_value();

        auto released = std::move(block_state).release();

        // --- the witness, from the trie as it was BEFORE the commit
        auto const wd = generate_witness(
            mdb_,
            pre_cursor,
            number,
            *released.state,
            collect_codes(released.code, *released.state, tdb_),
            released.self_destruct_storage_reads);

        // --- commit: this is what fills the header's computed fields
        test::commit_simple(
            tdb_,
            *released.state,
            released.code,
            commit_id(number),
            header,
            receipts,
            {},
            senders,
            block.transactions);
        tdb_.finalize(number, commit_id(number));
        tdb_.set_block_and_prefix(number);

        BlockHeader const sealed = tdb_.read_eth_header();
        block.header = sealed;
        bytes32_t const post_root = tdb_.state_root();

        // Field [3]: retain sealed ancestors, contiguous and oldest first.
        // Ancestors::Reached starts at the oldest BLOCKHASH read (or just the
        // parent); Ancestors::All includes the whole available buffer.
        size_t const all = std::min<size_t>(sealed_.size(), BlockHashBuffer::N);
        size_t keep = all;
        if (ancestors_ == Ancestors::Reached) {
            auto const oldest = recorder.oldest();
            keep = oldest.has_value() ? number - *oldest : 1;
            MONAD_ASSERT(keep >= 1 && keep <= all);
        }
        MONAD_ASSERT(sealed_[sealed_.size() - keep].number + keep == number);
        std::vector<byte_string> ancestors;
        for (size_t i = sealed_.size() - keep; i < sealed_.size(); ++i) {
#ifdef MONAD_ZKVM_L2
            // Hashes, not headers: BLOCKHASH wants the hash, and nothing on
            // this arm walks the headers for continuity any more.
            auto const h =
                to_bytes(header_hash(rlp::encode_block_header(sealed_[i])));
            ancestors.emplace_back(h.bytes, sizeof(h.bytes));
#else
            ancestors.push_back(rlp::encode_block_header(sealed_[i]));
#endif
        }
        MONAD_ASSERT(!ancestors.empty());
        MONAD_ASSERT(sealed_.back().state_root == pre_root);

        std::vector<byte_string> codes{wd.codes.begin(), wd.codes.end()};

        // Derive the expected anchor independently from host receipts. Host
        // execute_block clears pending storage but returns no anchor.
        bytes32_t anchor{};
#ifdef MONAD_ZKVM_L2
        {
            auto messages = collect_domain_messages(receipts, L2_DOMAIN_SPOKE);
            MONAD_ASSERT(messages.has_value());
            anchor = sorted_pair_merkle_root(messages.value());
        }
#endif

        BlockHeader published = sealed;
        byte_string block_rlp;
        byte_string witness;
        size_t encrypted = 0;

#ifdef MONAD_ZKVM_L2
        // Encrypt accepted transaction encodings for the domain body.
        // Execution-derived roots and receipts do not depend on encryption.
        std::vector<byte_string> leaves;
        leaves.reserve(block.transactions.size());
        for (size_t i = 0; i < block.transactions.size(); ++i) {
            // The trie form, which is what the guest decrypts back to: a
            // legacy transaction is its own RLP list, a typed one is the bare
            // type byte and payload with no string wrapper.
            byte_string const plain =
                rlp::encode_transaction(block.transactions[i]);
    #if defined(MONAD_L2_CIPHER_PLAINTEXT)
            // The control: the leaf is the transaction.
            leaves.emplace_back(plain);
    #else
            auto const ctx = l2_cipher_context(sealed);
            auto const r = ephemeral(sk_, number, i);
            unsigned char nonce[16] = {};
            for (unsigned b = 0; b < 8; ++b) {
                nonce[b] = static_cast<unsigned char>(i >> (8 * b));
            }
            std::vector<unsigned char> leaf;
            MONAD_ASSERT(l2_encrypt_leaf(
                ctx,
                r,
                std::span<unsigned char const, 16>{nonce},
                std::span<unsigned char const>{plain.data(), plain.size()},
                leaf));
            leaves.emplace_back(leaf.begin(), leaf.end());
    #endif
            ++encrypted;
        }
        published.transactions_root = ordered_trie_root(leaves);

        {
            // [ L1 header, [ciphertext...], [outer gas limit...], parent ].
            // Not a block: a domain has none. See domain_body.hpp.
            byte_string cts;
            for (auto const &leaf : leaves) {
                cts += rlp::encode_string2(leaf);
            }
            // No real L1 envelopes in the corpus: sponsor exactly the inner
            // gas limit to exercise the acceptance boundary (`==` passes, `>`
            // drops).
            byte_string limits;
            for (auto const &tx : block.transactions) {
                limits += rlp::encode_unsigned(tx.gas_limit);
            }
            byte_string body = rlp::encode_block_header(published);
            body += rlp::encode_list2(cts);
            body += rlp::encode_list2(limits);
            body += rlp::encode_unsigned(number - 1);
            block_rlp = rlp::encode_list2(body);
        }

        witness = encode_execution_witness_l2(
            block_rlp,
            wd.nodes,
            codes,
            ancestors,
            byte_string_view{sk_.bytes, sizeof(sk_.bytes)},
            byte_string_view{salt_secret_.bytes, sizeof(salt_secret_.bytes)});
#else
        block_rlp = rlp::encode_block(block);
        witness =
            encode_execution_witness(block_rlp, wd.nodes, codes, ancestors);
#endif

        // The sealed header is what the NEXT block's parent_hash and the
        // ancestor list must name, and on an L2 block that is the published
        // header -- the one whose transactions_root covers the ciphertexts.
        sealed_.push_back(published);
        block_hashes_.set(
            number, to_bytes(header_hash(rlp::encode_block_header(published))));
        if (sealed_.size() > BlockHashBuffer::N + 1) {
            sealed_.erase(sealed_.begin());
        }
        ++next_number_;

        return Emitted{
            .witness = witness,
            .pre_root = pre_root,
            .post_root = post_root,
            .block_hash =
                to_bytes(header_hash(rlp::encode_block_header(published))),
            .header = published,
            .receipts = std::move(receipts),
            .domain_anchor = anchor,
            .parent_hash = published.parent_hash,
            .encrypted_leaves = encrypted,
#ifdef MONAD_ZKVM_L2
            // Blinded with the parent's number, which is what the previous
            // block published as its own final state: the two have to be the
            // same bytes for the hub's chaining to be one equality.
            .pre_state_commitment = l2_state_commitment(
                std::span<unsigned char const, 32>{salt_secret_.bytes, 32},
                number - 1,
                pre_root),
            .state_commitment = l2_state_commitment(
                std::span<unsigned char const, 32>{salt_secret_.bytes, 32},
                number,
                post_root),
            .sequencing_anchor =
                [&] {
                    std::vector<byte_string_view> views;
                    views.reserve(leaves.size());
                    for (auto const &leaf : leaves) {
                        views.emplace_back(leaf);
                    }
                    return monad::sequencing_anchor(L2_CHAIN_ID, number, views);
                }(),
#endif
        };
    }
}

MONAD_NAMESPACE_END
