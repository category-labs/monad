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
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/assert.h>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
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

#include <cstring>
#include <utility>

#ifdef MONAD_ZKVM_L2
    #include <category/execution/ethereum/namespace_anchor.hpp>
    #include <zkvm/guest/body_roots.hpp>
    #include <zkvm/guest/l2_cipher.hpp>
    #include <zkvm/guest/l2_config.hpp>
    #include <zkvm/guest/l2_ecdh.hpp>
#endif

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    /// Paris. Matches what EthereumMainnet's schedule gives the block numbers
    /// and timestamps this builder chooses; if one moves the other must.
    using CorpusTraits = EvmTraits<MONAD_ETH_PARIS>;

    struct CorpusBuilder::Impl
    {
        /// One thread, one fiber: recover_senders fans out over this, and a
        /// corpus generator has no reason to want more.
        fiber::PriorityPool pool{1, 1};
        vm::VM vm;
        EthereumMainnet chain;
    };

    namespace
    {
#ifdef MONAD_ZKVM_L2
        /// The blinder goes in extra_data, whose 32-byte cap is exactly its
        /// width (block_rlp.cpp enforces EXTRA_DATA_MAX_LENGTH).
        void set_salt(BlockHeader &h, bytes32_t const &salt)
        {
            h.extra_data.assign(salt.bytes, sizeof(salt.bytes));
        }
#endif

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

        /// The codes the guest will need, which is NOT what release() hands
        /// back.
        ///
        /// BlockState::read_code caches into the VM and into nothing else, so
        /// `code_` collects the codes a block WROTE and never the ones it
        /// merely ran. Ship only those and the guest aborts inside
        /// read_code on a zero-length result -- a failure that names the code
        /// hash and nothing about where it should have come from.
        ///
        /// So: the written codes, plus the pre-state code of every account
        /// the block touched. Slightly over-inclusive (a touched account whose
        /// code never runs ships anyway) and exactly bounded by the witness's
        /// own access set, which is the set the guest can reach at all.
        ///
        /// Also a type change: release() gives a Code
        /// (tbb::concurrent_hash_map), generate_witness wants a segmented_map.
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

#ifdef MONAD_ZKVM_L2
    namespace
    {
        /// A fresh ephemeral scalar per leaf, derived so a regenerated corpus
        /// is byte-identical.
        ///
        /// Fresh, and not the operator secret. The rewriter this replaces
        /// passed sk as r, which makes R = pk on every leaf and P = sk^2 G a
        /// constant -- so two blocks in one epoch share a keystream for the
        /// same leaf index and plaintext length. That is a break, not an
        /// inefficiency: XORing two such leaves cancels the mask.
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
        set_salt(genesis, block_salt(genesis.number));
#endif

        test::commit_simple(
            tdb_,
            *released.state,
            released.code,
            bytes32_t{GENESIS_NUMBER},
            genesis);
        tdb_.finalize(GENESIS_NUMBER, bytes32_t{GENESIS_NUMBER});
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
        set_salt(genesis, block_salt(genesis.number));
#endif
        // The sink commits as it fills, so the header is handed over only at
        // the end -- and it is handed over already stamped, because the
        // blinder has to be in extra_data before the commit hashes it.
        GenesisSink sink{tdb_, chunk_accounts};
        seed(sink);
        seal_genesis(sink.finish(genesis));
    }

    CorpusBuilder::~CorpusBuilder() = default;

    void CorpusBuilder::check_operator_key() const
    {
#ifdef MONAD_ZKVM_L2
        // Checked once, against a throwaway header: the context's key
        // material does not depend on the block, only its epoch does, and a
        // secret that does not match the compiled operator key can never
        // produce a leaf this guest will decrypt.
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
            to_bytes(keccak256(rlp::encode_block_header(sealed))));
    }

    bytes32_t
    CorpusBuilder::block_salt([[maybe_unused]] uint64_t const number) const
    {
#ifdef MONAD_ZKVM_L2
        return l2_state_salt(
            std::span<unsigned char const, 32>{salt_secret_.bytes, 32}, number);
#else
        return bytes32_t{};
#endif
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
                to_bytes(keccak256(rlp::encode_block_header(parent))),
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
        set_salt(header, block_salt(number));
#endif

        // --- nonces then signatures, in that order: the nonce is inside the
        // --- signing preimage, so signing before setting it signs a lie.
        //
        // address_of is an EC multiplication, so each key becomes an address
        // exactly once and the same-sender count comes from a map. Scanning
        // the earlier transactions instead, re-deriving each of their
        // addresses, is quadratic in a multiplication: 12.5M of them on a
        // 5000-transaction block, which a payouts corpus reaches on every
        // block.
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

        // --- execute
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

        ChainContext<CorpusTraits> const chain_context{};
        auto receipts_r = execute_block<CorpusTraits>(
            impl_->chain,
            block,
            senders,
            authorities,
            block_state,
            block_hashes_,
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
            bytes32_t{number},
            header,
            receipts,
            {},
            senders,
            block.transactions);
        tdb_.finalize(number, bytes32_t{number});
        tdb_.set_block_and_prefix(number);

        BlockHeader const sealed = tdb_.read_eth_header();
        block.header = sealed;
        bytes32_t const post_root = tdb_.state_root();

        // --- field [3]: ascending, contiguous, ending at the parent, and the
        // --- newest carrying the pre-state root the blob was built against.
        // --- Taken from what the commit sealed, never rebuilt.
        std::vector<byte_string> ancestors;
        size_t const keep =
            std::min<size_t>(sealed_.size(), BlockHashBuffer::N);
        for (size_t i = sealed_.size() - keep; i < sealed_.size(); ++i) {
            ancestors.push_back(rlp::encode_block_header(sealed_[i]));
        }
        MONAD_ASSERT(!ancestors.empty());
        MONAD_ASSERT(sealed_.back().state_root == pre_root);

        std::vector<byte_string> codes{wd.codes.begin(), wd.codes.end()};

        // The anchor the L2 guest will publish. Recomputed here from the same
        // receipts rather than read back from execution: execute_block has
        // nowhere to return it (it yields receipts), so the host clears the
        // pending array and drops the value. Deliberate asymmetry -- the node
        // wants the root, the prover publishes the anchor -- and it means the
        // two are derived independently, which is what makes comparing them
        // worth anything.
        bytes32_t anchor{};
#ifdef MONAD_ZKVM_L2
        {
            auto messages =
                collect_namespace_messages(receipts, L2_NAMESPACE_SPOKE);
            MONAD_ASSERT(messages.has_value());
            anchor = sorted_pair_merkle_root(messages.value());
        }
#endif

        BlockHeader published = sealed;
        byte_string block_rlp;
        byte_string witness;
        size_t encrypted = 0;

#ifdef MONAD_ZKVM_L2
        // Encrypt the leaves and re-root the transactions trie over the
        // ciphertexts, which is what the header commits to on this chain.
        // commit_simple has already filled transactions_root from the
        // plaintext trie, so it is overwritten here and nowhere else -- every
        // other computed field (state_root, receipts_root, gas_used,
        // logs_bloom) is the same either way, because the cipher does not
        // change what executing the block does.
        std::vector<byte_string> leaves;
        leaves.reserve(block.transactions.size());
        for (size_t i = 0; i < block.transactions.size(); ++i) {
            // The trie form, which is what the guest decrypts back to: a
            // legacy transaction is its own RLP list, a typed one is the bare
            // type byte and payload with no string wrapper.
            byte_string const plain =
                rlp::encode_transaction(block.transactions[i]);
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
            ++encrypted;
        }
        published.transactions_root = ordered_trie_root(leaves);

        {
            byte_string txs;
            for (auto const &leaf : leaves) {
                txs += rlp::encode_string2(leaf);
            }
            byte_string body = rlp::encode_block_header(published);
            body += rlp::encode_list2(txs);
            body += rlp::encode_list2(byte_string{}); // no ommers, ever
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
            number, to_bytes(keccak256(rlp::encode_block_header(published))));
        if (sealed_.size() > BlockHashBuffer::N + 1) {
            sealed_.erase(sealed_.begin());
        }
        ++next_number_;

        return Emitted{
            .witness = witness,
            .pre_root = pre_root,
            .post_root = post_root,
            .block_hash =
                to_bytes(keccak256(rlp::encode_block_header(published))),
            .header = published,
            .receipts = std::move(receipts),
            .namespace_anchor = anchor,
            .parent_hash = published.parent_hash,
            .encrypted_leaves = encrypted};
    }
}

MONAD_NAMESPACE_END
