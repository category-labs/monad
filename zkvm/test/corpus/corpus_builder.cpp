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
#include <zkvm/test/corpus/tx_sign.hpp>

#include <category/core/assert.h>
#include <category/core/fiber/priority_pool.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/block_hash_buffer.hpp>
#include <category/execution/ethereum/chain/ethereum_mainnet.hpp>
#include <category/execution/ethereum/core/rlp/address_rlp.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/rlp/int_rlp.hpp>
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

#include <cstring>
#include <utility>

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

    CorpusBuilder::CorpusBuilder(std::function<void(State &)> const &seed)
        : impl_{std::make_unique<Impl>()}
        , mdb_{std::make_unique<InMemoryMachine>()}
        , tdb_{mdb_}
    {
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
            .gas_limit = GAS_LIMIT,
            .timestamp = GENESIS_TIMESTAMP,
            .base_fee_per_gas = uint256_t{0}};

        test::commit_simple(
            tdb_,
            *released.state,
            released.code,
            bytes32_t{GENESIS_NUMBER},
            genesis);
        tdb_.finalize(GENESIS_NUMBER, bytes32_t{GENESIS_NUMBER});
        tdb_.set_block_and_prefix(GENESIS_NUMBER);

        auto const sealed = tdb_.read_eth_header();
        sealed_.push_back(sealed);
        block_hashes_.set(
            GENESIS_NUMBER,
            to_bytes(keccak256(rlp::encode_block_header(sealed))));
    }

    CorpusBuilder::~CorpusBuilder() = default;

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
            .gas_limit = GAS_LIMIT,
            .timestamp = parent.timestamp + BLOCK_TIME,
            .beneficiary = spec.beneficiary,
            .base_fee_per_gas = uint256_t{0}};

        // --- nonces then signatures, in that order: the nonce is inside the
        // --- signing preimage, so signing before setting it signs a lie.
        for (size_t i = 0; i < spec.txs.size(); ++i) {
            auto const sender = corpus::address_of(spec.keys[i]);
            auto const acct = tdb_.read_account(sender);
            spec.txs[i].nonce = acct.has_value() ? acct->nonce : 0;
            // A block may carry two transactions from one sender; the second
            // must see the first's nonce, which the db does not yet know.
            for (size_t j = 0; j < i; ++j) {
                if (corpus::address_of(spec.keys[j]) == sender) {
                    ++spec.txs[i].nonce;
                }
            }
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
        byte_string const block_rlp = rlp::encode_block(block);
        byte_string const witness =
            encode_execution_witness(block_rlp, wd.nodes, codes, ancestors);

        sealed_.push_back(sealed);
        block_hashes_.set(
            number, to_bytes(keccak256(rlp::encode_block_header(sealed))));
        if (sealed_.size() > BlockHashBuffer::N + 1) {
            sealed_.erase(sealed_.begin());
        }
        ++next_number_;

        return Emitted{
            .witness = witness,
            .pre_root = pre_root,
            .post_root = post_root,
            .block_hash = to_bytes(keccak256(rlp::encode_block_header(sealed))),
            .header = sealed,
            .receipts = std::move(receipts)};
    }
}

MONAD_NAMESPACE_END
