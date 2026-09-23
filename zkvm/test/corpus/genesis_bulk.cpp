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

#include <category/core/assert.h>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/db/test/commit_simple.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/vm/code.hpp>

#include <utility>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    struct GenesisSink::Impl
    {
        TrieDb &tdb;
        size_t const chunk;
        StateDeltas deltas{};
        Code code{};
        size_t pending{0};
        size_t chunk_index{0};
        size_t total_accounts{0};
        size_t total_slots{0};
        bool finished{false};

        /// Commit `deltas` under `header` and start a fresh chunk. The block
        /// id is the height, which is what the other constructor uses for
        /// genesis and which keeps every chunk's id distinct.
        void commit(BlockHeader const &header)
        {
            auto const id = bytes32_t{header.number};
            test::commit_simple(tdb, deltas, code, id, header);
            tdb.finalize(header.number, id);
            tdb.set_block_and_prefix(header.number);
            deltas.clear();
            code.clear();
            pending = 0;
        }

        /// Flush a full chunk at its own pre-genesis height. These headers are
        /// never published, never enter the sealed chain and never reach a
        /// witness, so they carry no state blinder and nothing validates them
        /// -- but their timestamps still ascend and still sit under Shanghai,
        /// because a header trie full of nonsense is a trap for whoever reads
        /// it next.
        void flush_chunk()
        {
            MONAD_ASSERT_PRINTF(
                chunk_index < MAX_GENESIS_CHUNKS,
                "genesis seeding wants more than %zu chunks: raise "
                "chunk_accounts, or MAX_GENESIS_CHUNKS and with it the "
                "pre-genesis span",
                MAX_GENESIS_CHUNKS);
            uint64_t const remaining = MAX_GENESIS_CHUNKS - chunk_index;
            commit(BlockHeader{
                .difficulty = 0,
                .number = GENESIS_NUMBER - remaining,
                .gas_limit = GAS_LIMIT,
                .timestamp = GENESIS_TIMESTAMP - remaining * BLOCK_TIME,
                .base_fee_per_gas = uint256_t{0}});
            ++chunk_index;
        }
    };

    GenesisSink::GenesisSink(TrieDb &tdb, size_t const chunk_accounts)
        : impl_{
              std::make_unique<Impl>(Impl{.tdb = tdb, .chunk = chunk_accounts})}
    {
        MONAD_ASSERT(chunk_accounts > 0);
    }

    GenesisSink::~GenesisSink() = default;

    void GenesisSink::account(Address const &addr, Account const &acct)
    {
        MONAD_ASSERT(!impl_->finished);
        // Only here, so an account and the storage and code written after it
        // always land in the same chunk.
        if (impl_->pending == impl_->chunk) {
            impl_->flush_chunk();
        }
        // TBB's emplace returns a plain bool, not the pair std::unordered_map
        // hands back.
        bool const inserted = impl_->deltas.emplace(
            addr, StateDelta{.account = {std::nullopt, acct}});
        MONAD_ASSERT_PRINTF(
            inserted,
            "genesis seeding submitted the same account twice in one chunk");
        ++impl_->pending;
        ++impl_->total_accounts;
    }

    void GenesisSink::contract(
        Address const &addr, Account acct, byte_string_view const code)
    {
        acct.code_hash = to_bytes(keccak256(code));
        account(addr, acct);
        impl_->code.emplace(acct.code_hash, vm::make_shared_intercode(code));
    }

    void GenesisSink::storage(
        Address const &addr, bytes32_t const &slot, bytes32_t const &value)
    {
        MONAD_ASSERT(!impl_->finished);
        // An absent slot and a zero slot are the same state. Passing a zero
        // down as a delta would encode an erase of something that was never
        // there.
        if (value == bytes32_t{}) {
            return;
        }
        StateDeltas::accessor acc;
        MONAD_ASSERT_PRINTF(
            impl_->deltas.find(acc, addr),
            "genesis seeding wrote a slot for an account that is not in the "
            "current chunk: write an account, then its storage");
        acc->second.storage.emplace(slot, StorageDelta{bytes32_t{}, value});
        ++impl_->total_slots;
    }

    BlockHeader GenesisSink::finish(BlockHeader genesis)
    {
        MONAD_ASSERT(!impl_->finished);
        MONAD_ASSERT(genesis.number == GENESIS_NUMBER);
        impl_->commit(genesis);
        impl_->finished = true;
        return impl_->tdb.read_eth_header();
    }

    size_t GenesisSink::accounts() const
    {
        return impl_->total_accounts;
    }

    size_t GenesisSink::slots() const
    {
        return impl_->total_slots;
    }

    size_t GenesisSink::chunks_flushed() const
    {
        return impl_->chunk_index;
    }
}

MONAD_NAMESPACE_END
