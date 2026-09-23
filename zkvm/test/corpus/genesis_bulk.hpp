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

#pragma once

// Seeding a genesis state at benchmark scale.
//
// The obvious route -- drive a `State`, merge, release, commit -- is the one
// CorpusBuilder's other constructor takes, and it is the right one for the
// twenty accounts a scenario needs. It does not survive a million:
// State::set_storage (state3/state.cpp) probes two linear-scan containers per
// call, and FlatStorage::find (state3/account_state.hpp) is a scan in a host
// build -- the open-addressed index that would make it O(1) is compiled only
// under MONAD_ZKVM_ZISK, i.e. only for the guest. So the cost is quadratic in
// the slots already on an account, and a million of them measured at 64
// minutes.
//
// This builds the StateDeltas directly instead, which is what
// load_genesis_state (chain/genesis_state.cpp) already does, and hands them to
// test::commit_simple. No State, no scan. The trie was never the problem:
// mpt::Db takes a million leaves in one upsert (mpt/test/db_test.cpp,
// TYPED_TEST(DbTest, scalability)).

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>

#include <cstddef>
#include <cstdint>
#include <memory>

MONAD_NAMESPACE_BEGIN

namespace corpus
{
    /// How many pre-genesis heights the sink may spend on chunks. Chunk `i`
    /// commits at GENESIS_NUMBER - MAX_CHUNKS + i, so the run stays strictly
    /// below the genesis height and leaves the sealed-header chain and the
    /// block hash buffer -- both of which start at GENESIS_NUMBER -- untouched.
    inline constexpr size_t MAX_GENESIS_CHUNKS = 1024;

    /// Accumulates a genesis state and commits it in chunks.
    ///
    /// Chunking is not an optimisation. sizeof(StateDelta) == 752 (a static
    /// assertion in state2/state_deltas.hpp: each one embeds a 576-byte TBB
    /// map, empty or not), so a million accounts would be 752 MB of deltas
    /// before a single trie node exists. A chunk bounds that.
    ///
    /// Call order matters in one place: `storage` and `code` apply to an
    /// account already submitted in the CURRENT chunk, and a chunk is flushed
    /// only at the start of an `account` call. So write an account and then
    /// everything that belongs to it, and a chunk boundary can never fall
    /// between the two. Reaching for an account from an earlier chunk aborts
    /// rather than silently dropping the write.
    class GenesisSink
    {
    public:
        GenesisSink(TrieDb &, size_t chunk_accounts);
        ~GenesisSink();

        GenesisSink(GenesisSink const &) = delete;
        GenesisSink &operator=(GenesisSink const &) = delete;

        /// An externally owned account, or the account record of a contract
        /// whose code_hash the caller has already set.
        void account(Address const &, Account const &);

        /// An account plus its code, hashing the code and filling code_hash.
        void contract(Address const &, Account, byte_string_view code);

        /// One storage slot of an account submitted in this chunk. A zero
        /// value is dropped: an absent slot and a zero slot are the same
        /// state, and passing one down as a delta would be an erase.
        void
        storage(Address const &, bytes32_t const &slot, bytes32_t const &value);

        /// Commit whatever is pending as the genesis block itself, under the
        /// header given -- which the caller has already stamped (the L2 arm
        /// puts the state blinder in extra_data before anything hashes it).
        /// Returns the header as the commit sealed it, with the computed
        /// fields filled. A state small enough for one chunk therefore takes
        /// exactly one commit, at GENESIS_NUMBER, which is what makes it
        /// comparable to the State route.
        BlockHeader finish(BlockHeader genesis);

        /// Accounts submitted so far, across every chunk.
        size_t accounts() const;
        /// Storage slots submitted so far, across every chunk.
        size_t slots() const;
        /// Chunks flushed before the genesis commit.
        size_t chunks_flushed() const;

    private:
        struct Impl;
        std::unique_ptr<Impl> impl_;
    };
}

MONAD_NAMESPACE_END
