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

// Bulk genesis bypasses State and builds StateDeltas for commit_simple, as
// load_genesis_state does. Host State storage lookups scan linearly and
// become quadratic for large accounts; this avoids that seeding cost.

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
    /// Commit genesis in chunks to bound delta memory (752 bytes per
    /// StateDelta before trie nodes). Write account, then its code/storage in
    /// the same chunk. Flushing occurs only at the start of account();
    /// referring to an earlier chunk asserts rather than dropping a write.
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

        /// Commit pending data at genesis height and return the sealed header
        /// with computed fields. A one-chunk state takes one commit, matching
        /// the State-based route.
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
