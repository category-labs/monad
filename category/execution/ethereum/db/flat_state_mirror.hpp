// Copyright (C) 2025 Category Labs, Inc.
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

// Entire component is compiled out unless the RocksDB backend is enabled, so
// this header is empty in the default build and TrieDb is unchanged.
#ifdef MONAD_HAVE_ROCKSDB

    #include <category/core/address.hpp>
    #include <category/core/bytes.hpp>
    #include <category/core/config.hpp>
    #include <category/execution/ethereum/core/account.hpp>
    #include <category/execution/ethereum/state2/state_deltas.hpp>
    #include <category/execution/ethereum/types/incarnation.hpp>
    #include <category/statedb/kv_store.hpp>

    #include <filesystem>
    #include <memory>
    #include <optional>

MONAD_NAMESPACE_BEGIN

// F5 validating shadow: a flat (raw-key) RocksDB mirror of MonadDB state. On
// each commit, TrieDb writes the block's StateDeltas here too; on each read
// TrieDb asserts that a *present* flat value equals the trie's (the trie stays
// the source of truth, and the flat store may be incomplete since it starts
// empty -- only replayed blocks populate it). The flat value reuses the trie
// leaf encodings (encode_account_db / encode_storage_db), so it is
// byte-identical to the trie leaf -- only the key differs: a raw Address
// [+ raw slot] instead of keccak paths. Storage is slot-granular (no pages,
// matching the current MonadDB layout); selfdestruct/recreate clears the
// address's flat storage prefix explicitly. Replay-only; not wired for
// proposals/pruning.
class FlatStateMirror
{
public:
    static std::unique_ptr<FlatStateMirror>
    open(std::filesystem::path const &dir);

    explicit FlatStateMirror(std::unique_ptr<statedb::KvStore>);

    // Mirror one block's deltas (account + slot writes/deletes) into the flat
    // store, matching what the trie commits.
    void write(StateDeltas const &);

    std::optional<Account> read_account(Address const &) const;
    bytes32_t
    read_storage(Address const &, Incarnation, bytes32_t const &slot) const;

private:
    std::unique_ptr<statedb::KvStore> kv_;
};

MONAD_NAMESPACE_END

#endif // MONAD_HAVE_ROCKSDB
