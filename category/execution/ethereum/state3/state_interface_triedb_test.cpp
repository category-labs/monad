// Copyright (C) 2025-26 Category Labs, Inc.
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

// The StateInterface behaviour suite run against the native state3 State
// over a triedb: the pre-state is committed to an in-memory one as the
// previous block, and each transaction is a State over a BlockState that is
// merged back at the boundary.

#include <test_resource_data.h>

#include <category/core/assert.h>
#include <category/core/bytes.hpp>
#include <category/core/keccak.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/state3/state_interface_test.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/code.hpp>
#include <category/vm/evm/revision.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/vm.hpp>
#include <monad/test/config.hpp>

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

MONAD_TEST_NAMESPACE_BEGIN

namespace
{
    struct TrieDbBackend
    {
        using State = ::monad::State;

        mpt::Db db{std::make_unique<InMemoryMachine>()};
        TrieDb tdb{db};
        vm::VM vm;
        BlockState bs{tdb, vm};
        std::optional<State> st;
        uint64_t tx{1};

        explicit TrieDbBackend(PreState const &pre)
        {
            StateDeltas deltas;
            for (auto const &a : pre.accounts) {
                StorageDeltas storage;
                for (auto const &[key, value] : a.storage) {
                    storage.emplace(key, StorageDelta{bytes32_t{}, value});
                }
                deltas.emplace(
                    a.address,
                    StateDelta{
                        .account = {std::nullopt, a.account},
                        .storage = std::move(storage)});
            }
            Code code;
            for (auto const &bytes : pre.codes) {
                code.emplace(
                    to_bytes(keccak256(bytes)),
                    vm::make_shared_intercode(bytes));
            }
            commit_sequential(tdb, deltas, code, BlockHeader{});
            st.emplace(bs, Incarnation{1, tx});
        }

        State &state()
        {
            return *st;
        }

        void next_transaction()
        {
            MONAD_ASSERT(bs.can_merge(*st));
            bs.merge(*st);
            st.emplace(bs, Incarnation{1, ++tx});
        }
    };

    using Shanghai = EvmTraits<EvmRevision::Shanghai>;
    using Cancun = EvmTraits<EvmRevision::Cancun>;
    using Amsterdam = EvmTraits<EvmRevision::Amsterdam>;

    using Params = ::testing::Types<
        Param<TrieDbBackend, Shanghai>, Param<TrieDbBackend, Cancun>,
        Param<TrieDbBackend, Amsterdam>>;
}

INSTANTIATE_TYPED_TEST_SUITE_P(TrieDb, StateInterfaceTest, Params);

MONAD_TEST_NAMESPACE_END
