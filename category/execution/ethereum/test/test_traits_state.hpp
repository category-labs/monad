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

#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/mpt/db.hpp>
#include <category/vm/vm.hpp>

#include <monad/test/traits_test.hpp>

MONAD_NAMESPACE_BEGIN

struct InMemoryStateTestBase
{
    InMemoryMachine machine;
    mpt::Db db{machine};
    TrieDb tdb{db};
    vm::VM vm;
    BlockState block_state{tdb, vm};
    State state{block_state, Incarnation{0, 0}};
};

template <typename T>
struct InMemoryStateTraitsTest
    : public InMemoryStateTestBase
    , public TraitsTest<T>
{
    using InMemoryStateTestBase::state;
};

DEFINE_TRAITS_FIXTURE(InMemoryStateTraitsTest);

MONAD_NAMESPACE_END
