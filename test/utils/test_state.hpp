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

#pragma once

#include <category/execution/ethereum/db/db.hpp>
#include <category/execution/ethereum/db/trie_db.hpp>
#include <category/vm/vm.hpp>

#include <monad/test/config.hpp>

MONAD_TEST_NAMESPACE_BEGIN

struct TestState
{
    monad::InMemoryMachine machine;
    monad::mpt::Db db;
    monad::TrieDb trie_db;

    TestState()
        : db{machine}
        , trie_db{db}
    {
    }
};

using TestStateRef = std::shared_ptr<TestState>;

MONAD_TEST_NAMESPACE_END
