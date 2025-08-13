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

#include "test_fixtures_base.hpp"

#include <category/async/test/test_fixture.hpp>

namespace monad::test
{
    struct InMemoryMerkleTrieGTest
        : public MerkleTrie<InMemoryTrieBase<void, ::testing::Test>>
    {
        using MerkleTrie<
            InMemoryTrieBase<void, ::testing::Test>>::InMemoryTrieBase;
    };

    struct OnDiskMerkleTrieGTest
        : public MerkleTrie<OnDiskTrieBase<void, ::testing::Test>>
    {
        using MerkleTrie<OnDiskTrieBase<void, ::testing::Test>>::OnDiskTrieBase;
    };

    struct InMemoryTrieGTest
        : public PlainTrie<InMemoryTrieBase<void, ::testing::Test>>
    {
    };

    struct OnDiskTrieGTest
        : public PlainTrie<OnDiskTrieBase<void, ::testing::Test>>
    {
    };

    template <
        FillDBWithChunksConfig Config,
        monad::mpt::lockable_or_void LockType = void>
    struct FillDBWithChunksGTest
        : public FillDBWithChunks<Config, LockType, ::testing::Test>
    {
        using FillDBWithChunks<
            Config, LockType, ::testing::Test>::FillDBWithChunks;
    };

}
