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

#include <category/core/bytes.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/nibbles_view.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::literals;
using namespace monad::mpt;

namespace
{
    bytes32_t const block_id =
        0x9b1d4e7a02c6f83e5a7d0b2c4e6f8a1c3e5d7b9f0a2c4e6d8b1f3a5c7e9d0b2c_bytes32;
    bytes32_t const account =
        0x3f8a6c1e9d2b5f7a0c4e8d1b3a6f9c2e5d8b0a7f4c1e9d3b6a8f2c5e7d0b4a91_bytes32;
    bytes32_t const slot =
        0xd04b7e2a9c5f1e8b3d6a0f4c7e2b9d5a1f8c3e6b0d4a7f2c9e5b1d8a3f6c0e47_bytes32;

    void expect_bulk_matches_per_nibble(NibblesView const path)
    {
        auto const n = static_cast<unsigned>(path.nibble_size());
        for (unsigned start = 0; start <= n; ++start) {
            for (unsigned end = start; end <= n; ++end) {
                OnDiskMachine per_nibble;
                OnDiskMachine bulk;
                for (unsigned i = 0; i < start; ++i) {
                    per_nibble.down(path.get(i));
                    bulk.down(path.get(i));
                }
                for (unsigned i = start; i < end; ++i) {
                    per_nibble.down(path.get(i));
                }
                bulk.down(path.substr(start, end - start));
                ASSERT_EQ(bulk.depth, per_nibble.depth)
                    << "start=" << start << " end=" << end;
                ASSERT_EQ(bulk.trie_section, per_nibble.trie_section)
                    << "start=" << start << " end=" << end;
                ASSERT_EQ(bulk.table, per_nibble.table)
                    << "start=" << start << " end=" << end;
            }
        }
    }
}

TEST(MachineBase, bulk_down_matches_per_nibble_finalized_storage)
{
    expect_bulk_matches_per_nibble(concat(
        FINALIZED_NIBBLE,
        STATE_NIBBLE,
        NibblesView{account},
        NibblesView{slot}));
}

TEST(MachineBase, bulk_down_matches_per_nibble_proposal_storage)
{
    expect_bulk_matches_per_nibble(concat(
        PROPOSAL_NIBBLE,
        NibblesView{block_id},
        STATE_NIBBLE,
        NibblesView{account},
        NibblesView{slot}));
}

TEST(MachineBase, bulk_down_matches_per_nibble_call_frame)
{
    expect_bulk_matches_per_nibble(
        concat(FINALIZED_NIBBLE, CALL_FRAME_NIBBLE, NibblesView{account}));
}
