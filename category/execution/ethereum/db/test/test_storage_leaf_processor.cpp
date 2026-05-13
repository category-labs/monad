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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/core/rlp/bytes_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::literals;

TEST(StorageLeafProcessor, Roundtrip)
{
    // A storage leaf's value is encode_storage_db(slot, val). The processor
    // strips the slot and re-emits just the value as an RLP-encoded compact
    // (leading-zero-stripped) bytes32. Decoding the result must yield the
    // original value, regardless of the slot.
    bytes32_t const slot =
        0x0000000000000000000000000000000000000000000000000000000000000042_bytes32;
    bytes32_t const value =
        0x00000000000000000000000000000000000000000000000000000000deadbeef_bytes32;

    byte_string const db_encoded = encode_storage_db(slot, value);

    mpt::Node::SharedPtr const node = mpt::make_node(
        /*mask=*/0,
        /*children=*/{},
        /*path=*/mpt::NibblesView{},
        /*value=*/byte_string_view{db_encoded},
        /*data=*/byte_string_view{},
        /*version=*/0);

    byte_string const encoded = StorageLeafProcessor::process(*node);

    byte_string_view encoded_view{encoded};
    auto const decoded = rlp::decode_bytes32_compact(encoded_view);
    ASSERT_FALSE(decoded.has_error());
    EXPECT_EQ(encoded_view.size(), 0);
    EXPECT_EQ(decoded.value(), value);
}
