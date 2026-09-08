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
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>
#include <category/execution/ethereum/db/util.hpp>
#include <category/mpt/nibbles_view.hpp>
#include <category/mpt/node.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

#include <array>
#include <span>

using namespace monad;
using namespace monad::literals;

TEST(AccountLeafProcessor, RoundtripNoChildren)
{
    // A leaf with no children represents an account whose storage trie is
    // empty: AccountLeafProcessor::process must emit RLP with
    // storage_root == NULL_ROOT regardless of the node's data field.
    Account const original{
        .balance = uint256_t{24'000'000},
        .code_hash =
            0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32,
        .nonce = 7,
        .incarnation = Incarnation{0, 0}};
    Address const address = 0x00000000000000000000000000000000deadbeef_address;

    byte_string const db_encoded = encode_account_db(address, original);

    mpt::Node::SharedPtr const node = mpt::make_node(
        /*mask=*/0,
        /*children=*/{},
        /*path=*/mpt::NibblesView{},
        /*value=*/byte_string_view{db_encoded},
        /*data=*/byte_string_view{},
        /*version=*/0);

    byte_string const encoded = AccountLeafProcessor::process(*node);

    byte_string_view encoded_view{encoded};
    bytes32_t decoded_storage_root{};
    auto const decoded =
        rlp::decode_account(decoded_storage_root, encoded_view);
    ASSERT_FALSE(decoded.has_error());
    EXPECT_EQ(encoded_view.size(), 0);

    EXPECT_EQ(decoded_storage_root, NULL_ROOT);
    EXPECT_EQ(decoded.value().balance, original.balance);
    EXPECT_EQ(decoded.value().nonce, original.nonce);
    EXPECT_EQ(decoded.value().code_hash, original.code_hash);
}

TEST(AccountLeafProcessor, RoundtripWithChildren)
{
    // An account leaf with children carries the storage trie root in
    // node.data(). AccountLeafProcessor::process must surface that root in
    // the emitted RLP rather than falling through to NULL_ROOT.
    Account const original{
        .balance = uint256_t{42},
        .code_hash =
            0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32,
        .nonce = 1,
        .incarnation = Incarnation{0, 0}};
    Address const address = 0x00000000000000000000000000000000deadbeef_address;
    bytes32_t const storage_root =
        0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32;

    byte_string const db_encoded = encode_account_db(address, original);

    mpt::ChildData child{};
    child.len = 1;
    child.data[0] = 0xa;
    child.branch = 0x5;
    child.ptr = mpt::make_node(
        0, {}, mpt::NibblesView{}, byte_string_view{}, byte_string_view{}, 0);
    std::array<mpt::ChildData, 1> children{child};

    mpt::Node::SharedPtr const node = mpt::make_node(
        /*mask=*/static_cast<uint16_t>(1u << 0x5),
        /*children=*/std::span<mpt::ChildData>{children},
        /*path=*/mpt::NibblesView{},
        /*value=*/byte_string_view{db_encoded},
        /*data=*/
        byte_string_view{storage_root.bytes, sizeof(storage_root.bytes)},
        /*version=*/0);

    byte_string const encoded = AccountLeafProcessor::process(*node);

    byte_string_view encoded_view{encoded};
    bytes32_t decoded_storage_root{};
    auto const decoded =
        rlp::decode_account(decoded_storage_root, encoded_view);
    ASSERT_FALSE(decoded.has_error());
    EXPECT_EQ(encoded_view.size(), 0);

    EXPECT_EQ(decoded_storage_root, storage_root);
    EXPECT_EQ(decoded.value().balance, original.balance);
    EXPECT_EQ(decoded.value().nonce, original.nonce);
    EXPECT_EQ(decoded.value().code_hash, original.code_hash);
}

TEST(AccountLeafProcessor, EmptyValueReturnsEmpty)
{
    // A leaf carrying an empty value is the block-number leaf: process must
    // short-circuit and emit no bytes, regardless of any data field.
    mpt::Node::SharedPtr const node = mpt::make_node(
        /*mask=*/0,
        /*children=*/{},
        /*path=*/mpt::NibblesView{},
        /*value=*/byte_string_view{},
        /*data=*/byte_string_view{},
        /*version=*/0);

    EXPECT_EQ(AccountLeafProcessor::process(*node), byte_string{});
}
