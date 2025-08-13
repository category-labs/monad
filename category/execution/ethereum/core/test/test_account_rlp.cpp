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

#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/int.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/core/rlp/account_rlp.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp_Account, Encode)
{
    using namespace intx;
    using namespace evmc::literals;

    static constexpr uint256_t b{24'000'000};
    static constexpr bytes32_t storage_root{
        0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32};
    static constexpr bytes32_t code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};
    Account const a{.balance = b, .code_hash = code_hash};
    byte_string const rlp_account{
        0xf8, 0x48, 0x80, 0x84, 0x01, 0x6e, 0x36, 0x00, 0xa0, 0xbe, 0xa3,
        0x4d, 0xd0, 0x4b, 0x09, 0xad, 0x3b, 0x60, 0x14, 0x25, 0x1e, 0xe2,
        0x45, 0x78, 0x07, 0x40, 0x87, 0xee, 0x60, 0xfd, 0xa8, 0xc3, 0x91,
        0xcf, 0x46, 0x6d, 0xfe, 0x5d, 0x68, 0x7d, 0x7b, 0xa0, 0x6b, 0x8c,
        0xeb, 0xdc, 0x25, 0x90, 0xb4, 0x86, 0x45, 0x7b, 0xbb, 0x28, 0x6e,
        0x96, 0x01, 0x1b, 0xdd, 0x50, 0xcc, 0xc1, 0xd8, 0x58, 0x0c, 0x1f,
        0xfb, 0x3c, 0x89, 0xe8, 0x28, 0x46, 0x22, 0x83};
    auto const encoded_account = encode_account(a, storage_root);
    EXPECT_EQ(encoded_account, rlp_account);

    byte_string_view encoded_account_view{encoded_account};
    bytes32_t decoded_storage_root{};
    auto const decoded_account =
        decode_account(decoded_storage_root, encoded_account_view);
    ASSERT_FALSE(decoded_account.has_error());
    EXPECT_EQ(encoded_account_view.size(), 0);

    EXPECT_EQ(storage_root, decoded_storage_root);
    EXPECT_EQ(a.balance, decoded_account.value().balance);
    EXPECT_EQ(a.code_hash, decoded_account.value().code_hash);
}
