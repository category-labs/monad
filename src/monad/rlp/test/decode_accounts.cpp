#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>

#include <monad/core/byte_string.hpp>
#include <monad/core/bytes.hpp>
#include <monad/core/int.hpp>
#include <monad/core/transaction.hpp>

#include <intx/intx.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::rlp;

// Test Case Copied from Encode Account
TEST(Rlp_Account, DecodeAfterEncodeAccount)
{
    using namespace intx;
    using namespace evmc::literals;

    // Account w/o nonce
    byte_string_loc pos = 0;
    static constexpr uint256_t b{24'000'000};
    static constexpr bytes32_t storage_root{
        0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32};
    static constexpr bytes32_t code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};
    Account a{.balance = b, .code_hash = code_hash};
    auto encoded_account = encode_account(a, storage_root);
    auto [decoded_account, decoded_storage_root] = decode_account(encoded_account,pos);

    EXPECT_EQ(storage_root, decoded_storage_root);
    EXPECT_EQ(a.balance, decoded_account.balance);
    EXPECT_EQ(a.code_hash, decoded_account.code_hash);

    // With nonce added
    a.nonce = 10;
    pos = 0;
    auto encoded_account_2 = encode_account(a, storage_root);
    auto [decoded_account_2, decoded_storage_root_2] = decode_account(encoded_account_2, pos);

    EXPECT_EQ(a.nonce, decoded_account_2.nonce);
    EXPECT_EQ(storage_root, decoded_storage_root_2);
    EXPECT_EQ(a.balance, decoded_account_2.balance);
    EXPECT_EQ(a.code_hash, decoded_account_2.code_hash);
}

