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

    static constexpr uint256_t b{24'000'000};
    static constexpr bytes32_t storage_root{
        0xbea34dd04b09ad3b6014251ee24578074087ee60fda8c391cf466dfe5d687d7b_bytes32};
    static constexpr bytes32_t code_hash{
        0x6b8cebdc2590b486457bbb286e96011bdd50ccc1d8580c1ffb3c89e828462283_bytes32};
    Account const a{.balance = b, .code_hash = code_hash};
    auto const encoded_account = encode_account(a, storage_root);
    auto [dec_acc, dec_cr] = decode_account(encoded_account);

    EXPECT_EQ(storage_root, dec_cr);
    EXPECT_EQ(a.balance, dec_acc.balance);
}

