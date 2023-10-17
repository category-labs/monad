#include <monad/core/address.hpp>
#include <monad/core/withdrawal.hpp>

#include <monad/rlp/decode.hpp>
#include <monad/rlp/decode_helpers.hpp>
#include <monad/rlp/encode_helpers.hpp>

#include <gtest/gtest.h>

using namespace monad;
using namespace monad::rlp;

TEST(Rlp_Withdrawal, encode_decode_withdrawal)
{
    Withdrawal original_withdrawal{
        .index = 0,
        .validator_index = 0,
        .amount = 10000u,
        .recipient = 0x0000000000000000000000000000000000000000_address};

    auto const encoded_withdrawal = encode_withdrawal(original_withdrawal);

    byte_string const rlp_withdrawal =
        byte_string{0xda, 0x80, 0x80, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x82, 0x27, 0x10};

    EXPECT_EQ(encoded_withdrawal, rlp_withdrawal);

    Withdrawal decoded_withdrawal{};
    auto const remaining =
        decode_withdrawal(decoded_withdrawal, encoded_withdrawal);

    EXPECT_EQ(remaining.size(), 0);
    EXPECT_EQ(decoded_withdrawal.index, original_withdrawal.index);
    EXPECT_EQ(
        decoded_withdrawal.validator_index,
        original_withdrawal.validator_index);
    EXPECT_EQ(decoded_withdrawal.recipient, original_withdrawal.recipient);
    EXPECT_EQ(decoded_withdrawal.amount, original_withdrawal.amount);
}
