#include <category/core/byte_string.hpp>
#include <category/execution/ethereum/core/rlp/withdrawal_rlp.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>

#include <evmc/evmc.hpp>

#include <gtest/gtest.h>

using namespace evmc::literals;
using namespace monad;
using namespace monad::rlp;

TEST(Rlp_Withdrawal, encode_decode_withdrawal)
{
    Withdrawal const original_withdrawal{
        .index = 0,
        .validator_index = 0,
        .amount = 10000u,
        .recipient = 0x00_address};

    auto const encoded_withdrawal = encode_withdrawal(original_withdrawal);

    byte_string const rlp_withdrawal =
        byte_string{0xda, 0x80, 0x80, 0x94, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x82, 0x27, 0x10};

    EXPECT_EQ(encoded_withdrawal, rlp_withdrawal);

    byte_string_view encoded_withdrawal_view{encoded_withdrawal};
    auto const decoded_withdrawal = decode_withdrawal(encoded_withdrawal_view);

    ASSERT_FALSE(decoded_withdrawal.has_error());
    EXPECT_EQ(encoded_withdrawal_view.size(), 0);
    EXPECT_EQ(decoded_withdrawal.value().index, original_withdrawal.index);
    EXPECT_EQ(
        decoded_withdrawal.value().validator_index,
        original_withdrawal.validator_index);
    EXPECT_EQ(
        decoded_withdrawal.value().recipient, original_withdrawal.recipient);
    EXPECT_EQ(decoded_withdrawal.value().amount, original_withdrawal.amount);
}
