#include <gtest/gtest.h>

#include <ethash/keccak.hpp>
#include <evmc/hex.hpp>
#include <intx/intx.hpp>
#include <iomanip>
#include <monad/execution/ethereum/fork_traits.hpp>
#include <monad/execution/test/fakes.hpp>

using empty_list_t = boost::mp11::mp_list<>;

#undef DISABLE_LOGGING
#include <monad/logging/monad_log.hpp>

using state_t = monad::execution::fake::State;
using namespace evmc::literals;
using namespace monad::fork_traits;
using namespace boost::mp11;

// the following elliptic curve input data was directly copied from
// https://github.com/ethereum/go-ethereum/tree/master/core/vm/testdata/precompiles

static auto const ECRECOVER_UNRECOVERABLE_KEY_INPUT =
    evmc::from_hex(
        std::string_view{
            "a8b53bdf3306a35a7103ab5504a0c9b492295564b6202b1942a84ef3001072"
            "81000000000000000000000000000000000000000000000000000000000000"
            "001b3078356531653033663533636531386237373263636230303933666637"
            "31663366353366356337356237346463623331613835616138623838393262"
            "34653862112233445566778899101112131415161718192021222324252627"
            "2829303132"})
        .value();

static auto const ECRECOVER_VALID_KEY_INPUT =
    evmc::from_hex(
        std::string_view{
            "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d1c00"
            "0000000000000000000000000000000000000000000000000000000000001c73b1"
            "693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75feeb940"
            "b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549"})
        .value();

static auto const ECRECOVER_VALID_KEY_OUTPUT =
    evmc::from_hex(
        std::string_view{
            "000000000000000000000000a94f5374fce5edbc8e2a8697c15331677e6ebf0b"})
        .value();

// hash of empty string
static auto const SHA256_NULL_HASH =
    evmc::from_hex(
        std::string_view{
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"})
        .value();

// hash of the string "lol"
static auto const SHA256_LOL_HASH =
    evmc::from_hex(
        std::string_view{
            "07123e1f482356c415f684407a3b8723e10b2cbbc0b8fcd6282c49d37c9c1abc"})
        .value();

// hash of empty string padded to 32 bytes
static auto const RIPEMD160_NULL_HASH =
    evmc::from_hex(
        std::string_view{
            "9c1185a5c5e9fc54612808977ee8f548b2258d31000000000000000000000000"})
        .value();

// hash of the string "lol" padded to 32 bytes
static auto const RIPEMD160_LOL_HASH =
    evmc::from_hex(
        std::string_view{
            "14d61d472ae2e974453fb7a0ef239510f36bee24000000000000000000000000"})
        .value();

using ecrecover_frontier_through_homestead =
    mp_at_c<homestead::static_precompiles_t, 0>;
using sha256_frontier_through_homestead =
    mp_at_c<homestead::static_precompiles_t, 1>;
using ripemd160_frontier_through_homestead =
    mp_at_c<homestead::static_precompiles_t, 2>;
using identity_frontier_through_homestead =
    mp_at_c<homestead::static_precompiles_t, 3>;

TEST(FrontierThroughHomestead, ecrecover_unrecoverable_key_enough_gas)
{
    evmc_message input = {
        .gas = 6'000,
        .input_data = ECRECOVER_UNRECOVERABLE_KEY_INPUT.data(),
        .input_size = ECRECOVER_UNRECOVERABLE_KEY_INPUT.size()};

    auto const result = ecrecover_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 3'000);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, ecrecover_unrecoverable_key_insufficient_gas)
{
    evmc_message input = {
        .gas = 2'999,
        .input_data = ECRECOVER_UNRECOVERABLE_KEY_INPUT.data(),
        .input_size = ECRECOVER_UNRECOVERABLE_KEY_INPUT.size()};

    auto const result = ecrecover_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, ecrecover_valid_key_enough_gas)
{
    evmc_message input = {
        .gas = 6'000,
        .input_data = ECRECOVER_VALID_KEY_INPUT.data(),
        .input_size = ECRECOVER_VALID_KEY_INPUT.size()};

    auto const result = ecrecover_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 3'000);
    EXPECT_EQ(result.output_size, 32);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], ECRECOVER_VALID_KEY_OUTPUT[i]);
    }
}

TEST(FrontierThroughHomestead, ecrecover_valid_key_insufficient_gas)
{
    evmc_message input = {
        .gas = 2'999,
        .input_data = ECRECOVER_VALID_KEY_INPUT.data(),
        .input_size = ECRECOVER_VALID_KEY_INPUT.size()};

    auto const result = ecrecover_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, sha256_empty_enough_gas)
{
    evmc_message input = {.gas = 100};
    auto const result = sha256_frontier_through_homestead::execute(input);
    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 40);
    EXPECT_EQ(result.output_size, 32);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], SHA256_NULL_HASH[i]);
    }
}

TEST(FrontierThroughHomestead, sha256_empty_insufficient_gas)
{
    evmc_message input = {.gas = 59};
    auto const result = sha256_frontier_through_homestead::execute(input);
    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, sha256_message_enough_gas)
{
    monad::byte_string_fixed<3> message = {'l', 'o', 'l'};
    evmc_message input = {
        .gas = 73, .input_data = message.data(), .input_size = message.size()};

    auto const result = sha256_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 1);
    EXPECT_EQ(result.output_size, 32);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], SHA256_LOL_HASH[i]);
    }
}

TEST(FrontierThroughHomestead, sha256_message_insufficient_gas)
{
    monad::byte_string_fixed<3> message = {'l', 'o', 'l'};
    evmc_message input = {
        .gas = 71, .input_data = message.data(), .input_size = message.size()};

    auto const result = sha256_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, ripemd160_empty_enough_gas)
{
    evmc_message input = {.gas = 601};

    auto const result = ripemd160_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 1);
    EXPECT_EQ(result.output_size, 32);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], RIPEMD160_NULL_HASH[i]);
    }
}

TEST(FrontierThroughHomestead, ripemd160_empty_insufficient_gas)
{
    evmc_message input = {.gas = 599};

    auto const result = ripemd160_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], RIPEMD160_NULL_HASH[i]);
    }
}

TEST(FrontierThroughHomestead, ripemd160_message_enough_gas)
{
    monad::byte_string_fixed<3> message = {'l', 'o', 'l'};
    evmc_message input = {
        .gas = 721, .input_data = message.data(), .input_size = message.size()};

    auto const result = ripemd160_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 1);
    EXPECT_EQ(result.output_size, 32);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], RIPEMD160_LOL_HASH[i]);
    }
}

TEST(FrontierThroughHomestead, ripemd160_message_insufficient_gas)
{
    monad::byte_string_fixed<3> message = {'l', 'o', 'l'};
    evmc_message input = {
        .gas = 619, .input_data = message.data(), .input_size = message.size()};

    auto const result = ripemd160_frontier_through_homestead::execute(input);

    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, identity_empty_enough_gas)
{
    evmc_message input = {.gas = 16};
    auto const result = identity_frontier_through_homestead::execute(input);
    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 1);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, identity_empty_insufficient_gas)
{
    evmc_message input = {.gas = 14};
    auto const result = identity_frontier_through_homestead::execute(input);
    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}

TEST(FrontierThroughHomestead, identity_nonempty_enough_gas)
{
    monad::bytes32_t data = 0xdeadbeef_bytes32;
    evmc_message input = {
        .gas = 19,
        .input_data = data.bytes,
        .input_size = sizeof(monad::bytes32_t)};
    auto const result = identity_frontier_through_homestead::execute(input);
    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_SUCCESS);
    EXPECT_EQ(result.gas_left, 1);
    EXPECT_EQ(result.output_size, 32);

    for (size_t i = 0; i < result.output_size; i++) {
        EXPECT_EQ(result.output_data[i], data.bytes[i]);
    }
}

TEST(FrontierThroughHomestead, identity_nonempty_insufficient_gas)
{
    monad::bytes32_t data = 0xdeadbeef_bytes32;
    evmc_message input = {
        .gas = 17,
        .input_data = data.bytes,
        .input_size = sizeof(monad::bytes32_t)};
    auto const result = identity_frontier_through_homestead::execute(input);
    EXPECT_EQ(result.status_code, evmc_status_code::EVMC_OUT_OF_GAS);
    EXPECT_EQ(result.gas_left, 0);
    EXPECT_EQ(result.output_size, 0);
}
