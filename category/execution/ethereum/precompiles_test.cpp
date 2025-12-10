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

#include <category/execution/ethereum/core/address.hpp>
#include <category/execution/ethereum/precompiles.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/vm/evm/traits.hpp>
#include <monad/test/traits_test.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/hex.hpp>

#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <string_view>
#include <vector>

#include "test_resource_data.h"

using namespace monad;

using namespace evmc::literals;

namespace fs = std::filesystem;

namespace
{
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
                "18c547e4f7b0f325ad1e56f57e26c745b09a3e503d86e00e5255ff7f715d3d"
                "1c00"
                "0000000000000000000000000000000000000000000000000000000000001c"
                "73b1"
                "693892219d736caba55bdb67216e485557ea6b6af75f37096c9aa6a5a75fee"
                "b940"
                "b1d03b21e36b0e47e79769f095fe2ab855bd91e3a38756b7d75a9c4549"})
            .value();

    static auto const ECRECOVER_VALID_KEY_OUTPUT =
        evmc::from_hex(std::string_view{"000000000000000000000000a94f5374fce5ed"
                                        "bc8e2a8697c15331677e6ebf0b"})
            .value();

    // hash of empty string
    static auto const SHA256_NULL_HASH =
        evmc::from_hex(std::string_view{"e3b0c44298fc1c149afbf4c8996fb92427ae41"
                                        "e4649b934ca495991b7852b855"})
            .value();

    // hash of the string "lol"
    static auto const SHA256_LOL_HASH =
        evmc::from_hex(std::string_view{"07123e1f482356c415f684407a3b8723e10b2c"
                                        "bbc0b8fcd6282c49d37c9c1abc"})
            .value();

    // hash of empty string padded to 32 bytes
    static auto const RIPEMD160_NULL_HASH =
        evmc::from_hex(std::string_view{"0000000000000000000000009c1185a5c5e9fc"
                                        "54612808977ee8f548b2258d31"})
            .value();

    // hash of the string "lol" padded to 32 bytes
    static auto const RIPEMD160_LOL_HASH =
        evmc::from_hex(std::string_view{"00000000000000000000000014d61d472ae2e9"
                                        "74453fb7a0ef239510f36bee24"})
            .value();

    // the following point evaluation input data was directly copied from
    // https://github.com/ethereum/go-ethereum/tree/master/core/vm/testdata/precompiles
    static auto const POINT_EVALUATION_INPUT =
        evmc::from_hex(
            std::string_view{
                "014edfed8547661f6cb416eba53061a2f6dce872c0497e6dd485a876fe2567"
                "f156"
                "4c0a11a0f704f4fc3e8acfe0f8245f0ad1347b378fbf96e206da11a5d36306"
                "6d92"
                "8e13fe443e957d82e3e71d48cb65d51028eb4483e719bf8efcdf12f7c321a4"
                "21e2"
                "29565952cfff4ef3517100a97da1d4fe57956fa50a442f92af03b1bf37adac"
                "c8ad"
                "4ed209b31287ea5bb94d9d06a444d6bb5aadc3ceb615b50d6606bd54bfe529"
                "f592"
                "47987cd1ab848d19de599a9052f1835fb0d0d44cf70183e19a68c9"})

            .value();
    static auto const POINT_EVALUATION_EXPECTED =
        evmc::from_hex(std::string_view{"00000000000000000000000000000000000000"
                                        "0000000000000000000000100073"
                                        "eda753299d7d483339d80809a1d80553bda402"
                                        "fffe5bfeffffffff00000001"})
            .value();

    struct test_case
    {
        std::string name;
        evmc::bytes input;
        std::optional<evmc::bytes> expected;
        std::optional<evmc_status_code> expected_failure;
        int64_t gas;
        std::optional<int64_t> gas_offset;
    };

    void from_json(nlohmann::json const &j, test_case &t)
    {
        t.name = j.at("Name");
        std::string input = j.at("Input");
        t.input = evmc::from_hex(std::string_view{input}).value();
        if (j.contains("Expected")) {
            std::string expected = j.at("Expected");
            t.expected = evmc::from_hex(std::string_view{expected}).value();
        }

        // Expected-to-fail tests don't have a Gas field, so we assign them the
        // maximum gas value to prevent out-of-gas errors from masking the
        // actual failure the test is expected to trigger.
        t.gas = j.value("Gas", std::numeric_limits<decltype(t.gas)>::max());
    }

    std::vector<test_case> load_test_cases(fs::path const &json_path)
    {
        MONAD_ASSERT(fs::is_regular_file(json_path));
        std::ifstream in(json_path);
        return nlohmann::json::parse(in);
    }

    template <typename Callable>
    auto
    transform_test_cases(std::vector<test_case> const &source, Callable &&f)
    {
        auto res = source;
        for (auto &test_case : res) {
            f(test_case);
        }
        return res;
    }

    template <typename Callable>
    std::vector<test_case>
    transform_test_cases(std::span<test_case const> source, Callable &&f)
    {
        auto res = std::vector<test_case>{};
        for (auto &t : source) {
            test_case copy{t};
            f(copy);
            res.emplace_back(std::move(copy));
        }
        return res;
    }

    static test_case const ECRECOVER_TEST_CASES[] = {
        {.name = "ecrecover_unrecoverable_key_enough_gas",
         .input = ECRECOVER_UNRECOVERABLE_KEY_INPUT,
         .gas = 3'000,
         .gas_offset = 3'000},
        {.name = "ecrecover_unrecoverable_key_insufficient_gas",
         .input = ECRECOVER_UNRECOVERABLE_KEY_INPUT,
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 3'000,
         .gas_offset = -1},
        {.name = "ecrecover_valid_key_enough_gas",
         .input = ECRECOVER_VALID_KEY_INPUT,
         .gas = 3'000,
         .gas_offset = 3'000},
        {.name = "ecrecover_valid_key_insufficient_gas",
         .input = ECRECOVER_VALID_KEY_INPUT,
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 3'000,
         .gas_offset = -1}};

    static test_case const SHA256_TEST_CASES[] = {
        {.name = "sha256_empty_enough_gas",
         .input = evmc::bytes{},
         .expected = SHA256_NULL_HASH,
         .gas = 60,
         .gas_offset = 40},
        {.name = "sha256_empty_insufficient_gas",
         .input = evmc::bytes{},
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 60,
         .gas_offset = -1},
        {.name = "sha256_message_enough_gas",
         .input = evmc::bytes{reinterpret_cast<uint8_t const *>("lol"), 3},
         .expected = SHA256_LOL_HASH,
         .gas = 72,
         .gas_offset = 1},
        {.name = "sha256_message_insufficient_gas",
         .input = evmc::bytes{reinterpret_cast<uint8_t const *>("lol"), 3},
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 72,
         .gas_offset = -1}};

    static test_case const RIPEMD160_TEST_CASES[] = {
        {.name = "ripemd160_empty_enough_gas",
         .input = evmc::bytes{},
         .expected = RIPEMD160_NULL_HASH,
         .gas = 600,
         .gas_offset = 1},
        {.name = "ripemd160_empty_insufficient_gas",
         .input = evmc::bytes{},
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 600,
         .gas_offset = -1},
        {.name = "ripemd160_message_enough_gas",
         .input = evmc::bytes{reinterpret_cast<uint8_t const *>("lol"), 3},
         .expected = RIPEMD160_LOL_HASH,
         .gas = 720,
         .gas_offset = 1},
        {.name = "ripemd160_message_insufficient_gas",
         .input = evmc::bytes{reinterpret_cast<uint8_t const *>("lol"), 3},
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 720,
         .gas_offset = -1}};

    static test_case const IDENTITY_TEST_CASES[] = {
        {.name = "identity_empty_enough_gas",
         .input = evmc::bytes{},
         .expected = evmc::bytes{},
         .gas = 15,
         .gas_offset = 1},
        {.name = "identity_empty_insufficient_gas",
         .input = evmc::bytes{},
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 15,
         .gas_offset = -1},
        {.name = "identity_nonempty_enough_gas",
         .input = evmc::bytes{reinterpret_cast<uint8_t const *>("dead"), 4},
         .expected = evmc::bytes{reinterpret_cast<uint8_t const *>("dead"), 4},
         .gas = 18,
         .gas_offset = 1},
        {.name = "identity_nonempty_insufficient_gas",
         .input = evmc::bytes{reinterpret_cast<uint8_t const *>("dead"), 4},
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 18,
         .gas_offset = -1}};

    static test_case const POINT_EVALUATION_CASES[] = {
        {.name = "point_evaluation_enough_gas",
         .input = POINT_EVALUATION_INPUT,
         .expected = POINT_EVALUATION_EXPECTED,
         .gas = 50'000,
         .gas_offset = 3'000},
        {.name = "point_evaluation_insufficient_gas",
         .input = POINT_EVALUATION_INPUT,
         .expected_failure = evmc_status_code::EVMC_OUT_OF_GAS,
         .gas = 50'000,
         .gas_offset = -1}};

    template <Traits traits>
    void do_geth_tests(
        char const *suite_name, std::span<test_case const> test_cases,
        monad::Address const &code_address)
    {
        InMemoryMachine machine;
        mpt::Db db{machine};
        TrieDb tdb{db};
        vm::VM vm;
        BlockState bs{tdb, vm};
        State s{bs, Incarnation{0, 0}};

        for (auto const &test_case : test_cases) {
            auto test_with_gas_offset = [&](int64_t gas_offset) {
                evmc_message const input = {
                    .gas = test_case.gas + gas_offset,
                    .input_data = test_case.input.data(),
                    .input_size = test_case.input.size(),
                    .code_address = code_address};

                NoopCallTracer call_tracer{};
                evmc::Result const result =
                    check_call_precompile<traits>(s, call_tracer, input)
                        .value();

                if (test_case.expected) {
                    EXPECT_EQ(
                        result.status_code, evmc_status_code::EVMC_SUCCESS)
                        << suite_name << " test case " << test_case.name;
                }

                if (test_case.expected_failure) {
                    EXPECT_EQ(result.status_code, *test_case.expected_failure)
                        << suite_name << " test case " << test_case.name;
                }

                if (result.status_code == evmc_status_code::EVMC_SUCCESS) {
                    EXPECT_EQ(result.gas_left, gas_offset)
                        << suite_name << " test case " << test_case.name
                        << " gas check failed.";
                }
                else {
                    EXPECT_EQ(result.gas_left, 0)
                        << suite_name << " test case " << test_case.name
                        << " gas check failed. It should have cleared "
                           "gas_left.";
                }

                if (test_case.expected) {
                    auto &expected = *test_case.expected;

                    ASSERT_EQ(result.output_size, expected.size())
                        << suite_name << " test case " << test_case.name
                        << " output buffer size check failed.";

                    for (size_t i = 0; i < result.output_size; i++) {
                        EXPECT_EQ(expected[i], result.output_data[i])
                            << suite_name << " test case " << test_case.name
                            << " output buffer equality check failed.";
                    }
                }
            };

            if (test_case.gas_offset) {
                test_with_gas_offset(*test_case.gas_offset);
            }
            else {
                test_with_gas_offset(0);
                test_with_gas_offset(100);
            }
        }
    }

    template <Traits traits>
    void do_geth_tests(
        char const *suite_name, std::string_view json_path,
        monad::Address const &code_address)
    {
        auto const tests =
            load_test_cases(test_resource::geth_vectors_dir / json_path);
        do_geth_tests<traits>(suite_name, tests, code_address);
    }
}

TYPED_TEST(TraitsTest, ecrecover)
{
    if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
        if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
            // MONAD_SEVEN doubles the price of ecrecover
            auto const tests = transform_test_cases(
                ECRECOVER_TEST_CASES, [](auto &test) { test.gas *= 2; });
            return do_geth_tests<typename TestFixture::Trait>(
                "ecrecover", tests, 0x01_address);
        }
    }

    do_geth_tests<typename TestFixture::Trait>(
        "ecrecover", ECRECOVER_TEST_CASES, 0x01_address);
}

TYPED_TEST(TraitsTest, sha256)
{
    do_geth_tests<typename TestFixture::Trait>(
        "sha256", SHA256_TEST_CASES, 0x02_address);
}

TYPED_TEST(TraitsTest, ripemd160)
{
    do_geth_tests<typename TestFixture::Trait>(
        "ripemd160", RIPEMD160_TEST_CASES, 0x03_address);
}

TYPED_TEST(TraitsTest, identity)
{
    do_geth_tests<typename TestFixture::Trait>(
        "identity", IDENTITY_TEST_CASES, 0x04_address);
}

TYPED_TEST(TraitsTest, modular_exponentiation)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_BYZANTIUM) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x05_address));
    }
    else if constexpr (TestFixture::Trait::evm_rev() < EVMC_BERLIN) {
        do_geth_tests<typename TestFixture::Trait>(
            "Modular Exponentiation", "modexp.json", 0x05_address);
    }
    else if constexpr (TestFixture::Trait::evm_rev() < EVMC_OSAKA) {
        // EIP-2565 repricing since Berlin
        do_geth_tests<typename TestFixture::Trait>(
            "Modular Exponentiation", "modexp_eip2565.json", 0x05_address);
    }
    else {
        // EIP-7883 repricing since Osaka
        do_geth_tests<typename TestFixture::Trait>(
            "Modular Exponentiation", "modexp_eip7883.json", 0x05_address);
    }
}

TYPED_TEST(TraitsTest, bn_add)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_BYZANTIUM) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x06_address));
    }
    else {
        auto tests =
            load_test_cases(test_resource::geth_vectors_dir / "bn256Add.json");

        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                // MONAD_SEVEN doubles the price of bn_add
                tests = transform_test_cases(
                    tests, [](auto &test) { test.gas *= 2; });
            }
        }
        else if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
            // Before https://eips.ethereum.org/EIPS/eip-1108
            tests =
                transform_test_cases(tests, [](auto &test) { test.gas = 500; });
        }

        do_geth_tests<typename TestFixture::Trait>(
            "bn_add", tests, 0x06_address);
    }
}

TYPED_TEST(TraitsTest, bn_mul)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_BYZANTIUM) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x07_address));
    }
    else {
        auto tests = load_test_cases(
            test_resource::geth_vectors_dir / "bn256ScalarMul.json");

        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                // MONAD_SEVEN increases the price of bn_mul by 5x
                tests = transform_test_cases(
                    tests, [](auto &test) { test.gas *= 5; });
            }
        }
        else if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
            // Before https://eips.ethereum.org/EIPS/eip-1108
            tests = transform_test_cases(
                tests, [](auto &test) { test.gas = 40'000; });
        }

        do_geth_tests<typename TestFixture::Trait>(
            "bn_mul", tests, 0x07_address);
    }
}

TYPED_TEST(TraitsTest, bn_pairing)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_BYZANTIUM) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x08_address));
    }
    else {
        auto tests = load_test_cases(
            test_resource::geth_vectors_dir / "bn256Pairing.json");

        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                // MONAD_SEVEN increases the price of bn_pairing by 5x
                tests = transform_test_cases(
                    tests, [](auto &test) { test.gas *= 5; });
            }
        }
        else if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
            // Before https://eips.ethereum.org/EIPS/eip-1108
            tests = transform_test_cases(tests, [](auto &test) {
                // k = input size in bytes / 192;
                auto const k = test.input.size() / 192;
                test.gas = static_cast<int64_t>(80'000 * k + 100'000);
            });
        }

        do_geth_tests<typename TestFixture::Trait>(
            "bn_pairing", tests, 0x08_address);
    }
}

TYPED_TEST(TraitsTest, blake2f)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_ISTANBUL) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x09_address));
    }
    else {
        auto blake2f_test = [&](char const *name, std::string_view json) {
            std::vector<test_case> tests =
                load_test_cases(test_resource::geth_vectors_dir / json);

            if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
                if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                    // MONAD_SEVEN doubles the price of blake2F
                    tests = transform_test_cases(
                        tests, [](auto &test) { test.gas *= 2; });
                }
            }

            do_geth_tests<typename TestFixture::Trait>(
                name, tests, 0x09_address);
        };

        blake2f_test("blake_2f_valid", "blake2F.json");
        blake2f_test("blake_2f_invalid", "fail-blake2f.json");
    }
}

TYPED_TEST(TraitsTest, point_evaluation)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_CANCUN) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x0a_address));
    }
    else {
        ASSERT_TRUE(init_trusted_setup());

        if constexpr (is_monad_trait_v<typename TestFixture::Trait>) {
            if constexpr (TestFixture::Trait::monad_rev() >= MONAD_SEVEN) {
                // In MONAD_SEVEN point_evaluation cost is increased by 4x
                auto const tests = transform_test_cases(
                    POINT_EVALUATION_CASES, [](auto &test) { test.gas *= 4; });
                return do_geth_tests<typename TestFixture::Trait>(
                    "point_evaluation", tests, 0x0a_address);
            }
        }

        do_geth_tests<typename TestFixture::Trait>(
            "point_evaluation", POINT_EVALUATION_CASES, 0x0a_address);
    }
}

TYPED_TEST(TraitsTest, blsg1add)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x0b_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g1_add_valid", "blsG1Add.json", 0x0b_address);

        do_geth_tests<typename TestFixture::Trait>(
            "bls_g1_add_invalid", "fail-blsG1Add.json", 0x0b_address);
    }
}

TYPED_TEST(TraitsTest, blsg1mul)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x0c_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g1_mul_valid", "blsG1Mul.json", 0x0c_address);

        do_geth_tests<typename TestFixture::Trait>(
            "bls_g1_mul_invalid", "fail-blsG1Mul.json", 0x0c_address);

        do_geth_tests<typename TestFixture::Trait>(
            "bls_g1_msm_valid", "blsG1MultiExp.json", 0x0c_address);

        do_geth_tests<typename TestFixture::Trait>(
            "bls_g1_msm_invalid", "fail-blsG1MultiExp.json", 0x0c_address);
    }
}

TYPED_TEST(TraitsTest, blsg2add)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x0d_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g2_add_valid", "blsG2Add.json", 0x0d_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g2_add_invalid", "fail-blsG2Add.json", 0x0d_address);
    }
}

TYPED_TEST(TraitsTest, blsg2mul)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x0e_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g2_mul_valid", "blsG2Mul.json", 0x0e_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g2_mul_invalid", "fail-blsG2Mul.json", 0x0e_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g2_msm_valid", "blsG2MultiExp.json", 0x0e_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls_g2_msm_invalid", "fail-blsG2MultiExp.json", 0x0e_address);
    }
}

TYPED_TEST(TraitsTest, bls_pairing_check)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x0f_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls12_pairing_check_valid", "blsPairing.json", 0x0f_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls12_pairing_check_invalid",
            "fail-blsPairing.json",
            0x0f_address);
    }
}

TYPED_TEST(TraitsTest, bls_map_g1)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x10_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls12_map_fp_to_g1_valid", "blsMapG1.json", 0x10_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls12_map_fp_to_g1_invalid", "fail-blsMapG1.json", 0x10_address);
    }
}

TYPED_TEST(TraitsTest, bls_map_g2)
{
    if constexpr (TestFixture::Trait::evm_rev() < EVMC_PRAGUE) {
        EXPECT_FALSE(is_precompile<typename TestFixture::Trait>(0x11_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "bls12_map_fp2_to_g2_valid", "blsMapG2.json", 0x11_address);
        do_geth_tests<typename TestFixture::Trait>(
            "bls12_map_fp2_to_g2_invalid", "fail-blsMapG2.json", 0x11_address);
    }
}

TYPED_TEST(TraitsTest, p256_verify)
{
    if constexpr (!TestFixture::Trait::eip_7951_active()) {
        EXPECT_FALSE(
            is_precompile<typename TestFixture::Trait>(0x0100_address));
    }
    else {
        do_geth_tests<typename TestFixture::Trait>(
            "p256_verify", "p256Verify.json", 0x0100_address);
    }
}
