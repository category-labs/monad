#include <ethereum_test.hpp>
#include <from_json.hpp>

#include <category/execution/ethereum/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>
#include <evmc/hex.hpp>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <gtest/gtest.h>

#include <cstdint>

MONAD_TEST_NAMESPACE_BEGIN

void load_state_from_json(nlohmann::json const &j, State &state)
{
    for (auto const &[j_addr, j_acc] : j.items()) {
        auto const account_address =
            evmc::from_hex<monad::Address>(j_addr).value();

        if (j_acc.contains("code") || j_acc.contains("storage")) {
            ASSERT_TRUE(j_acc.contains("code") && j_acc.contains("storage"));
            state.create_contract(account_address);
        }

        if (j_acc.contains("code")) {
            state.set_code(
                account_address, j_acc.at("code").get<monad::byte_string>());
        }

        state.add_to_balance(
            account_address, j_acc.at("balance").get<intx::uint256>());
        // we cannot use the nlohmann::json from_json<uint64_t> because
        // it does not use the strtoull implementation, whereas we need
        // it so we can turn a hex string into a uint64_t
        state.set_nonce(
            account_address, integer_from_json<uint64_t>(j_acc.at("nonce")));

        if (j_acc.contains("storage")) {
            ASSERT_TRUE(j_acc["storage"].is_object());
            for (auto const &[key, value] : j_acc["storage"].items()) {
                nlohmann::json const key_json = key;
                monad::bytes32_t const key_bytes32 =
                    key_json.get<monad::bytes32_t>();
                monad::bytes32_t const value_bytes32 = value;
                if (value_bytes32 == monad::bytes32_t{}) {
                    // skip setting starting storage to zero to avoid pointless
                    // deletion
                    continue;
                }
                EXPECT_EQ(
                    state.set_storage(
                        account_address, key_bytes32, value_bytes32),
                    EVMC_STORAGE_ADDED);
            }
        }
    }
}

MONAD_TEST_NAMESPACE_END
