#pragma once

#include <monad/test/config.hpp>

#include <monad/state2/state.hpp>

#include <ethash/hash_types.hpp>

#include <filesystem>
#include <vector>

#include <gmock/gmock.h>
#include <gtest/gtest.h>

#include <nlohmann/json.hpp>

#include <from_json.hpp>

MONAD_TEST_NAMESPACE_BEGIN

inline std::unordered_map<std::string, size_t> const fork_index_map = {
    {"Frontier", 0},
    {"Homestead", 1},
    // DAO and Tangerine Whistle not covered by Ethereum Tests
    {"EIP158", 4},
    {"Byzantium", 5},
    {"ConstantinopleFix", 6},
    {"Istanbul", 7},
    {"Berlin", 8},
    {"London", 9},
    {"Merge", 10},
    {"Shanghai", 11}};

class EthereumTests : public testing::Test
{
    std::filesystem::path const json_test_file_;
    std::string const suite_name_;
    std::string const test_name_;
    std::string const file_name_;
    std::optional<size_t> const fork_index_;
    std::optional<size_t> const txn_index_;

public:
    EthereumTests(
        std::filesystem::path json_test_file, std::string suite_name,
        std::string test_name, std::string file_name,
        std::optional<size_t> fork_index,
        std::optional<size_t> txn_index) noexcept
        : json_test_file_{json_test_file}
        , suite_name_{suite_name}
        , test_name_{test_name}
        , file_name_{file_name}
        , fork_index_{fork_index}
        , txn_index_(txn_index)
    {
    }

    static void register_test(
        std::string suite_name, std::filesystem::path const &file,
        std::optional<size_t> fork_index, std::optional<size_t> txn_index);

    static void register_test_files(
        std::filesystem::path const &root, std::optional<size_t> fork_index,
        std::optional<size_t> txn_index);

    void TestBody() override;

    [[nodiscard]] static StateTransitionTest load_state_test(
        nlohmann::json json, std::string suite_name, std::string test_name,
        std::string file_name, std::optional<size_t> fork_index,
        std::optional<size_t> txn_index);

    static void
    run_state_test(StateTransitionTest const &test, nlohmann::json const &json);
};

/**
 * @param fork_name
 * @return the index that corresponds to the fork_name in the `all_forks_t`
 * type
 */
[[nodiscard]] std::optional<size_t> to_fork_index(std::string_view fork_name);

template <typename TState>
void load_state_from_json(nlohmann::json const &j, TState &state)
{
    for (auto const &[j_addr, j_acc] : j.items()) {
        auto const account_address =
            evmc::from_hex<monad::address_t>(j_addr).value();

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
                nlohmann::json key_json = key;
                monad::bytes32_t key_bytes32 = key_json.get<monad::bytes32_t>();
                monad::bytes32_t value_bytes32 = value;
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
