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

#include <category/core/address.hpp>
#include <category/core/bytes.hpp>
#include <category/core/log.hpp>
#include <category/execution/ethereum/core/account.hpp>
#include <category/execution/ethereum/db/state_delta_log.hpp>
#include <category/execution/ethereum/state2/state_deltas.hpp>
#include <category/execution/ethereum/types/incarnation.hpp>
#include <category/vm/vm.hpp>

#include <nlohmann/json.hpp>

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <optional>
#include <span>
#include <sstream>
#include <string>

using namespace monad;
using namespace monad::literals;

namespace
{
    Address const ADDR_CREATED =
        0xaa00000000000000000000000000000000000001_address;
    Address const ADDR_UPDATED =
        0xbb00000000000000000000000000000000000002_address;
    Address const ADDR_DESTROYED =
        0xcc00000000000000000000000000000000000003_address;

    bytes32_t const SLOT_A =
        0x0000000000000000000000000000000000000000000000000000000000000001_bytes32;
    bytes32_t const SLOT_B =
        0x0000000000000000000000000000000000000000000000000000000000000002_bytes32;
    bytes32_t const VAL_A =
        0x0000000000000000000000000000000000000000000000000000000000000042_bytes32;
    bytes32_t const VAL_B =
        0x0000000000000000000000000000000000000000000000000000000000000099_bytes32;

    bytes32_t const CODE_HASH =
        0x1100000000000000000000000000000000000000000000000000000000000022_bytes32;
    bytes32_t const BLOCK_HASH =
        0xdeadbeef00000000000000000000000000000000000000000000000000000000_bytes32;
    bytes32_t const PARENT_HASH =
        0xcafef00d00000000000000000000000000000000000000000000000000000000_bytes32;

    Account make_account(uint64_t const nonce, uint64_t const balance)
    {
        return Account{
            .balance = uint256_t{balance},
            .code_hash = bytes32_t{},
            .nonce = nonce,
            .incarnation = Incarnation::from_int(7)};
    }

    std::string read_file(std::filesystem::path const &path)
    {
        std::ifstream f{path};
        std::stringstream ss;
        ss << f.rdbuf();
        return ss.str();
    }
}

TEST(StateDeltaLog, EmitsValidJsonForBlockWithCreateUpdateDestroy)
{
    auto const tmp = std::filesystem::temp_directory_path() /
                     "monad_state_delta_log_test.jsonl";
    std::filesystem::remove(tmp);

    state_delta_logger = create_event_tracer(tmp);
    ASSERT_NE(state_delta_logger, nullptr);

    StateDeltas const state{
        {ADDR_CREATED,
         StateDelta{
             .account = {std::nullopt, make_account(1, 100)},
             .storage = {{SLOT_A, {bytes32_t{}, VAL_A}}}}},
        {ADDR_UPDATED,
         StateDelta{
             .account = {make_account(5, 500), make_account(6, 501)},
             .storage =
                 {{SLOT_B, {VAL_A, VAL_B}},
                  // Unchanged slot — should be filtered from the JSON.
                  {SLOT_A, {VAL_A, VAL_A}}}}},
        {ADDR_DESTROYED,
         StateDelta{
             .account = {make_account(9, 900), std::nullopt}, .storage = {}}},
    };

    uint8_t const bytecode[] = {0x60, 0x00, 0x60, 0x00, 0xf3};
    Code const code{
        {CODE_HASH,
         vm::make_shared_intercode(
             std::span<uint8_t const>{bytecode, sizeof(bytecode)})}};

    log_state_deltas(
        /*block_number=*/19'000'001,
        BLOCK_HASH,
        PARENT_HASH,
        state,
        code);

    flush_logger();
    state_delta_logger = nullptr;

    auto const content = read_file(tmp);
    ASSERT_FALSE(content.empty());
    ASSERT_EQ(std::count(content.begin(), content.end(), '\n'), 1)
        << "expected exactly one JSON line";

    auto const j = nlohmann::json::parse(content);

    EXPECT_EQ(j.at("block").get<uint64_t>(), 19'000'001u);
    EXPECT_EQ(
        j.at("block_hash").get<std::string>(),
        "0xdeadbeef00000000000000000000000000000000000000000000000000000000");
    EXPECT_EQ(
        j.at("parent_hash").get<std::string>(),
        "0xcafef00d00000000000000000000000000000000000000000000000000000000");

    auto const &accounts = j.at("accounts");
    EXPECT_EQ(accounts.size(), 3u);

    auto const &created =
        accounts.at("0xaa00000000000000000000000000000000000001");
    EXPECT_TRUE(created.at("pre").is_null());
    EXPECT_EQ(created.at("post").at("nonce").get<std::string>(), "0x1");
    EXPECT_EQ(created.at("post").at("balance").get<std::string>(), "0x64");
    EXPECT_EQ(created.at("post").at("incarnation").get<std::string>(), "0x7");
    EXPECT_EQ(
        created.at("storage")
            .at(
                "0x0000000000000000000000000000000000000000000000000000000000000001")
            .at("post")
            .get<std::string>(),
        "0x0000000000000000000000000000000000000000000000000000000000000042");

    auto const &updated =
        accounts.at("0xbb00000000000000000000000000000000000002");
    EXPECT_EQ(updated.at("pre").at("nonce").get<std::string>(), "0x5");
    EXPECT_EQ(updated.at("post").at("nonce").get<std::string>(), "0x6");
    auto const &updated_storage = updated.at("storage");
    EXPECT_EQ(updated_storage.size(), 1u)
        << "unchanged slot should be filtered out";
    EXPECT_TRUE(updated_storage.contains(
        "0x0000000000000000000000000000000000000000000000000000000000000002"));
    EXPECT_FALSE(updated_storage.contains(
        "0x0000000000000000000000000000000000000000000000000000000000000001"));

    auto const &destroyed =
        accounts.at("0xcc00000000000000000000000000000000000003");
    EXPECT_EQ(destroyed.at("pre").at("nonce").get<std::string>(), "0x9");
    EXPECT_TRUE(destroyed.at("post").is_null());

    auto const &code_json = j.at("code");
    EXPECT_EQ(code_json.size(), 1u);
    EXPECT_EQ(
        code_json
            .at(
                "0x1100000000000000000000000000000000000000000000000000000000000022")
            .get<std::string>(),
        "0x60006000f3");

    std::filesystem::remove(tmp);
}

TEST(StateDeltaLog, NoLoggerIsNoOp)
{
    state_delta_logger = nullptr;

    StateDeltas const state;
    Code const code;
    // Must not crash, must not produce any side effects.
    log_state_deltas(0, bytes32_t{}, bytes32_t{}, state, code);
    SUCCEED();
}
