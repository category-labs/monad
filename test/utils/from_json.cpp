// Copyright (C) 2025-26 Category Labs, Inc.
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

#include "from_json.hpp"

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/hex.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <monad/test/config.hpp>

#include <evmc/evmc.h>

#include <intx/intx.hpp>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include <cstdint>

MONAD_TEST_NAMESPACE_BEGIN

monad::BlockHeader read_genesis_blockheader(nlohmann::json const &genesis_json)
{
    using namespace monad;

    BlockHeader block_header{};

    block_header.difficulty = intx::from_string<uint256_t>(
        genesis_json["difficulty"].get<std::string>());

    auto const extra_data =
        from_hex(genesis_json["extraData"].get<std::string>());
    MONAD_ASSERT(extra_data.has_value());
    block_header.extra_data = extra_data.value();

    block_header.gas_limit =
        std::stoull(genesis_json["gasLimit"].get<std::string>(), nullptr, 0);

    auto const mix_hash_byte_string =
        from_hex(genesis_json["mixHash"].get<std::string>());
    MONAD_ASSERT(mix_hash_byte_string.has_value());
    std::copy_n(
        mix_hash_byte_string.value().begin(),
        mix_hash_byte_string.value().length(),
        block_header.prev_randao.bytes);

    uint64_t const nonce{
        std::stoull(genesis_json["nonce"].get<std::string>(), nullptr, 0)};
    intx::be::unsafe::store<uint64_t>(block_header.nonce.data(), nonce);

    auto const parent_hash_byte_string =
        from_hex(genesis_json["parentHash"].get<std::string>());
    MONAD_ASSERT(parent_hash_byte_string.has_value());
    std::copy_n(
        parent_hash_byte_string.value().begin(),
        parent_hash_byte_string.value().length(),
        block_header.parent_hash.bytes);

    block_header.timestamp =
        std::stoull(genesis_json["timestamp"].get<std::string>(), nullptr, 0);

    if (genesis_json.contains("coinbase")) {
        auto const coinbase =
            from_hex(genesis_json["coinbase"].get<std::string>());
        MONAD_ASSERT(coinbase.has_value());
        std::copy_n(
            coinbase.value().begin(),
            coinbase.value().length(),
            block_header.beneficiary.bytes);
    }

    // London fork
    if (genesis_json.contains("baseFeePerGas")) {
        block_header.base_fee_per_gas = intx::from_string<uint256_t>(
            genesis_json["baseFeePerGas"].get<std::string>());
    }

    // Shanghai fork
    if (genesis_json.contains("blobGasUsed")) {
        block_header.blob_gas_used = std::stoull(
            genesis_json["blobGasUsed"].get<std::string>(), nullptr, 0);
    }
    if (genesis_json.contains("excessBlobGas")) {
        block_header.excess_blob_gas = std::stoull(
            genesis_json["excessBlobGas"].get<std::string>(), nullptr, 0);
    }
    if (genesis_json.contains("parentBeaconBlockRoot")) {
        auto const parent_beacon_block_root =
            from_hex(genesis_json["parentBeaconBlockRoot"].get<std::string>());
        MONAD_ASSERT(parent_beacon_block_root.has_value());
        auto &write_to =
            block_header.parent_beacon_block_root.emplace(bytes32_t{});
        std::copy_n(
            parent_beacon_block_root.value().begin(),
            parent_beacon_block_root.value().length(),
            write_to.bytes);
    }

    // Prague fork
    if (genesis_json.contains("requestsHash")) {
        auto const requests_hash =
            from_hex(genesis_json["requestsHash"].get<std::string>());
        MONAD_ASSERT(requests_hash.has_value());
        auto &write_to = block_header.requests_hash.emplace(bytes32_t{});
        std::copy_n(
            requests_hash.value().begin(),
            requests_hash.value().length(),
            write_to.bytes);
    }

    return block_header;
}

MONAD_TEST_NAMESPACE_END

namespace nlohmann
{

    void
    adl_serializer<monad::State>::from_json(json const &j, monad::State &state)
    {
        for (auto const &[j_addr, j_acc] : j.items()) {
            auto const account_address =
                monad::from_hex<monad::Address>(j_addr).value();

            if (j_acc.contains("code") || j_acc.contains("storage")) {
                MONAD_ASSERT(
                    j_acc.contains("code") && j_acc.contains("storage"));
                state.create_contract(account_address);
            }

            if (j_acc.contains("code")) {
                state.set_code(
                    account_address,
                    j_acc.at("code").get<monad::byte_string>());
            }

            state.add_to_balance(
                account_address, j_acc.at("balance").get<intx::uint256>());
            // we cannot use the nlohmann::json from_json<uint64_t> because
            // it does not use the strtoull implementation, whereas we need
            // it so we can turn a hex string into a uint64_t
            state.set_nonce(
                account_address,
                integer_from_json<uint64_t>(j_acc.at("nonce")));

            if (j_acc.contains("storage")) {
                MONAD_ASSERT(j_acc["storage"].is_object());
                for (auto const &[key, value] : j_acc["storage"].items()) {
                    nlohmann::json const key_json = key;
                    monad::bytes32_t const key_bytes32 =
                        key_json.get<monad::bytes32_t>();
                    monad::bytes32_t const value_bytes32 = value;
                    if (value_bytes32 == monad::bytes32_t{}) {
                        // skip setting starting storage to zero to avoid
                        // pointless deletion
                        continue;
                    }
                    MONAD_ASSERT(
                        state.set_storage(
                            account_address, key_bytes32, value_bytes32) ==
                        EVMC_STORAGE_ADDED);
                }
            }
        }
    }

} // namespace nlohmann
