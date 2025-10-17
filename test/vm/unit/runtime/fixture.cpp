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

#include "fixture.hpp"

#include <category/vm/runtime/allocator.hpp>
#include <category/vm/runtime/keccak.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>
#include <category/vm/runtime/uint256.hpp>

#include <evmc/evmc.h>
#include <evmc/evmc.hpp>
#include <evmc/mocked_host.hpp>

#include <array>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits>
#include <numeric>
#include <string_view>

using namespace monad::vm::runtime;

namespace monad::vm::compiler::test
{
    namespace
    {
        evmc::MockedHost init_host(std::array<evmc_bytes32, 2> &blob_hashes_)
        {
            auto host = evmc::MockedHost{};

            host.tx_context = evmc_tx_context{
                .tx_gas_price = bytes32_from_uint256(56762),
                .tx_origin = 0x000000000000000000000000000000005CA1AB1E_address,
                .block_coinbase =
                    0x00000000000000000000000000000000BA5EBA11_address,
                .block_number = 23784,
                .block_timestamp = 1733494490,
                .block_gas_limit = 30000000,
                .block_prev_randao = bytes32_from_uint256(89273),
                .chain_id = bytes32_from_uint256(2342),
                .block_base_fee = bytes32_from_uint256(389),
                .blob_base_fee = bytes32_from_uint256(98988),
                .blob_hashes = blob_hashes_.data(),
                .blob_hashes_count = blob_hashes_.size(),
                .initcodes = nullptr,
                .initcodes_count = 0,
            };

            host.block_hash = bytes32_from_uint256(
                0x105DF6064F84551C4100A368056B8AF0E491077245DAB1536D2CFA6AB78421CE_u256);

            return host;
        }
    }

    RuntimeTest::RuntimeTest()
        : blob_hashes_{bytes32_from_uint256(1), bytes32_from_uint256(2)}
        , host_{init_host(blob_hashes_)}
        , ctx_{
              .host = &host_.get_interface(),
              .context = host_.to_context(),
              .gas_remaining = std::numeric_limits<std::int64_t>::max(),
              .gas_refund = 0,
              .env =
                  {
                      .evmc_flags = 0,
                      .depth = 0,
                      .recipient =
                          0x0000000000000000000000000000000000000001_address,
                      .sender =
                          0x0000000000000000000000000000000000000002_address,
                      .value = {},
                      .create2_salt = {},
                      .input_data = &call_data_[0],
                      .code = &code_[0],
                      .return_data = {},
                      .input_data_size = sizeof(call_data_),
                      .code_size = sizeof(code_),
                      .return_data_size = 0,
                      .tx_context = host_.tx_context,
                  },
              .memory = Memory(EvmMemoryAllocator{})}
    {
        std::iota(code_.rbegin(), code_.rend(), 0);
        std::iota(call_data_.begin(), call_data_.end(), 0);
        std::iota(call_return_data_.begin(), call_return_data_.end(), 0);
    }

    evmc_result
    RuntimeTest::success_result(std::int64_t gas_left, std::int64_t gas_refund)
    {
        auto output_data = result_data();
        return {
            .status_code = EVMC_SUCCESS,
            .gas_left = gas_left,
            .gas_refund = gas_refund,
            .output_data = output_data.data(),
            .output_size = output_data.size(),
            .release = nullptr,
            .create_address = {},
            .padding = {},
        };
    }

    evmc_result RuntimeTest::create_result(
        evmc_address prog_addr, std::int64_t gas_left, std::int64_t gas_refund)
    {
        auto output_data = result_data();
        return {
            .status_code = EVMC_SUCCESS,
            .gas_left = gas_left,
            .gas_refund = gas_refund,
            .output_data = output_data.data(),
            .output_size = output_data.size(),
            .release = nullptr,
            .create_address = prog_addr,
            .padding = {},
        };
    }

    evmc_result RuntimeTest::failure_result(evmc_status_code sc)
    {
        auto output_data = result_data();
        return {
            .status_code = sc,
            .gas_left = 0,
            .gas_refund = 0,
            .output_data = output_data.data(),
            .output_size = output_data.size(),
            .release = nullptr,
            .create_address = {},
            .padding = {},
        };
    }

    void RuntimeTest::set_balance(uint256_t addr, uint256_t balance)
    {
        host_.accounts[address_from_uint256(addr)].balance =
            bytes32_from_uint256(balance);
    }

    std::span<uint8_t const> RuntimeTest::result_data()
    {
        return {call_return_data_.data(), call_return_data_.size()};
    }

    void
    RuntimeTest::add_account_at(uint256_t addr, std::span<uint8_t> const code)
    {
        auto const contract_addr = address_from_uint256(addr);
        auto const codehash = ethash::keccak256(code.data(), code.size());
        evmc::bytes32 codehash_bytes;
        std::copy(codehash.bytes, codehash.bytes + 32, codehash_bytes.bytes);
        auto const account = evmc::MockedAccount{
            .nonce = 0,
            .code = evmc::bytes(code.data(), code.size()),
            .codehash = codehash_bytes,
            .balance = {},
            .storage = {},
            .transient_storage = {},
        };
        auto const [_, inserted] =
            host_.accounts.insert({contract_addr, account});
        ASSERT_TRUE(inserted);
    }
}
