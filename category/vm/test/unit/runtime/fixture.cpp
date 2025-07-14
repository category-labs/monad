#include "fixture.hpp"

#include <monad/vm/runtime/allocator.hpp>
#include <monad/vm/runtime/transmute.hpp>
#include <monad/vm/runtime/types.hpp>
#include <monad/vm/runtime/uint256.hpp>

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

    std::basic_string_view<uint8_t> RuntimeTest::result_data()
    {
        auto output_size = call_return_data_.size();
        auto *output_data =
            reinterpret_cast<std::uint8_t *>(std::malloc(output_size));
        std::memcpy(output_data, call_return_data_.data(), output_size);
        return {output_data, output_size};
    }
}
