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

#include <category/core/address.hpp>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/monad_exception.hpp>
#include <category/core/runtime/uint256.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/withdrawal.hpp>
#include <category/execution/ethereum/trace/call_frame.hpp>
#include <category/rpc/utils/response_size.hpp>
#include <category/vm/evm/status_code.h>

#include <bit>
#include <cstddef>
#include <limits>
#include <span>
#include <string_view>
#include <vector>

#include <nlohmann/json.hpp>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

namespace eth_simulate_json = rpc::eth_simulateV1::json_fields;

using namespace monad;

size_t value_size(size_t const x)
{
    // The image of bit_width is [0, 64] for size_t on typical platforms, so
    // it is safe to interpret its return value as an element of size_t.
    return x == 0 ? 3 : 2 + (static_cast<size_t>(std::bit_width(x)) + 3) / 4;
}

size_t value_size(uint256_t const &x)
{
    return x == 0 ? 3 : 2 + (monad::bit_width(x) + 3) / 4;
}

size_t value_size(Address const &)
{
    return 2 * sizeof(Address) + 2 /* 0xABCDEF.... */;
}

size_t value_size(bytes32_t const &)
{
    return 2 * sizeof(bytes32_t) + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string const &x)
{
    return x.size() * 2 + 2 /* 0xABCDEF.... */;
}

size_t value_size(byte_string_fixed<8> const &)
{
    return 18; // 0x0000...
}

size_t value_size(byte_string_fixed<256> const &)
{
    return 514; // 0x0000...
}

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

size_t padded_max_size(size_t const max_size)
{
    // We use the size of the in-memory structures to bound the memory
    // consumption. This estimator is inaccurate as the RPC
    // client submits the maximum size of the CBOR response, which is
    // more compact than the in-memory structures.  Therefore we keep a
    // small amount of headroom to absorb estimator drift while still
    // bounding memory growth. We use a monotonic hyperbolic function to
    // compute the headroom, which decays percentage-wise as the
    // `max_size` increases. This is to avoid over-estimating the
    // headroom for large `max_size` values, preventing excessive
    // memory usage.
    //
    // Monotonic hyperbolic percentage in basis points:
    // S(M) = M_min + (M_max - M_min) * k / (k + M)
    // where k controls how quickly slack decays.
    constexpr size_t bps_scale = 10'000; // basis points: 100% = 10'000.
    constexpr size_t M_max = bps_scale / 2; // 50%
    constexpr size_t M_min = 1; // 0.01%
    constexpr size_t k = 4096; // 4 KiB
    // At the time of writing the BFT RPC client has M = 25'000'000 (25
    // MB). Meaning, we get roughly 2500 bytes of slack using this
    // method.

    size_t const denominator = max_size > std::numeric_limits<size_t>::max() - k
                                   ? std::numeric_limits<size_t>::max()
                                   : max_size + k;
    size_t const slack_bps = M_min + ((M_max - M_min) * k) / denominator;

    // Computing `ceil(max_size * slack_bps / bps_scale)` using integer
    // maths.
    size_t const whole = (max_size / bps_scale) * slack_bps;
    size_t const remainder = max_size % bps_scale;
    size_t const fraction =
        (remainder * slack_bps + (bps_scale - 1)) / bps_scale;
    size_t const slack = whole + fraction;

    if (max_size > std::numeric_limits<size_t>::max() - slack) {
        return std::numeric_limits<size_t>::max();
    }
    return max_size + slack;
}

namespace rpc::eth_simulateV1
{
    size_t log_entry_size(
        Block const &block, std::vector<Receipt> const &receipts,
        std::span<std::vector<CallFrame> const> const call_frames,
        bytes32_t const &block_hash,
        std::span<bytes32_t const> const txn_hashes)
    {

        size_t carried_size =
            sizeof(nlohmann::json::object_t) +
            // Shallow size estimation for the calls field. The cost of nested
            // objects is computed below.
            eth_simulate_json::calls.size() + sizeof(nlohmann::json::value_t) +
            sizeof(nlohmann::json::array_t) +
            sizeof(nlohmann::json::object_t) * block.transactions.size();

        // Calculate the size of the nested objects within the call array.
        for (size_t tx_idx = 0; tx_idx < block.transactions.size(); ++tx_idx) {
            MONAD_ASSERT_THROW(
                call_frames[tx_idx].size() > 0,
                "call frames size must be greater than 0");

            carried_size +=
                // Field names + value sizes
                (eth_simulate_json::return_data.size() +
                 sizeof(nlohmann::json::value_t) +
                 value_size(call_frames[tx_idx][0].output)) +
                (eth_simulate_json::gas_used.size() +
                 sizeof(nlohmann::json::value_t) +
                 value_size(call_frames[tx_idx][0].gas_used)) +
                (eth_simulate_json::status.size() +
                 sizeof(nlohmann::json::value_t) +
                 3); // NOTE(dhil): Return status is always 3
                     // bytes, either 0x0 or 0x1.

            // Calculate the size of each log entry
            size_t log_index_cnt = 0;
            if (call_frames[tx_idx][0].status == MONAD_STATUS_SUCCESS) {
                carried_size += eth_simulate_json::logs.size() +
                                sizeof(nlohmann::json::array_t);
                for (auto const &log : receipts[tx_idx].logs) {
                    carried_size +=
                        sizeof(nlohmann::json::object_t) +
                        (eth_simulate_json::address.size() +
                         sizeof(nlohmann::json::value_t) +
                         value_size(log.address)) +
                        (eth_simulate_json::topics.size() +
                         sizeof(nlohmann::json::array_t) +
                         ((sizeof(nlohmann::json::value_t) +
                           sizeof(bytes32_t) * 2 + 2) *
                          log.topics.size())) +
                        (eth_simulate_json::data.size() +
                         sizeof(nlohmann::json::value_t) +
                         value_size(log.data)) +
                        (eth_simulate_json::block_number.size() +
                         sizeof(nlohmann::json::value_t) +
                         value_size(block.header.number)) +
                        (eth_simulate_json::transaction_hash.size() +
                         sizeof(nlohmann::json::value_t) +
                         value_size(txn_hashes[tx_idx])) +
                        (eth_simulate_json::transaction_index.size() +
                         sizeof(nlohmann::json::value_t) + value_size(tx_idx)) +
                        (eth_simulate_json::block_hash.size() +
                         sizeof(nlohmann::json::value_t) +
                         value_size(block_hash)) +
                        (eth_simulate_json::log_index.size() +
                         sizeof(nlohmann::json::value_t) +
                         value_size(log_index_cnt++)) +
                        (eth_simulate_json::removed.size() +
                         sizeof(nlohmann::json::value_t) + sizeof(bool));
                }
            }
            else {
                constexpr size_t error_term_size =
                    sizeof(nlohmann::json::object_t) +
                    2 * sizeof(nlohmann::json::value_t) +
                    eth_simulate_json::error.size() +
                    eth_simulate_json::message.size() +
                    eth_simulate_json::execution_reverted.size();
                carried_size += error_term_size;
            }
        }

        carried_size +=
            (eth_simulate_json::hash.size() + sizeof(nlohmann::json::value_t) +
             value_size(block_hash)) +
            (eth_simulate_json::parent_hash.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.parent_hash)) +
            (eth_simulate_json::sha3_uncles.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.ommers_hash)) +
            (eth_simulate_json::miner.size() + sizeof(nlohmann::json::value_t) +
             value_size(block.header.beneficiary)) +
            (eth_simulate_json::size.size() + sizeof(nlohmann::json::value_t) +
             // NOTE(dhil): The block size is calculated later, however, its
             // size is bounded by size_t. This is a conservative estimate which
             // likely overestimates the size of the field by 10-12 bytes or so.
             value_size(std::numeric_limits<size_t>::max())) +
            (eth_simulate_json::state_root.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.state_root)) +
            (eth_simulate_json::transactions_root.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.transactions_root)) +
            (eth_simulate_json::receipts_root.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.receipts_root)) +
            (eth_simulate_json::withdrawals_root.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.withdrawals_root.value_or(NULL_HASH))) +
            (eth_simulate_json::logs_bloom.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.logs_bloom)) +
            (eth_simulate_json::difficulty.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.difficulty)) +
            (eth_simulate_json::number.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.number)) +
            (eth_simulate_json::gas_limit.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.gas_limit)) +
            (eth_simulate_json::gas_used.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.gas_used)) +
            (eth_simulate_json::timestamp.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.timestamp)) +
            (eth_simulate_json::extra_data.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.extra_data)) +
            (eth_simulate_json::mix_hash.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.prev_randao)) +
            (eth_simulate_json::nonce.size() + sizeof(nlohmann::json::value_t) +
             value_size(block.header.nonce)) +
            (eth_simulate_json::base_fee_per_gas.size() +
             sizeof(nlohmann::json::value_t) +
             value_size(block.header.base_fee_per_gas.value_or(0))) +
            (eth_simulate_json::uncles.size() +
             sizeof(nlohmann::json::array_t) +
             block.ommers.size() * (sizeof(nlohmann::json::value_t) +
                                    sizeof(bytes32_t) * 2 + 2)) +
            (eth_simulate_json::transactions.size() +
             sizeof(nlohmann::json::array_t) +
             (sizeof(nlohmann::json::value_t) + sizeof(bytes32_t) * 2 + 2) *
                 txn_hashes.size()) +
            (eth_simulate_json::withdrawals.size() +
             sizeof(nlohmann::json::array_t));

        for (auto const &withdrawal :
             block.withdrawals.value_or(std::vector<Withdrawal>{})) {
            carried_size +=
                (sizeof(nlohmann::json::object_t) +
                 (eth_simulate_json::index.size() +
                  sizeof(nlohmann::json::value_t) +
                  value_size(withdrawal.index)) +
                 (eth_simulate_json::validator_index.size() +
                  sizeof(nlohmann::json::value_t) +
                  value_size(withdrawal.validator_index)) +
                 (eth_simulate_json::amount.size() +
                  sizeof(nlohmann::json::value_t) +
                  value_size(withdrawal.amount)) +
                 (eth_simulate_json::recipient.size() +
                  sizeof(nlohmann::json::value_t) +
                  value_size(withdrawal.recipient)));
        }

        return carried_size;
    }
}

MONAD_NAMESPACE_END
