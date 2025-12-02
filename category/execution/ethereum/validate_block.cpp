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

#include <category/core/assert.h>
#include <category/core/byte_string.hpp>
#include <category/core/bytes.hpp>
#include <category/core/config.hpp>
#include <category/core/keccak.hpp>
#include <category/core/likely.h>
#include <category/core/result.hpp>
#include <category/execution/ethereum/core/block.hpp>
#include <category/execution/ethereum/core/receipt.hpp>
#include <category/execution/ethereum/core/rlp/block_rlp.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/transaction_gas.hpp>
#include <category/execution/ethereum/validate_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/switch_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <evmc/evmc.h>

#include <boost/outcome/config.hpp>
// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif
#include <boost/outcome/success_failure.hpp>
#include <boost/outcome/try.hpp>

#include <cstdint>
#include <initializer_list>
#include <limits>
#include <vector>

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

Receipt::Bloom compute_bloom(std::vector<Receipt> const &receipts)
{
    Receipt::Bloom bloom{};
    for (auto const &receipt : receipts) {
        for (unsigned i = 0; i < bloom.size(); ++i) {
            bloom[i] |= receipt.bloom[i];
        }
    }
    return bloom;
}

bytes32_t compute_ommers_hash(std::vector<BlockHeader> const &ommers)
{
    if (ommers.empty()) {
        return NULL_LIST_HASH;
    }
    return to_bytes(keccak256(rlp::encode_ommers(ommers)));
}

template <Traits traits>
Result<void> static_validate_header(BlockHeaderInputs const &inputs)
{
    // YP eq. 56
    if (MONAD_UNLIKELY(inputs.gas_limit < 5000)) {
        return BlockError::InvalidGasLimit;
    }

    // EIP-1985
    if (MONAD_UNLIKELY(
            inputs.gas_limit > std::numeric_limits<int64_t>::max())) {
        return BlockError::InvalidGasLimit;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(inputs.extra_data.length() > 32)) {
        return BlockError::ExtraDataTooLong;
    }

    // EIP-1559
    if constexpr (traits::evm_rev() < EVMC_LONDON) {
        if (MONAD_UNLIKELY(inputs.base_fee_per_gas.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else if (MONAD_UNLIKELY(!inputs.base_fee_per_gas.has_value())) {
        return BlockError::MissingField;
    }

    // EIP-7685
    if constexpr (traits::evm_rev() < EVMC_PRAGUE) {
        if (MONAD_UNLIKELY(inputs.requests_hash.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else if (MONAD_UNLIKELY(!inputs.requests_hash.has_value())) {
        return BlockError::MissingField;
    }

    // EIP-4844 and EIP-4788
    if constexpr (traits::evm_rev() < EVMC_CANCUN) {
        if (MONAD_UNLIKELY(
                inputs.blob_gas_used.has_value() ||
                inputs.excess_blob_gas.has_value() ||
                inputs.parent_beacon_block_root.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else if (MONAD_UNLIKELY(
                 !inputs.blob_gas_used.has_value() ||
                 !inputs.excess_blob_gas.has_value() ||
                 !inputs.parent_beacon_block_root.has_value())) {
        return BlockError::MissingField;
    }

    // EIP-4895
    if constexpr (traits::evm_rev() < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(inputs.withdrawals_root.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else if (MONAD_UNLIKELY(!inputs.withdrawals_root.has_value())) {
        return BlockError::MissingField;
    }

    // EIP-3675
    if constexpr (traits::evm_rev() >= EVMC_PARIS) {
        if (MONAD_UNLIKELY(inputs.difficulty != 0)) {
            return BlockError::PowBlockAfterMerge;
        }

        constexpr byte_string_fixed<8> empty_nonce{
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00};
        if (MONAD_UNLIKELY(inputs.nonce != empty_nonce)) {
            return BlockError::InvalidNonce;
        }

        if (MONAD_UNLIKELY(inputs.ommers_hash != NULL_LIST_HASH)) {
            return BlockError::WrongOmmersHash;
        }
    }

    return success();
}

EXPLICIT_TRAITS(static_validate_header);

template <Traits traits>
constexpr Result<void> static_validate_ommers(InputBlock const block)
{
    // YP eq. 33
    if (compute_ommers_hash(block.ommers) != block.header_inputs.ommers_hash) {
        return BlockError::WrongOmmersHash;
    }

    // EIP-3675
    if constexpr (traits::evm_rev() >= EVMC_PARIS) {
        if (MONAD_UNLIKELY(!block.ommers.empty())) {
            return BlockError::TooManyOmmers;
        }
    }

    // YP eq. 167
    if (MONAD_UNLIKELY(block.ommers.size() > 2)) {
        return BlockError::TooManyOmmers;
    }

    // Verified in go-ethereum
    if (MONAD_UNLIKELY(
            block.ommers.size() == 2 && block.ommers[0] == block.ommers[1])) {
        return BlockError::DuplicateOmmers;
    }

    // YP eq. 167
    for (auto const &ommer : block.ommers) {
        BOOST_OUTCOME_TRY(static_validate_header<traits>(ommer));
    }

    return success();
}

template <Traits traits>
constexpr Result<void> static_validate_4844(InputBlock const block)
{
    if constexpr (traits::evm_rev() >= EVMC_CANCUN) {
        uint64_t blob_gas_used = 0;
        for (auto const &tx : block.transactions) {
            if (tx.type == TransactionType::eip4844) {
                blob_gas_used += get_total_blob_gas(tx);
            }
        }
        constexpr uint64_t MAX_BLOB_GAS_PER_BLOCK = 786432;
        if (MONAD_UNLIKELY(blob_gas_used > MAX_BLOB_GAS_PER_BLOCK)) {
            return BlockError::GasAboveLimit;
        }
        if (MONAD_UNLIKELY(
                block.header_inputs.blob_gas_used.value() != blob_gas_used)) {
            return BlockError::InvalidGasUsed;
        }
    }
    return success();
}

template <Traits traits>
constexpr Result<void> static_validate_body(InputBlock const block)
{
    // EIP-4895
    if constexpr (traits::evm_rev() < EVMC_SHANGHAI) {
        if (MONAD_UNLIKELY(block.withdrawals.has_value())) {
            return BlockError::FieldBeforeFork;
        }
    }
    else {
        if (MONAD_UNLIKELY(!block.withdrawals.has_value())) {
            return BlockError::MissingField;
        }
    }

    BOOST_OUTCOME_TRY(static_validate_ommers<traits>(block));
    BOOST_OUTCOME_TRY(static_validate_4844<traits>(block));

    return success();
}

template <Traits traits>
Result<void> static_validate_block(InputBlock const block)
{
    BOOST_OUTCOME_TRY(static_validate_header<traits>(block.header_inputs));

    BOOST_OUTCOME_TRY(static_validate_body<traits>(block));

    return success();
}

EXPLICIT_TRAITS(static_validate_block);

Result<void>
static_validate_block(evmc_revision const rev, InputBlock const block)
{
    SWITCH_EVM_TRAITS(static_validate_block, block);
    MONAD_ASSERT(false);
}

Result<void>
validate_output_header(BlockHeader const &input, BlockHeader const &output)
{
    // First, validate execution inputs.
    if (MONAD_UNLIKELY(input.ommers_hash != output.ommers_hash)) {
        return BlockError::WrongOmmersHash;
    }
    if (MONAD_UNLIKELY(input.transactions_root != output.transactions_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.withdrawals_root != output.withdrawals_root)) {
        return BlockError::WrongMerkleRoot;
    }

    // Second, validate execution outputs known before commit.

    // YP eq. 170
    if (MONAD_UNLIKELY(input.gas_used != output.gas_used)) {
        return BlockError::InvalidGasUsed;
    }

    // YP eq. 56
    if (MONAD_UNLIKELY(output.gas_used > output.gas_limit)) {
        return BlockError::GasAboveLimit;
    }

    // YP eq. 33
    if (MONAD_UNLIKELY(input.logs_bloom != output.logs_bloom)) {
        return BlockError::WrongLogsBloom;
    }

    if (MONAD_UNLIKELY(input.parent_hash != output.parent_hash)) {
        return BlockError::WrongParentHash;
    }

    // Lastly, validate execution outputs only known after commit.
    if (MONAD_UNLIKELY(input.state_root != output.state_root)) {
        return BlockError::WrongMerkleRoot;
    }
    if (MONAD_UNLIKELY(input.receipts_root != output.receipts_root)) {
        return BlockError::WrongMerkleRoot;
    }

    return success();
}

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::BlockError>::mapping> const &
quick_status_code_from_enum<monad::BlockError>::value_mappings()
{
    using monad::BlockError;

    static std::initializer_list<mapping> const v = {
        {BlockError::Success, "success", {errc::success}},
        {BlockError::GasAboveLimit, "gas above limit", {}},
        {BlockError::InvalidGasLimit, "invalid gas limit", {}},
        {BlockError::ExtraDataTooLong, "extra data too long", {}},
        {BlockError::WrongOmmersHash, "wrong ommers hash", {}},
        {BlockError::WrongParentHash, "wrong parent hash", {}},
        {BlockError::FieldBeforeFork, "field before fork", {}},
        {BlockError::MissingField, "missing field", {}},
        {BlockError::PowBlockAfterMerge, "pow block after merge", {}},
        {BlockError::InvalidNonce, "invalid nonce", {}},
        {BlockError::TooManyOmmers, "too many ommers", {}},
        {BlockError::DuplicateOmmers, "duplicate ommers", {}},
        {BlockError::InvalidOmmerHeader, "invalid ommer header", {}},
        {BlockError::WrongDaoExtraData, "wrong dao extra data", {}},
        {BlockError::WrongLogsBloom, "wrong logs bloom", {}},
        {BlockError::InvalidGasUsed, "invalid gas used", {}},
        {BlockError::WrongMerkleRoot, "wrong merkle root", {}}};

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
