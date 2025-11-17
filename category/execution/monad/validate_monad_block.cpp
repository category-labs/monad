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

#include <category/core/config.hpp>
#include <category/core/result.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <algorithm>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif

#include <concepts>

MONAD_NAMESPACE_BEGIN

template <class MonadConsensusBlockHeader>
Result<void>
static_validate_consensus_header(MonadConsensusBlockHeader const &header)
{
    uint64_t const timestamp_s = uint64_t{header.timestamp_ns / 1'000'000'000};
    if (MONAD_UNLIKELY(timestamp_s != header.execution_inputs.timestamp)) {
        return MonadBlockError::TimestampMismatch;
    }

    if constexpr (std::same_as<
                      MonadConsensusBlockHeader,
                      MonadConsensusBlockHeaderV2>) {
        if (MONAD_UNLIKELY(
                uint256_t{header.base_fee} !=
                header.execution_inputs.base_fee_per_gas)) {
            return MonadBlockError::BaseFeeMismatch;
        }
    }

    return outcome::success();
}

EXPLICIT_MONAD_CONSENSUS_BLOCK_HEADER(static_validate_consensus_header);

template <Traits traits>
Result<void> static_validate_monad_body(
    std::span<Address const> const senders,
    std::span<Transaction const> const txns)
{
    MONAD_ASSERT(senders.size() == txns.size());

    if constexpr (traits::monad_rev() < MONAD_FOUR) {
        return outcome::success();
    }

    // Find the first user txn.
    auto const first_user_sender = std::find_if_not(
        senders.begin(), senders.end(), [](Address const &sender) {
            return sender == SYSTEM_SENDER;
        });

    // No other system txns should come after it.
    auto const bad_system_sender =
        std::find(first_user_sender, senders.end(), SYSTEM_SENDER);
    if (MONAD_UNLIKELY(bad_system_sender != senders.end())) {
        return MonadBlockError::SystemTransactionNotFirstInBlock;
    }

    auto const end_system_txn =
        txns.begin() + std::distance(senders.begin(), first_user_sender);
    auto const is_reward = [](Transaction const &tx) { return tx.value > 0; };

    // Find first reward txn.
    auto const first_reward_txn =
        std::find_if(txns.begin(), end_system_txn, is_reward);
    if (MONAD_UNLIKELY(first_reward_txn == end_system_txn)) {
        return outcome::success();
    }

    // No other reward txn should come after it.
    auto const another_reward =
        std::find_if(std::next(first_reward_txn), end_system_txn, is_reward);
    if (MONAD_UNLIKELY(another_reward != end_system_txn)) {
        return MonadBlockError::MultipleRewardTransactions;
    }

    // Reward should not exceed 25 MON.
    constexpr uint256_t MAXIMUM_BLOCK_REWARD = 25 * staking::MON;
    if (MONAD_UNLIKELY(first_reward_txn->value > MAXIMUM_BLOCK_REWARD)) {
        return MonadBlockError::InvalidRewardValue;
    }

    return outcome::success();
}

EXPLICIT_MONAD_TRAITS(static_validate_monad_body);

MONAD_NAMESPACE_END

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_BEGIN

std::initializer_list<
    quick_status_code_from_enum<monad::MonadBlockError>::mapping> const &
quick_status_code_from_enum<monad::MonadBlockError>::value_mappings()
{
    using monad::MonadBlockError;

    static std::initializer_list<mapping> const v = {
        {MonadBlockError::Success, "success", {errc::success}},
        {MonadBlockError::TimestampMismatch, "timestamp mismatch", {}},
        {MonadBlockError::BaseFeeMismatch, "base fee mismatch", {}},
        {MonadBlockError::SystemTransactionNotFirstInBlock,
         "system transaction not first in block",
         {}},
        {MonadBlockError::MultipleRewardTransactions,
         "multiple reward transactions",
         {}},
        {MonadBlockError::InvalidRewardValue, "invalid reward value", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
