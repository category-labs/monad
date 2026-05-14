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
#include <category/core/int.hpp>
#include <category/core/result.hpp>
#include <category/execution/monad/core/monad_block.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/system_sender.hpp>
#include <category/execution/monad/validate_monad_block.hpp>
#include <category/vm/evm/explicit_traits.hpp>

#include <algorithm>
#include <array>
#include <cstdint>
#include <optional>

// TODO unstable paths between versions
#if __has_include(<boost/outcome/experimental/status-code/status-code/config.hpp>)
    #include <boost/outcome/experimental/status-code/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/status-code/generic_code.hpp>
#else
    #include <boost/outcome/experimental/status-code/config.hpp>
    #include <boost/outcome/experimental/status-code/generic_code.hpp>
#endif

#include <concepts>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

enum class SyscallKind : uint8_t
{
    Snapshot = 0,
    OnEpochChange = 1,
    Reward = 2,
    Other = 3,
};

MONAD_ANONYMOUS_NAMESPACE_END

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

    auto const classify = [](Transaction const &tx) -> SyscallKind {
        if (MONAD_UNLIKELY(tx.data.size() < 4)) {
            return SyscallKind::Other;
        }
        switch (load_be_unsafe<uint32_t>(tx.data.data())) {
        case staking::selector::SNAPSHOT:
            return SyscallKind::Snapshot;
        case staking::selector::ON_EPOCH_CHANGE:
            return SyscallKind::OnEpochChange;
        case staking::selector::REWARD:
            return SyscallKind::Reward;
        }
        return SyscallKind::Other;
    };

    constexpr uint256_t MAXIMUM_BLOCK_REWARD = 25 * staking::MON;

    std::array<bool, 3> seen{};
    std::optional<SyscallKind> last_kind;
    for (auto it = txns.begin(); it != end_system_txn; ++it) {
        auto const kind = classify(*it);
        if (MONAD_UNLIKELY(kind == SyscallKind::Other)) {
            return MonadBlockError::UnknownSystemTransaction;
        }

        if (MONAD_UNLIKELY(seen[static_cast<uint8_t>(kind)])) {
            return MonadBlockError::DuplicateSystemTransaction;
        }
        seen[static_cast<uint8_t>(kind)] = true;

        if (MONAD_UNLIKELY(last_kind.has_value() && kind < *last_kind)) {
            return MonadBlockError::SystemTransactionOutOfOrder;
        }
        last_kind = kind;

        if (kind == SyscallKind::Reward &&
            MONAD_UNLIKELY(it->value > MAXIMUM_BLOCK_REWARD)) {
            return MonadBlockError::InvalidRewardValue;
        }
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
        {MonadBlockError::SystemTransactionOutOfOrder,
         "system transaction out of order",
         {}},
        {MonadBlockError::DuplicateSystemTransaction,
         "duplicate system transaction",
         {}},
        {MonadBlockError::UnknownSystemTransaction,
         "unknown system transaction",
         {}},
        {MonadBlockError::InvalidRewardValue, "invalid reward value", {}},
    };

    return v;
}

BOOST_OUTCOME_SYSTEM_ERROR2_NAMESPACE_END
