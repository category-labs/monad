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

#include <boost/fiber/future/future.hpp>
#include <boost/outcome/try.hpp>
#include <category/core/assert.h>
#include <category/execution/ethereum/chain/chain.hpp>
#include <category/execution/ethereum/core/contract/abi_signatures.hpp>
#include <category/execution/ethereum/core/transaction.hpp>
#include <category/execution/ethereum/event/record_txn_events.hpp>
#include <category/execution/ethereum/metrics/block_metrics.hpp>
#include <category/execution/ethereum/state2/block_state.hpp>
#include <category/execution/ethereum/state3/state.hpp>
#include <category/execution/ethereum/trace/call_tracer.hpp>
#include <category/execution/ethereum/trace/event_trace.hpp>
#include <category/execution/ethereum/validate_transaction.hpp>
#include <category/execution/monad/execute_system_transaction.hpp>
#include <category/execution/monad/staking/staking_contract.hpp>
#include <category/execution/monad/staking/util/constants.hpp>
#include <category/execution/monad/staking/util/staking_error.hpp>
#include <category/execution/monad/validate_system_transaction.hpp>
#include <category/vm/evm/explicit_traits.hpp>
#include <category/vm/evm/traits.hpp>

#include <optional>

MONAD_ANONYMOUS_NAMESPACE_BEGIN

struct SyscallSelector
{
    static constexpr uint32_t REWARD =
        abi_encode_selector("syscallReward(address)");
    static constexpr uint32_t SNAPSHOT =
        abi_encode_selector("syscallSnapshot()");
    static constexpr uint32_t ON_EPOCH_CHANGE =
        abi_encode_selector("syscallOnEpochChange(uint64)");
};

static_assert(SyscallSelector::REWARD == 0x791bdcf3);
static_assert(SyscallSelector::SNAPSHOT == 0x157eeb21);
static_assert(SyscallSelector::ON_EPOCH_CHANGE == 0x1d4e9f02);

MONAD_ANONYMOUS_NAMESPACE_END

MONAD_NAMESPACE_BEGIN

using BOOST_OUTCOME_V2_NAMESPACE::success;

template <Traits traits>
ExecuteSystemTransaction<traits>::ExecuteSystemTransaction(
    Chain const &chain, uint64_t const i, Transaction const &tx,
    Address const &sender, BlockHeader const &header, BlockState &block_state,
    BlockMetrics &block_metrics, boost::fibers::future<void> &prev,
    CallTracerBase &call_tracer)
    : chain_{chain}
    , i_{i}
    , tx_{tx}
    , sender_{sender}
    , header_{header}
    , block_state_{block_state}
    , block_metrics_{block_metrics}
    , prev_{prev}
    , call_tracer_{call_tracer}
{
    record_txn_header_events(static_cast<uint32_t>(i), tx, sender, {});
}

template <Traits traits>
Result<Receipt> ExecuteSystemTransaction<traits>::operator()()
{
    TRACE_TXN_EVENT(StartTxn);

    BOOST_OUTCOME_TRY(static_validate_system_transaction<traits>(tx_, sender_));
    {
        Transaction tx = tx_;
        tx.gas_limit =
            2'000'000; // required to pass intrinsic gas validation check
        BOOST_OUTCOME_TRY(static_validate_transaction<traits>(
            tx,
            std::nullopt /* 0 base fee to pass validation */,
            std::nullopt /* 0 blob fee to pass validation */,
            chain_.get_chain_id()));
    }

    {
        TRACE_TXN_EVENT(StartExecution);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};
        state.set_original_nonce(sender_, tx_.nonce);

        call_tracer_.reset();

        auto result = execute(state);

        {
            TRACE_TXN_EVENT(StartStall);
            prev_.wait();
        }

        if (block_state_.can_merge(state)) {
            if (result.has_error()) {
                return std::move(result.error());
            }
            auto const receipt = execute_final(state);
            block_state_.merge(state);
            record_txn_output_events(
                static_cast<uint32_t>(this->i_),
                receipt,
                call_tracer_.get_call_frames(),
                state);
            return receipt;
        }
    }
    block_metrics_.inc_retries();
    {
        TRACE_TXN_EVENT(StartRetry);

        State state{block_state_, Incarnation{header_.number, i_ + 1}};

        call_tracer_.reset();

        auto result = execute(state);

        MONAD_ASSERT(block_state_.can_merge(state));
        if (result.has_error()) {
            return std::move(result.error());
        }
        auto const receipt = execute_final(state);
        block_state_.merge(state);
        record_txn_output_events(
            static_cast<uint32_t>(this->i_),
            receipt,
            call_tracer_.get_call_frames(),
            state);
        return receipt;
    }
}

template <Traits traits>
evmc_message ExecuteSystemTransaction<traits>::to_message() const
{
    evmc_message msg{
        .kind = EVMC_CALL,
        .flags = 0,
        .depth = 0,
        .gas = 0,
        .recipient = *tx_.to,
        .sender = sender_,
        .input_data = tx_.data.data(),
        .input_size = tx_.data.size(),
        .value = {},
        .create2_salt = {},
        .code_address = *tx_.to,
        .code = nullptr,
        .code_size = 0,
    };
    intx::be::store(msg.value.bytes, tx_.value);
    return msg;
}

template <Traits traits>
Result<void> ExecuteSystemTransaction<traits>::execute(State &state)
{
    BOOST_OUTCOME_TRY(validate_system_transaction(tx_, sender_, state));

    auto const nonce = state.get_nonce(sender_);
    state.set_nonce(sender_, nonce + 1);

    state.push();
    call_tracer_.on_enter(to_message());
    BOOST_OUTCOME_TRY(execute_staking_syscall(state, tx_.data, tx_.value));
    call_tracer_.on_exit(evmc::Result{EVMC_SUCCESS});
    state.pop_accept();

    return success();
}

template <Traits traits>
Receipt ExecuteSystemTransaction<traits>::execute_final(State &state)
{
    // always return success because these transactions can't revert.
    Receipt receipt{.status = 1u, .gas_used = 0, .type = tx_.type};
    for (auto const &log : state.logs()) {
        receipt.add_log(std::move(log));
    }
    call_tracer_.on_finish(receipt.gas_used);
    return receipt;
}

template <Traits traits>
Result<void> ExecuteSystemTransaction<traits>::execute_staking_syscall(
    State &state, byte_string_view calldata, uint256_t const &value)
{
    // creates staking account in state if it doesn't exist
    state.add_to_balance(staking::STAKING_CA, 0);

    staking::StakingContract contract(state, call_tracer_);
    if (MONAD_UNLIKELY(calldata.size() < 4)) {
        return staking::StakingError::InvalidInput;
    }

    auto const signature =
        intx::be::unsafe::load<uint32_t>(calldata.substr(0, 4).data());
    calldata.remove_prefix(4);

    switch (signature) {
    case SyscallSelector::REWARD:
        return contract.syscall_reward<traits>(calldata, value);
    case SyscallSelector::SNAPSHOT:
        return contract.syscall_snapshot(calldata, value);
    case SyscallSelector::ON_EPOCH_CHANGE:
        return contract.syscall_on_epoch_change(calldata, value);
    }
    return staking::StakingError::MethodNotSupported;
}

EXPLICIT_MONAD_TRAITS_CLASS(ExecuteSystemTransaction);

MONAD_NAMESPACE_END
