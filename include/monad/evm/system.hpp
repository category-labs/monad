#pragma once

#include <monad/evm/call_parameters.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/execution_state.hpp>
#include <monad/evm/fee_schedule.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/execution/evm.hpp>
#include <monad/execution/precompiles.hpp>
#include <monad/state3/state.hpp>

MONAD_EVM_NAMESPACE_BEGIN

// template <Revision rev, Opcode op>
//     requires(op == Opcode::CREATE || op == Opcode::CREATE2)
// Status create_impl(StackPointer sp, ExecutionState &state) noexcept
//{
//     if (!state.env.can_modify_state) {
//         return Status::StaticModeViolation;
//     }
//
//     auto const &value = sp.pop();
//     auto const &offset = sp.pop();
//     auto const &size = sp.pop();
//     auto const &salt = (op == OP_CREATE2) ? sp.pop() : uint256{};
//
//     state.last_return_data.clear();
//
//     BOOST_OUTCOME_TRY(
//         auto const grow_cost,
//         state.mstate.memory.grow_if_needed(
//             state.mstate.gas_left, offset, size));
//     MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
//     MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());
//
//     state.mstate.gas_left -= grow_cost;
//
//     auto const offset_z = static_cast<size_t>(offset);
//     auto const size_z = static_cast<size_t>(size);
//
//     // EIP-3860
//     if (rev >= Revision::Shanghai && size_z > 0xC000) {
//         sp.push(0);
//         return Status::OutOfGas;
//     }
//
//     auto const word_cost = [&] {
//         uint64_t cost = 0;
//         // EIP-3860
//         if constexpr (rev >= Revision::Shanghai) {
//             cost += 2;
//         }
//         if constexpr (op == Opcode::CREATE2) {
//             cost += keccak256_cost_per_word;
//         }
//     }();
//
//     auto const init_code_cost = num_words(size_z) * word_cost;
//     if (state.mstate.gas_left < init_code_cost) {
//         sp.push(0);
//         return Status::OutOfGas;
//     }
//
//     state.mstate.gas_left -= init_code_cost;
//
//     // See EIP-3860 for mention of the below two "light checks"
//     if (state.env.depth >= 1024) {
//         sp.push(0);
//         return Status::Success;
//     }
//
//     if (value && intx::be::load<uint256>(
//                      state.sstate.get_balance(state.env.address)) < value) {
//         sp.push(0);
//         return Status::Success;
//     }
//
//     // auto msg = evmc_message{};
//     // msg.gas = gas_left;
//
//     // EIP-150
//     if constexpr (rev >= EVMC_TANGERINE_WHISTLE) {
//         msg.gas = msg.gas - msg.gas / 64;
//     }
//
//     // msg.kind = (op == OP_CREATE) ? EVMC_CREATE : EVMC_CREATE2;
//     // if (size_z > 0) {
//     //     // offset_z may be garbage if size_z == 0.
//     //     msg.input_data = &state.memory[offset_z];
//     //     msg.args_size_z = size_z;
//     // }
//     // msg.sender = state.msg->recipient;
//     // msg.depth = state.msg->depth + 1;
//     // msg.create2_salt = intx::be::store<evmc::bytes32>(salt);
//     // msg.value = intx::be::store<evmc::uint256be>(value);
//
//     // auto const result = state.host.call(msg);
//     // gas_left -= msg.gas - result.gas_left;
//     // state.gas_refund += result.gas_refund;
//
//     // state.return_data.assign(result.output_data, result.ret_size_z);
//     // if (result.status_code == EVMC_SUCCESS) {
//     //     sp.top() = intx::be::load<uint256>(result.create_address);
//     // }
//
//     // return {EVMC_SUCCESS, gas_left};
// }
//

template <Revision rev, Opcode op>
    requires(
        op == Opcode::CALL || op == Opcode::CALLCODE ||
        op == Opcode::DELEGATECALL || op == Opcode::STATICCALL)
std::optional<std::tuple<CallParameters, size_t, size_t>>
pre_call(StackPointer &sp, ExecutionState &state, Status &status)
{
    // TODO: remove once we test recursions
    MONAD_ASSERT(state.env.depth == 0);

    auto const gas = sp.pop();
    auto const address = intx::be::trunc<Address>(sp.pop());
    auto const value =
        (op == Opcode::STATICCALL || op == Opcode::DELEGATECALL) ? 0 : sp.pop();
    auto const args_offset = sp.pop();
    auto const args_size = sp.pop();
    auto const ret_offset = sp.pop();
    auto const ret_size = sp.pop();

    state.last_return_data.clear();

    // EIP-2929
    if constexpr (rev >= Revision::Berlin) {
        if (!state.sstate.access_account(address)) {
            constexpr auto cost = additional_cold_account_access_cost<rev>;
            if (state.mstate.gas_left < cost) {
                status = Status::OutOfGas;
                return std::nullopt;
            }
            state.mstate.gas_left -= cost;
        }
    }

    status = state.mstate.memory.grow_if_needed(
        state.mstate.gas_left, args_offset, args_size);
    if (status != Status::Success) {
        return std::nullopt;
    }

    status = state.mstate.memory.grow_if_needed(
        state.mstate.gas_left, ret_offset, ret_size);
    if (status != Status::Success) {
        return std::nullopt;
    }

    if constexpr (op == Opcode::CALL) {
        // Note: not checking CALLCODE here to match geth behavior. Also,
        // CALLCODE is depracated in solidity 0.5
        // https://github.com/ethereum/go-ethereum/blob/8321fe2fda0b44d6df3750bcee28b8627525173b/core/vm/instructions.go#L686
        if (value && !state.env.can_modify_state) {
            status = Status::StaticModeViolation;
            return std::nullopt;
        }
    }

    auto const cost = [&] {
        uint64_t ret = value ? call_value_cost : 0;
        if constexpr (op == Opcode::CALL) {
            if ((value || rev < Revision::SpuriousDragon) &&
                !state.sstate.state().account_exists(address)) {
                ret += new_account_cost;
            }
        }
        return ret;
    }();
    if (state.mstate.gas_left < cost) {
        status = Status::OutOfGas;
        return std::nullopt;
    }
    state.mstate.gas_left -= cost;

    MONAD_ASSERT(gas <= std::numeric_limits<uint64_t>::max());
    auto gas_u = static_cast<uint64_t>(gas);
    // EIP-150
    if constexpr (rev >= Revision::TangerineWhistle) {
        gas_u =
            std::min(gas_u, state.mstate.gas_left - state.mstate.gas_left / 64);
    }
    else if (state.mstate.gas_left < gas_u) {
        status = Status::OutOfGas;
        return std::nullopt;
    }
    if (value) {
        gas_u += call_stipend;
        state.mstate.gas_left += call_stipend;
    }

    // See EIP-3860 for mention of the below two "light checks"
    // and f0s: System Operations in YP
    if (state.env.depth >= 1024) {
        status = Status::Success;
        return std::nullopt;
    }
    if (value && intx::be::load<uint256_t>(state.sstate.state().get_balance(
                     state.env.address)) < value) {
        status = Status::Success;
        return std::nullopt;
    }

    MONAD_ASSERT(args_offset <= std::numeric_limits<size_t>::max());
    MONAD_ASSERT(args_size <= std::numeric_limits<size_t>::max());
    auto const args_offset_z = static_cast<size_t>(args_offset);
    auto const args_size_z = static_cast<size_t>(args_size);
    auto const params = CallParameters{
        .sender =
            op == Opcode::DELEGATECALL ? state.env.sender : state.env.address,
        .origin = state.env.origin,
        .recipient = (op == Opcode::CALL || op == Opcode::STATICCALL)
                         ? address
                         : state.env.address,
        .code_address = address,
        .gas = gas_u,
        .value = op == Opcode::DELEGATECALL ? state.env.value : value,
        .gas_price = state.env.gas_price,
        .input_data =
            args_size_z ? state.mstate.memory.substr(args_offset_z, args_size_z)
                        : byte_string_view{},
        .depth = state.env.depth + 1,
        .can_modify_state =
            op == Opcode::STATICCALL ? false : state.env.can_modify_state};

    status = pre_call2<op>(params, state.sstate);
    if (status != Status::Success) {
        return std::nullopt;
    }

    MONAD_ASSERT(ret_offset <= std::numeric_limits<size_t>::max());
    MONAD_ASSERT(ret_size <= std::numeric_limits<size_t>::max());
    return std::make_tuple(
        params, static_cast<size_t>(ret_offset), static_cast<size_t>(ret_size));
}

// TODO: remove
template <Opcode op>
Status pre_call2(CallParameters const &params, SystemState &sstate)
{
    sstate.state().push();

    if constexpr (op != Opcode::DELEGATECALL) {
        if (auto const status = transfer_call_balances(params, sstate);
            status != Status::Success) {
            sstate.state().pop_reject();
            return status;
        }
    }

    if constexpr (op == Opcode::CALL || op == Opcode::STATICCALL) {
        if (!params.can_modify_state) {
            // eip-161: trigger a touch for transfer of zero balance
            sstate.state().touch(params.recipient);
        }
    }

    return Status::Success;
}

// done regardless
// TODO: remove
inline void post_call1(ExecutionState &substate, Status const status)
{
    if (status != Status::Success && status != Status::Revert) {
        substate.mstate.gas_left = 0;
    }

    if (status != Status::Success) {
        substate.gas_refund = 0;
    }
}

// done regardless
// TODO: remove
inline void post_call2(ExecutionState &state, Status const status)
{
    if (status == Status::Success) {
        state.sstate.state().pop_accept();
    }
    else {
        bool const ripemd_touched =
            state.sstate.state().is_touched(ripemd_address);
        state.sstate.state().pop_reject();
        if (MONAD_UNLIKELY(ripemd_touched)) {
            // YP K.1. Deletion of an Account Despite Out-of-gas.
            state.sstate.state().touch(ripemd_address);
        }
    }
}

// only done for inner call (depth > 0)
// TODO: make this take less arguments
inline void post_call3(
    StackPointer sp, ExecutionState &state, uint64_t const gas_left,
    int64_t const gas_refund, byte_string_view const output, Status &status,
    size_t const gas, size_t const ret_offset, size_t const ret_size)
{
    MONAD_ASSERT(status == Status::Success || gas_refund == 0);
    MONAD_ASSERT(
        status == Status::Success || status == Status::Revert || gas_left == 0);

    state.last_return_data = output;
    sp.push(status == Status::Success);

    if (auto const copy_size = std::min(ret_size, output.size());
        copy_size > 0) {
        state.mstate.memory.replace(ret_offset, copy_size, output);
    }

    auto const gas_used = gas - gas_left;
    state.mstate.gas_left -= gas_used;
    state.gas_refund += gas_refund;
    status = Status::Success;
}

template <Status status>
Status halt(StackPointer sp, ExecutionState &state)
{
    auto const &offset = sp.pop();
    auto const &size = sp.pop();

    auto const grow_status =
        state.mstate.memory.grow_if_needed(state.mstate.gas_left, offset, size);
    if (grow_status != Status::Success) {
        return grow_status;
    }
    MONAD_ASSERT(offset <= std::numeric_limits<size_t>::max());
    MONAD_ASSERT(size <= std::numeric_limits<size_t>::max());

    if (size) {
        state.return_data = state.mstate.memory.substr(
            static_cast<size_t>(offset), static_cast<size_t>(size));
    }
    return status;
}

MONAD_EVM_NAMESPACE_END
