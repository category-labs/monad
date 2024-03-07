#include <monad/evm/arithmetic.hpp>
#include <monad/evm/config.hpp>
#include <monad/evm/dup.hpp>
#include <monad/evm/environmental.hpp>
#include <monad/evm/execute.hpp>
#include <monad/evm/explicit_revision.hpp>
#include <monad/evm/opcodes.hpp>
#include <monad/evm/push.hpp>
#include <monad/evm/revision.hpp>
#include <monad/evm/sha3.hpp>
#include <monad/evm/stack_memory_storage_flow.hpp>
#include <monad/evm/stack_pointer.hpp>
#include <monad/evm/status.hpp>
#include <monad/evm/system.hpp>
#include <monad/execution/precompiles.hpp>

MONAD_EVM_NAMESPACE_BEGIN

namespace
{
    struct Frame
    {
        int sp;
        uint64_t gas;
        size_t ret_offset;
        size_t ret_size;
        std::shared_ptr<ExecutionState> state;
    };

    using Frames = std::deque<Frame>;

    template <Opcode op>
    Status validate_stack(int const sp)
    {
        using Trait = Trait<op>;

        MONAD_ASSERT(sp >= -1 && sp <= 1024);

        if constexpr (Trait::stack_height_change > 0) {
            static_assert(Trait::stack_height_change == 1);
            if (MONAD_UNLIKELY(sp == 1024)) {
                return Status::StackOverflow;
            }
        }

        if constexpr (Trait::stack_height_required) {
            if (MONAD_UNLIKELY(
                    sp < 0 || (static_cast<size_t>(sp + 1) <
                               Trait::stack_height_required))) {
                return Status::StackUnderflow;
            }
        }

        return Status::Success;
    }

    template <Revision rev, Opcode op>
    Status validate(int const sp, ExecutionState const &state)
    {
        using Trait = Trait<op>;

        if constexpr (rev < Trait::since) {
            return Status::UndefinedInstruction;
        }

        if (auto const status = validate_stack<op>(sp);
            status != Status::Success) {
            return status;
        }
        else if (state.mstate.gas_left < Trait::template baseline_cost<rev>()) {
            return Status::OutOfGas;
        }
        return Status::Success;
    }

    void post_call(Frames &frames, Status &status)
    {
        auto &subframe = frames.back();
        auto &substate = *subframe.state;
        if (substate.env.depth == 0) {
            return;
        }

        auto &pframe = frames[substate.env.depth - 1];
        post_call1(substate, status);
        post_call2(*pframe.state, status);
        post_call3(
            StackPointer{pframe.state->mstate.stack + pframe.sp},
            *pframe.state,
            substate.mstate.gas_left,
            substate.gas_refund,
            substate.return_data,
            status,
            subframe.gas,
            subframe.ret_offset,
            subframe.ret_size);
        pframe.sp += 1;
    }

    template <Revision rev, Opcode op>
    void execute_opcode(Frames &frames, Status &status)
    {
        using Trait = Trait<op>;
        static_assert(Trait::pc_increment > 0);

        MONAD_ASSERT(!frames.empty());
        MONAD_ASSERT(status == Status::Success);
        auto &sp = frames.back().sp;
        auto &state = *frames.back().state;
        auto sptr = StackPointer{state.mstate.stack + sp};
        MONAD_ASSERT((state.env.depth + 1) == frames.size());

        status = validate<rev, op>(sp, state);
        if (status != Status::Success) {
            post_call(frames, status);
            frames.pop_back();
            return;
        }

        MONAD_ASSERT(
            state.mstate.gas_left >= Trait::template baseline_cost<rev>());
        state.mstate.gas_left -= Trait::template baseline_cost<rev>();

        if constexpr (
            op == Opcode::CALL || op == Opcode::CALLCODE ||
            op == Opcode::DELEGATECALL || op == Opcode::STATICCALL) {
            auto const res = pre_call<rev, op>(sptr, state, status);
            if (!res.has_value()) {
                MONAD_ASSERT(status != Status::Success);
                post_call(frames, status);
                frames.pop_back();
                return;
            }
            auto const &[params, ret_offset, ret_size] = res.value();

            if (auto const result = check_call_precompile<rev>(params);
                result.has_value()) {
                uint64_t cost;
                byte_string output;
                std::tie(status, cost, output) = result.value();

                MONAD_ASSERT(
                    status == Status::Success || (cost == 0 && output.empty()));
                post_call2(state, status);
                post_call3(
                    sptr,
                    state,
                    params.gas - cost,
                    0,
                    output,
                    status,
                    params.gas,
                    ret_offset,
                    ret_size);
                sp += Trait::stack_height_change;
            }
            else {
                frames.emplace_back(
                    -1,
                    params.gas,
                    ret_offset,
                    ret_size,
                    std::make_shared<ExecutionState>(
                        state.sstate.state(), state.env.header, params));
                static_assert(
                    Trait::stack_height_required <=
                    std::numeric_limits<int>::max());
                sp -= static_cast<int>(Trait::stack_height_required);
            }
            state.mstate.pc += Trait::pc_increment;
        }
        else {
            status = Trait::template impl<rev>(sptr, state);
            if (op == Opcode::STOP || op == Opcode::RETURN ||
                op == Opcode::SELFDESTRUCT || status != Status::Success) {
                post_call(frames, status);
                frames.pop_back();
                return;
            }
            sp += Trait::stack_height_change;
            state.mstate.pc += Trait::pc_increment;
        }
    }

}

template <Revision rev>
Status execute(std::shared_ptr<ExecutionState> const state)
{
    MONAD_ASSERT(state->mstate.pc == 0);

    std::deque<Frame> frames;
    frames.emplace_back(-1, 0ul, 0ul, 0ul, state);
    Status status = Status::Success;
    while (!frames.empty()) {
        auto const op =
            static_cast<Opcode>(frames.back().state->analysis.code.at(
                frames.back().state->mstate.pc));
        switch (op) {
#define CASE_OP(OP)                                                            \
    case (OP):                                                                 \
        execute_opcode<rev, OP>(frames, status);                               \
        break;
            CASE_OP(Opcode::STOP)
            CASE_OP(Opcode::ADD)
            CASE_OP(Opcode::SUB)
            CASE_OP(Opcode::KECCAK256)
            CASE_OP(Opcode::ADDRESS)
            CASE_OP(Opcode::ORIGIN)
            CASE_OP(Opcode::CALLER)
            CASE_OP(Opcode::CALLVALUE)
            CASE_OP(Opcode::CALLDATALOAD)
            CASE_OP(Opcode::CALLDATASIZE)
            CASE_OP(Opcode::CODESIZE)
            CASE_OP(Opcode::GASPRICE)
            CASE_OP(Opcode::POP)
            CASE_OP(Opcode::MLOAD)
            CASE_OP(Opcode::MSTORE)
            CASE_OP(Opcode::SSTORE)
            CASE_OP(Opcode::PC)
            CASE_OP(Opcode::GAS)
            CASE_OP(Opcode::PUSH1)
            CASE_OP(Opcode::PUSH2)
            CASE_OP(Opcode::PUSH3)
            CASE_OP(Opcode::PUSH4)
            CASE_OP(Opcode::PUSH5)
            CASE_OP(Opcode::PUSH6)
            CASE_OP(Opcode::PUSH7)
            CASE_OP(Opcode::PUSH8)
            CASE_OP(Opcode::PUSH9)
            CASE_OP(Opcode::PUSH10)
            CASE_OP(Opcode::PUSH11)
            CASE_OP(Opcode::PUSH12)
            CASE_OP(Opcode::PUSH13)
            CASE_OP(Opcode::PUSH14)
            CASE_OP(Opcode::PUSH15)
            CASE_OP(Opcode::PUSH16)
            CASE_OP(Opcode::PUSH17)
            CASE_OP(Opcode::PUSH18)
            CASE_OP(Opcode::PUSH19)
            CASE_OP(Opcode::PUSH20)
            CASE_OP(Opcode::PUSH21)
            CASE_OP(Opcode::PUSH22)
            CASE_OP(Opcode::PUSH23)
            CASE_OP(Opcode::PUSH24)
            CASE_OP(Opcode::PUSH25)
            CASE_OP(Opcode::PUSH26)
            CASE_OP(Opcode::PUSH27)
            CASE_OP(Opcode::PUSH28)
            CASE_OP(Opcode::PUSH29)
            CASE_OP(Opcode::PUSH30)
            CASE_OP(Opcode::PUSH31)
            CASE_OP(Opcode::PUSH32)
            CASE_OP(Opcode::DUP1)
            CASE_OP(Opcode::DUP2)
            CASE_OP(Opcode::DUP3)
            CASE_OP(Opcode::DUP4)
            CASE_OP(Opcode::DUP5)
            CASE_OP(Opcode::DUP6)
            CASE_OP(Opcode::DUP7)
            CASE_OP(Opcode::DUP8)
            CASE_OP(Opcode::DUP9)
            CASE_OP(Opcode::DUP10)
            CASE_OP(Opcode::DUP11)
            CASE_OP(Opcode::DUP12)
            CASE_OP(Opcode::DUP13)
            CASE_OP(Opcode::DUP14)
            CASE_OP(Opcode::DUP15)
            CASE_OP(Opcode::DUP16)
            CASE_OP(Opcode::CALL)
            CASE_OP(Opcode::CALLCODE)
            CASE_OP(Opcode::DELEGATECALL)
            CASE_OP(Opcode::RETURN)
            CASE_OP(Opcode::SELFDESTRUCT)
#undef CASE_OP
        default:
            MONAD_ASSERT(false); // TODO: handle this error more gracefully
        }
    }
    return status;
}

EXPLICIT_REVISION(execute);

MONAD_EVM_NAMESPACE_END
