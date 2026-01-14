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

#include <category/core/runtime/uint256.hpp>
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/compiler/ir/x86/emitter.hpp>

#include <evmc/evmc.h>

#include <cstdint>

namespace monad::vm::compiler::bound_inference
{
    using namespace monad::vm::compiler;
    using namespace monad::vm::compiler::native;

    // Compute bounds on the result of an instruction, if possible.
    // This function may return values greater than 256, use
    // compute_result_bound. It may also not compute the tightest possible bound
    // for instructions that are constant folded, i.e. composed only of
    // literals.
    template <OpCode Instr, Traits traits>
    std::uint32_t compute_result_bound(Emitter &emit)
    {
        static constexpr auto info =
            compiler::opcode_table<traits>[static_cast<std::uint8_t>(Instr)];
        auto &stack = emit.get_stack();
        auto const top_index = stack.top_index();
        using enum OpCode;
        if constexpr (Instr == Add) {
            return std::min(
                256u,
                std::max(
                    stack.get(top_index)->bit_upper_bound(),
                    stack.get(top_index - 1)->bit_upper_bound()) +
                    1);
        }
        else if constexpr (Instr == Mul) {
            return std::min(
                256u,
                stack.get(top_index)->bit_upper_bound() +
                    stack.get(top_index - 1)->bit_upper_bound());
        }
        else if constexpr (Instr == Div || Instr == SDiv) {
            // When both sides are non-negative, SDiv is the same as Div
            auto const lhs_bound = stack.get(top_index)->bit_upper_bound();
            auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
            if (Instr == Div || (lhs_bound < 256 && rhs_bound < 256)) {
                // Worst case: negative number divided by 1
                return lhs_bound;
            }
            else {
                // Signed division with possible negative numbers
                return 256;
            }
        }
        else if constexpr (Instr == Mod || Instr == SMod) {
            // When both sides are non-negative, SMod is the same as Mod
            auto const lhs_bound = stack.get(top_index)->bit_upper_bound();
            auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
            if (Instr == Mod || (lhs_bound < 256 && rhs_bound < 256)) {
                // Result is always less than the modulus.
                return rhs_bound;
            }
            else {
                // Signed modulus with possible negative numbers
                return 256;
            }
        }
        else if constexpr (Instr == Sub) {
            // No bound can be inferred because of negative numbers unless
            // the lhs is a literal and rhs is bounded by lhs.
            auto const lhs = stack.get(top_index);
            auto const lhs_bound = lhs->bit_upper_bound();
            auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
            if (lhs->literal() && lhs_bound > rhs_bound) {
                // Result will not go negative, worst case is subtracting 0
                return lhs_bound;
            }
            else {
                return 256;
            }
        }
        else if constexpr (Instr == AddMod || Instr == MulMod) {
            // Result is always less than the modulus.
            return stack.get(top_index - 2)->bit_upper_bound();
        }
        else if constexpr (Instr == Exp || Instr == SignExtend) {
            // No bound can be inferred.
            return 256;
        }
        else if constexpr (
            Instr == Lt || Instr == Gt || Instr == SLt || Instr == SGt ||
            Instr == Eq || Instr == IsZero) {
            // Boolean result (0 or 1)
            return 1;
        }
        else if constexpr (Instr == And) {
            // Bitwise and: result bound is min of operand bounds
            return std::min(
                stack.get(top_index)->bit_upper_bound(),
                stack.get(top_index - 1)->bit_upper_bound());
        }
        else if constexpr (Instr == Or || Instr == XOr) {
            // Bitwise or/xor: result bound is max of operand bounds
            return std::max(
                stack.get(top_index)->bit_upper_bound(),
                stack.get(top_index - 1)->bit_upper_bound());
        }
        else if constexpr (Instr == Not) {
            // Worst case value == 0 => result = 2^256 - 1
            return 256;
        }
        else if constexpr (Instr == Byte) {
            // Extracts one byte
            return 8;
        }
        else if constexpr (Instr == Shl) {
            // if the shift amount is a literal, we shift the bound
            // accordingly. Otherwise, assume a shl with the maximum shift
            // amount.
            auto const shift = stack.get(top_index);
            auto const shift_bound = shift->bit_upper_bound();
            auto const val = stack.get(top_index - 1);
            auto const val_bound = val->bit_upper_bound();
            if (shift->literal()) {
                auto const shift_lit = shift->literal()->value;
                if (shift_lit >= 256) {
                    return 0; // all bits shifted out of range
                }
                else {
                    // shift_lit < 256 ^ val_bound < 256 => no overflow
                    return val_bound + static_cast<std::uint32_t>(shift_lit);
                }
            }
            else {
                // shift is not a literal, assume maximum shift (bounded by
                // 2**16 - 1) to prevent overflows.
                auto const max_shift = (1u << std::min(16u, shift_bound)) - 1;
                return val_bound + max_shift;
            }
        }
        else if constexpr (Instr == Shr || Instr == Sar) {
            // If we can bound the value to be non-negative, we can treat
            // sar like shr for the purpose of upper bound computation.
            auto const shift = stack.get(top_index);
            auto const val = stack.get(top_index - 1);
            auto const val_bound = val->bit_upper_bound();
            // Whether sign bits are involved in the shift
            auto const signed_shift = Instr == Sar && val_bound == 256;
            if (!signed_shift && shift->literal()) {
                // Unsigned shift with a literal shift amount
                auto const shift_lit = shift->literal()->value;
                if (shift_lit >= 256 ||
                    static_cast<std::uint32_t>(shift_lit) >= val_bound) {
                    return 0; // All bits shifted out of range
                }
                else {
                    // Difference with SHL: subtract the shift amount
                    return val_bound - static_cast<std::uint32_t>(shift_lit);
                }
            }
            else {
                // Shift is either not a literal or the value is negative.
                // In both cases, we cannot infer a tighter bound than the
                // original value's bound
                return val_bound;
            }
        }

        else if constexpr (Instr == Clz) {
            return 9; // max 256 leading zeros
        }
        else if constexpr (Instr == Sha3) {
            return 256; // full word
        }
        else if constexpr (Instr == Address) {
            return 160; // address
        }
        else if constexpr (Instr == Balance) {
            return 256; // full word
        }
        else if constexpr (Instr == Origin) {
            return 160; // address
        }
        else if constexpr (Instr == Caller) {
            return 160; // address
        }
        else if constexpr (Instr == CallValue) {
            return 256; // full word
        }
        else if constexpr (Instr == CallDataLoad) {
            return 256; // full word
        }
        else if constexpr (Instr == CallDataSize) {
            return sizeof(monad::vm::runtime::Environment::input_data_size) * 8;
        }
        else if constexpr (Instr == CallDataCopy) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == CodeSize) {
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        }
        else if constexpr (Instr == CodeCopy) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == GasPrice) {
            return sizeof(evmc_tx_context::tx_gas_price) * 8;
        }
        else if constexpr (Instr == ExtCodeSize) {
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        }
        else if constexpr (Instr == ExtCodeCopy) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == ReturnDataSize) {
            return sizeof(monad::vm::runtime::Environment::return_data_size) *
                   8;
        }
        else if constexpr (Instr == ReturnDataCopy) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == ExtCodeHash) {
            return 256; // full word
        }
        else if constexpr (Instr == BlockHash) {
            return 256; // full word
        }
        else if constexpr (Instr == Coinbase) {
            return 160; // address
        }
        else if constexpr (Instr == Timestamp) {
            return sizeof(evmc_tx_context::block_timestamp) * 8;
        }
        else if constexpr (Instr == Number) {
            return sizeof(evmc_tx_context::block_number) * 8;
        }
        else if constexpr (Instr == Difficulty) {
            return 256; // full word
        }
        else if constexpr (Instr == GasLimit) {
            return sizeof(evmc_tx_context::block_gas_limit) * 8;
        }
        else if constexpr (Instr == ChainId) {
            return 256; // full word
        }
        else if constexpr (Instr == SelfBalance) {
            return 256; // full word
        }
        else if constexpr (Instr == BaseFee) {
            return 256; // full word
        }
        else if constexpr (Instr == BlobHash) {
            return 256; // full word
        }
        else if constexpr (Instr == BlobBaseFee) {
            return 256; // full word
        }
        else if constexpr (Instr == Pop) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == MLoad) {
            return 256; // full word
        }
        else if constexpr (Instr == MStore) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == MStore8) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == SLoad) {
            return 256; // full word
        }
        else if constexpr (Instr == SStore) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == Pc) {
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        }
        else if constexpr (Instr == MSize) {
            return sizeof(monad::vm::runtime::Memory::size) * 8;
        }
        else if constexpr (Instr == Gas) {
            return sizeof(monad::vm::runtime::Context::gas_remaining) * 8;
        }
        else if constexpr (Instr == TLoad) {
            return 256; // full word
        }
        else if constexpr (Instr == TStore) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == MCopy) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == Push) {
            return info.index * 8; // number of bits pushed
        }
        else if constexpr (Instr == Dup) {
            return stack.get(top_index + 1 - info.index)->bit_upper_bound();
        }
        else if constexpr (Instr == Swap) {
            return stack.get(top_index - info.index)->bit_upper_bound();
        }
        else if constexpr (Instr == Log) {
            return 256; // no result pushed
        }
        else if constexpr (Instr == Create) {
            return 160; // address
        }
        else if constexpr (Instr == Call) {
            return 1; // success flag
        }
        else if constexpr (Instr == CallCode) {
            return 1; // success flag
        }
        else if constexpr (Instr == DelegateCall) {
            return 1; // success flag
        }
        else if constexpr (Instr == Create2) {
            return 160; // address
        }
        else if constexpr (Instr == StaticCall) {
            return 1; // success flag
        }
        else {
            static_assert(
                false,
                "compute_result_bound not implemented for this instruction");
        }
    }
}
