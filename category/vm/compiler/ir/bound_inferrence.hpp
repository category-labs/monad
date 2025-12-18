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

#pragma once

#include <category/core/runtime/uint256.hpp>
#include <category/vm/compiler/ir/instruction.hpp>
#include <category/vm/compiler/ir/x86.hpp>
#include <category/vm/compiler/ir/x86/emitter.hpp>

#include <evmc/evmc.h>

#include <cstdint>

using namespace monad::vm::compiler;
using namespace monad::vm::compiler::native;

namespace
{
    // Compute bounds on the result of an instruction, if possible.
    // This function may return values greater than 256, use compute_result_bound.
    // It may also not compute the tightest possible bound for instructions that
    // are constant folded, i.e. composed only of literals.
    std::uint32_t compute_result_bound_unsafe(Emitter &emit, Instruction const &instr)
    {
        using enum OpCode;
        auto &stack = emit.get_stack();
        auto const top_index = stack.top_index();
        switch (instr.opcode()) {
        case Add:
            return std::max(
                       stack.get(top_index)->bit_upper_bound(),
                       stack.get(top_index - 1)->bit_upper_bound()) +
                   1;
        case Mul:
            return stack.get(top_index)->bit_upper_bound() *
                   stack.get(top_index - 1)->bit_upper_bound();

            // Max bound corresponds to case where denominator = 1.
            return stack.get(top_index)->bit_upper_bound();
        case Div:
        case SDiv:
            {
                // When both sides are non-negative, SDiv === Div
                auto const lhs_bound = stack.get(top_index)->bit_upper_bound();
                auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
                if (instr.opcode() == Div || (lhs_bound < 256 && rhs_bound < 256)) {
                    // Worst case: negative number divided by 1
                    return lhs_bound;
                } else {
                    // Signed division with possible negative numbers
                    return 256;
                }
            }
        case Mod:
        case SMod:
            {
                // When both sides are non-negative, SMod === Mod
                auto const lhs_bound = stack.get(top_index)->bit_upper_bound();
                auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
                if (instr.opcode() == Mod || (lhs_bound < 256 && rhs_bound < 256)) {
                    // Result is always less than the modulus.
                    return rhs_bound;
                } else {
                    // Signed modulus with possible negative numbers
                    return 256;
                }
            }
        case Sub:
            {
                // No bound can be inferred because of negative numbers unless
                // the lhs is a literal and rhs is bounded by lhs.
                auto const lhs = stack.get(top_index);
                auto const lhs_bound = lhs->bit_upper_bound();
                auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
                if (lhs->literal() && lhs_bound > rhs_bound) {
                    // Result will not go negative, worst case is subtracting 0
                    return lhs_bound;
                } else {
                    return 256;
                }
            }
        case AddMod:
        case MulMod:
            // Result is always less than the modulus.
            return stack.get(top_index - 2)->bit_upper_bound();
        case Exp:
        case SignExtend:
            // No bound can be inferred.
            return 256;
        case Lt:
        case Gt:
        case SLt:
        case SGt:
        case Eq:
        case IsZero:
            // Boolean result (0 or 1)
            return 1;
        case And:
            // Bitwise and: result bound is min of operand bounds
            return std::min(
                stack.get(top_index)->bit_upper_bound(),
                stack.get(top_index - 1)->bit_upper_bound());
        case Or:
        case XOr:
            // Bitwise or/xor: result bound is max of operand bounds
            return std::max(
                stack.get(top_index)->bit_upper_bound(),
                stack.get(top_index - 1)->bit_upper_bound());
        case Not:
            // Worst case value == 0 => result = 2^256 - 1
            return 256;
        case Byte:
            // Extracts one byte
            return 8;
        case Shl: {
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
        case Shr:
        case Sar: {
            // If we can bound the value to be non-negative, we can treat
            // sar like shr for the purpose of upper bound computation.
            auto const shift = stack.get(top_index);
            auto const val = stack.get(top_index - 1);
            auto const val_bound = val->bit_upper_bound();
            // Whether sign bits are involved in the shift
            auto const signed_shift = instr.opcode() == Sar && val_bound == 256;
            if (!signed_shift && shift->literal()) {
                // Unsigned shift with a literal shift amount
                auto const shift_lit = shift->literal()->value;
                if (shift_lit >= 256) {
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

        case Clz:
            return 9; // max 256 leading zeros
        case Sha3:
            return 256; // full word
        case Address:
            return 160; // address
        case Balance:
            return 256; // full word
        case Origin:
            return 160; // address
        case Caller:
            return 160; // address
        case CallValue:
            return 256; // full word
        case CallDataLoad:
            return 256; // full word
        case CallDataSize:
            return sizeof(monad::vm::runtime::Environment::input_data_size) * 8;
        case CallDataCopy:
            return 256; // no result pushed
        case CodeSize:
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        case CodeCopy:
            return 256; // no result pushed
        case GasPrice:
            return sizeof(evmc_tx_context::tx_gas_price) * 8;
        case ExtCodeSize:
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        case ExtCodeCopy:
            return 256; // no result pushed
        case ReturnDataSize:
            return sizeof(monad::vm::runtime::Environment::return_data_size) *
                   8;
        case ReturnDataCopy:
            return 256; // no result pushed
        case ExtCodeHash:
            return 256; // full word
        case BlockHash:
            return 256; // full word
        case Coinbase:
            return 160; // address
        case Timestamp:
            return sizeof(evmc_tx_context::block_timestamp) * 8;
        case Number:
            return sizeof(evmc_tx_context::block_number) * 8;
        case Difficulty:
            return 256; // full word
        case GasLimit:
            return sizeof(evmc_tx_context::block_gas_limit) * 8;
        case ChainId:
            return 256; // full word
        case SelfBalance:
            return 256; // full word
        case BaseFee:
            return 256; // full word
        case BlobHash:
            return 256; // full word
        case BlobBaseFee:
            return 256; // full word
        case Pop:
            return 256; // no result pushed
        case MLoad:
            return 256; // full word
        case MStore:
            return 256; // no result pushed
        case MStore8:
            return 256; // no result pushed
        case SLoad:
            return 256; // full word
        case SStore:
            return 256; // no result pushed
        case Pc:
            return sizeof(instr.pc()) * 8;
        case MSize:
            return sizeof(monad::vm::runtime::Memory::size) * 8;
        case Gas:
            return sizeof(monad::vm::runtime::Context::gas_remaining) * 8;
        case TLoad:
            return 256; // full word
        case TStore:
            return 256; // no result pushed
        case MCopy:
            return 256; // no result pushed
        case Push:
            return instr.index() * 8; // number of bits pushed
        case Dup:
            return 256; // same as the duplicated value
        case Swap:
            return 256; // same as the swapped value
        case Log:
            return 256; // no result pushed
        case Create:
            return 160; // address
        case Call:
            return 1; // success flag
        case CallCode:
            return 1; // success flag
        case DelegateCall:
            return 1; // success flag
        case Create2:
            return 160; // address
        case StaticCall:
            return 1; // success flag
        }
    }

    std::uint32_t compute_result_bound(Emitter &emit, Instruction const &instr) {
        return std::min(256u, compute_result_bound_unsafe(emit, instr));
    }
}
