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

    // Compute bounds on the result of an instruction.
    // It may not compute the tightest possible bound for instructions that are
    // constant folded, i.e. composed only of literals.
    std::uint32_t compute_result_bound(Instruction instr, Emitter &emit)
    {
        auto &stack = emit.get_stack();
        auto const top_index = stack.top_index();
        using enum OpCode;
        if (instr.opcode() == Add) {
            return std::min(
                256u,
                std::max(
                    stack.get(top_index)->bit_upper_bound(),
                    stack.get(top_index - 1)->bit_upper_bound()) +
                    1);
        }
        else if (instr.opcode() == Mul) {
            return std::min(
                256u,
                stack.get(top_index)->bit_upper_bound() +
                    stack.get(top_index - 1)->bit_upper_bound());
        }
        else if (instr.opcode() == Div || instr.opcode() == SDiv) {
            // When both sides are non-negative, SDiv is the same as Div
            auto const lhs_bound = stack.get(top_index)->bit_upper_bound();
            auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
            if (instr.opcode() == Div || (lhs_bound < 256 && rhs_bound < 256)) {
                // Worst case: negative number divided by 1
                return lhs_bound;
            }
            else {
                // Signed division with possible negative numbers
                return 256;
            }
        }
        else if (instr.opcode() == Mod || instr.opcode() == SMod) {
            // When both sides are non-negative, SMod is the same as Mod
            auto const lhs_bound = stack.get(top_index)->bit_upper_bound();
            auto const rhs_bound = stack.get(top_index - 1)->bit_upper_bound();
            if (instr.opcode() == Mod || (lhs_bound < 256 && rhs_bound < 256)) {
                // Result is always less than the modulus.
                return rhs_bound;
            }
            else {
                // Signed modulus with possible negative numbers
                return 256;
            }
        }
        else if (instr.opcode() == Sub) {
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
        else if (instr.opcode() == AddMod || instr.opcode() == MulMod) {
            // Result is always less than the modulus.
            return stack.get(top_index - 2)->bit_upper_bound();
        }
        else if (instr.opcode() == Exp || instr.opcode() == SignExtend) {
            // No bound can be inferred.
            return 256;
        }
        else if (
            instr.opcode() == Lt || instr.opcode() == Gt ||
            instr.opcode() == SLt || instr.opcode() == SGt ||
            instr.opcode() == Eq || instr.opcode() == IsZero) {
            // Boolean result (0 or 1)
            return 1;
        }
        else if (instr.opcode() == And) {
            // Bitwise and: result bound is min of operand bounds
            return std::min(
                stack.get(top_index)->bit_upper_bound(),
                stack.get(top_index - 1)->bit_upper_bound());
        }
        else if (instr.opcode() == Or || instr.opcode() == XOr) {
            // Bitwise or/xor: result bound is max of operand bounds
            return std::max(
                stack.get(top_index)->bit_upper_bound(),
                stack.get(top_index - 1)->bit_upper_bound());
        }
        else if (instr.opcode() == Not) {
            // Worst case value == 0 => result = 2^256 - 1
            return 256;
        }
        else if (instr.opcode() == Byte) {
            // Extracts one byte
            return 8;
        }
        else if (instr.opcode() == Shl) {
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
        else if (instr.opcode() == Shr || instr.opcode() == Sar) {
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

        else if (instr.opcode() == Clz) {
            return 9; // max 256 leading zeros
        }
        else if (instr.opcode() == Sha3) {
            return 256; // full word
        }
        else if (instr.opcode() == Address) {
            return 160; // address
        }
        else if (instr.opcode() == Balance) {
            return 256; // full word
        }
        else if (instr.opcode() == Origin) {
            return 160; // address
        }
        else if (instr.opcode() == Caller) {
            return 160; // address
        }
        else if (instr.opcode() == CallValue) {
            return 256; // full word
        }
        else if (instr.opcode() == CallDataLoad) {
            return 256; // full word
        }
        else if (instr.opcode() == CallDataSize) {
            return sizeof(monad::vm::runtime::Environment::input_data_size) * 8;
        }
        else if (instr.opcode() == CallDataCopy) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == CodeSize) {
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        }
        else if (instr.opcode() == CodeCopy) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == GasPrice) {
            return sizeof(evmc_tx_context::tx_gas_price) * 8;
        }
        else if (instr.opcode() == ExtCodeSize) {
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        }
        else if (instr.opcode() == ExtCodeCopy) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == ReturnDataSize) {
            return sizeof(monad::vm::runtime::Environment::return_data_size) *
                   8;
        }
        else if (instr.opcode() == ReturnDataCopy) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == ExtCodeHash) {
            return 256; // full word
        }
        else if (instr.opcode() == BlockHash) {
            return 256; // full word
        }
        else if (instr.opcode() == Coinbase) {
            return 160; // address
        }
        else if (instr.opcode() == Timestamp) {
            return sizeof(evmc_tx_context::block_timestamp) * 8;
        }
        else if (instr.opcode() == Number) {
            return sizeof(evmc_tx_context::block_number) * 8;
        }
        else if (instr.opcode() == Difficulty) {
            return 256; // full word
        }
        else if (instr.opcode() == GasLimit) {
            return sizeof(evmc_tx_context::block_gas_limit) * 8;
        }
        else if (instr.opcode() == ChainId) {
            return 256; // full word
        }
        else if (instr.opcode() == SelfBalance) {
            return 256; // full word
        }
        else if (instr.opcode() == BaseFee) {
            return 256; // full word
        }
        else if (instr.opcode() == BlobHash) {
            return 256; // full word
        }
        else if (instr.opcode() == BlobBaseFee) {
            return 256; // full word
        }
        else if (instr.opcode() == Pop) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == MLoad) {
            return 256; // full word
        }
        else if (instr.opcode() == MStore) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == MStore8) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == SLoad) {
            return 256; // full word
        }
        else if (instr.opcode() == SStore) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == Pc) {
            return sizeof(monad::vm::runtime::Environment::code_size) * 8;
        }
        else if (instr.opcode() == MSize) {
            return sizeof(monad::vm::runtime::Memory::size) * 8;
        }
        else if (instr.opcode() == Gas) {
            return sizeof(monad::vm::runtime::Context::gas_remaining) * 8;
        }
        else if (instr.opcode() == TLoad) {
            return 256; // full word
        }
        else if (instr.opcode() == TStore) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == MCopy) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == Push) {
            return instr.index() * 8; // number of bits pushed
        }
        else if (instr.opcode() == Dup) {
            return stack.get(top_index + 1 - instr.index())->bit_upper_bound();
        }
        else if (instr.opcode() == Swap) {
            return stack.get(top_index - instr.index())->bit_upper_bound();
        }
        else if (instr.opcode() == Log) {
            return 256; // no result pushed
        }
        else if (instr.opcode() == Create) {
            return 160; // address
        }
        else if (instr.opcode() == Call) {
            return 1; // success flag
        }
        else if (instr.opcode() == CallCode) {
            return 1; // success flag
        }
        else if (instr.opcode() == DelegateCall) {
            return 1; // success flag
        }
        else if (instr.opcode() == Create2) {
            return 160; // address
        }
        else if (instr.opcode() == StaticCall) {
            return 1; // success flag
        }
        else {
            // Default case: assume full 256-bit bound for unhandled opcodes
            return 256;
        }
    }
}
