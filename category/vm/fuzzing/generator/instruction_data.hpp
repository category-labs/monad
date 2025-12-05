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

#include <category/vm/evm/opcodes.hpp>

#include <array>

namespace monad::vm::fuzzing
{
    using monad::vm::compiler::EvmOpCode;
    using enum monad::vm::compiler::EvmOpCode;

    template <auto in, auto f>
    consteval auto filter()
    {
        static constexpr auto new_size = std::count_if(in.begin(), in.end(), f);
        auto out = std::array<typename decltype(in)::value_type, new_size>{};
        std::copy_if(in.begin(), in.end(), out.begin(), f);
        return out;
    }

    template <Traits traits, auto opcodes>
    consteval auto make_opcode_array()
    {
        return filter<opcodes, [](auto opcode) {
            return !is_unknown_opcode_info<traits>(opcode);
        }>();
    }

    // The following instructions are special cases in the generator:
    //   RETURNDATACOPY  (generate_returndatacopy)
    //   PUSH0 - PUSH32  (generate_push)
    //   CREATE, CREATE2 (generate_create)

    constexpr auto call_non_terminators = std::array{
        CALL,
        CALLCODE,
        DELEGATECALL,
        STATICCALL,
    };

    constexpr auto dup_non_terminator = std::array{
        DUP1,
        DUP2,
        DUP3,
        DUP4,
        DUP5,
        DUP6,
        DUP7,
        DUP8,
        DUP9,
        DUP10,
        DUP11,
        DUP12,
        DUP13,
        DUP14,
        DUP15,
        DUP16,
    };

    constexpr auto uncommon_non_terminators_all = std::array{
        BALANCE,  BLOBHASH,    BLOCKHASH,   CALLDATACOPY, CALLDATALOAD,
        CODECOPY, EXTCODECOPY, EXTCODEHASH, EXTCODESIZE,  LOG0,
        LOG1,     LOG2,        LOG3,        LOG4,         MCOPY,
        MLOAD,    MSTORE,      MSTORE8,     SELFBALANCE,  SHA3,
        SLOAD,    SSTORE,      TLOAD,       TSTORE,
    };

    // Note DIFFICULTY == PREVRANDAO
    constexpr auto common_non_terminators_all = std::array{
        ADD,        MUL,         SUB,
        DIV,        SDIV,        MOD,
        SMOD,       ADDMOD,      MULMOD,
        EXP,        SIGNEXTEND,  LT,
        GT,         SLT,         SGT,
        EQ,         ISZERO,      AND,
        OR,         XOR,         NOT,
        BYTE,       SHL,         SHR,
        SAR,        ADDRESS,     ORIGIN,
        CALLER,     CALLVALUE,   CALLDATASIZE,
        CODESIZE,   GASPRICE,    RETURNDATASIZE,
        COINBASE,   TIMESTAMP,   NUMBER,
        DIFFICULTY, GASLIMIT,    CHAINID,
        BASEFEE,    BLOBBASEFEE, POP,
        PC,         MSIZE,       GAS,
        SWAP1,      SWAP2,       SWAP3,
        SWAP4,      SWAP5,       SWAP6,
        SWAP7,      SWAP8,       SWAP9,
        SWAP10,     SWAP11,      SWAP12,
        SWAP13,     SWAP14,      SWAP15,
        SWAP16,     CLZ,
    };

    constexpr auto terminators_all = std::array{
        STOP,
        REVERT,
        RETURN,
        JUMPDEST,
        JUMPI,
        JUMP,
        SELFDESTRUCT,
    };

    constexpr auto exit_terminators_all = std::array{
        STOP,
        REVERT,
        RETURN,
        SELFDESTRUCT,
    };

    constexpr auto jump_terminators_all = std::array{
        JUMP,
        JUMPI,
        JUMPDEST,
    };

    constexpr auto uncommon_non_terminators = make_opcode_array<
        EvmTraits<EVMC_OSAKA>, uncommon_non_terminators_all>();
    constexpr auto common_non_terminators =
        make_opcode_array<EvmTraits<EVMC_OSAKA>, common_non_terminators_all>();
    constexpr auto terminators =
        make_opcode_array<EvmTraits<EVMC_OSAKA>, terminators_all>();
    constexpr auto exit_terminators =
        make_opcode_array<EvmTraits<EVMC_OSAKA>, exit_terminators_all>();
    constexpr auto jump_terminators =
        make_opcode_array<EvmTraits<EVMC_OSAKA>, jump_terminators_all>();

    constexpr bool is_exit_terminator(std::uint8_t opcode) noexcept
    {
        return std::find(
                   exit_terminators_all.begin(),
                   exit_terminators_all.end(),
                   opcode) != exit_terminators_all.end();
    }

    static_assert(is_exit_terminator(STOP));

    std::vector<std::uint8_t> const &
    memory_operands(std::uint8_t const opcode) noexcept;

    bool uses_memory(std::uint8_t const opcode) noexcept;
}
