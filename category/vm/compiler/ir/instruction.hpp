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
#include <category/vm/core/assert.h>

#include <evmc/evmc.hpp>

#include <cstdint>
#include <format>
#include <limits>
#include <optional>
#include <span>
#include <tuple>
#include <vector>

namespace monad::vm::compiler
{
    enum class OpCode : std::uint8_t
    {
        Add = 0x01,
        Mul = 0x02,
        Sub = 0x03,
        Div = 0x04,
        SDiv = 0x05,
        Mod = 0x06,
        SMod = 0x07,
        AddMod = 0x08,
        MulMod = 0x09,
        Exp = 0x0A,
        SignExtend = 0x0B,
        Lt = 0x10,
        Gt = 0x11,
        SLt = 0x12,
        SGt = 0x13,
        Eq = 0x14,
        IsZero = 0x15,
        And = 0x16,
        Or = 0x17,
        XOr = 0x18,
        Not = 0x19,
        Byte = 0x1A,
        Shl = 0x1B,
        Shr = 0x1C,
        Sar = 0x1D,
        Clz = 0x1E,
        Sha3 = 0x20,
        Address = 0x30,
        Balance = 0x31,
        Origin = 0x32,
        Caller = 0x33,
        CallValue = 0x34,
        CallDataLoad = 0x35,
        CallDataSize = 0x36,
        CallDataCopy = 0x37,
        CodeSize = 0x38,
        CodeCopy = 0x39,
        GasPrice = 0x3A,
        ExtCodeSize = 0x3B,
        ExtCodeCopy = 0x3C,
        ReturnDataSize = 0x3D,
        ReturnDataCopy = 0x3E,
        ExtCodeHash = 0x3F,
        BlockHash = 0x40,
        Coinbase = 0x41,
        Timestamp = 0x42,
        Number = 0x43,
        Difficulty = 0x44,
        GasLimit = 0x45,
        ChainId = 0x46,
        SelfBalance = 0x47,
        BaseFee = 0x48,
        BlobHash = 0x49,
        BlobBaseFee = 0x4A,
        Pop = 0x50,
        MLoad = 0x51,
        MStore = 0x52,
        MStore8 = 0x53,
        SLoad = 0x54,
        SStore = 0x55,
        Pc = 0x58,
        MSize = 0x59,
        Gas = 0x5A,
        TLoad = 0x5C,
        TStore = 0x5D,
        MCopy = 0x5E,
        Push = 0x5F,
        Dup = 0x80,
        Swap = 0x90,
        Log = 0xA0,
        CheckReserveBalance = 0xD0,
        Create = 0xF0,
        Call = 0xF1,
        CallCode = 0xF2,
        DelegateCall = 0xF4,
        Create2 = 0xF5,
        StaticCall = 0xFA,
    };

    class Instruction
    {
    public:
        constexpr Instruction(
            std::uint32_t pc, OpCode opcode, std::uint32_t static_gas_cost,
            std::uint8_t stack_args, std::uint8_t index,
            std::uint8_t stack_increase, bool dynamic_gas);

        constexpr Instruction(
            std::uint32_t pc, OpCode opcode, runtime::uint256_t immediate_value,
            std::uint32_t static_gas_cost, std::uint8_t stack_args,
            std::uint8_t index, std::uint8_t stack_increase, bool dynamic_gas);

        constexpr runtime::uint256_t const &immediate_value() const noexcept;
        constexpr std::uint32_t pc() const noexcept;
        constexpr std::uint32_t static_gas_cost() const noexcept;
        constexpr OpCode opcode() const noexcept;
        constexpr std::uint8_t stack_args() const noexcept;
        constexpr std::uint8_t index() const noexcept;
        constexpr bool increases_stack() const noexcept;
        constexpr std::uint8_t stack_increase() const noexcept;
        constexpr bool dynamic_gas() const noexcept;

        friend constexpr bool
        operator==(Instruction const &, Instruction const &) noexcept;

    private:
        constexpr auto as_tuple() const noexcept;

        runtime::uint256_t immediate_value_;
        std::uint32_t pc_;
        std::uint32_t static_gas_cost_;
        OpCode opcode_;
        std::uint8_t stack_args_;
        std::uint8_t index_;
        std::uint8_t stack_increase_;
        bool dynamic_gas_;
    };

    /*
     * Instruction
     */

    constexpr Instruction::Instruction(
        std::uint32_t pc, OpCode op, std::uint32_t static_gas_cost,
        std::uint8_t stack_args, std::uint8_t index,
        std::uint8_t stack_increase, bool dynamic_gas)
        : Instruction(
              pc, op, 0, static_gas_cost, stack_args, index, stack_increase,
              dynamic_gas)
    {
    }

    constexpr Instruction::Instruction(
        std::uint32_t pc, OpCode op, runtime::uint256_t immediate_value,
        std::uint32_t static_gas_cost, std::uint8_t stack_args,
        std::uint8_t index, std::uint8_t stack_increase, bool dynamic_gas)
        : immediate_value_(immediate_value)
        , pc_(pc)
        , static_gas_cost_(static_gas_cost)
        , opcode_(op)
        , stack_args_(stack_args)
        , index_(index)
        , stack_increase_(stack_increase)
        , dynamic_gas_(dynamic_gas)
    {
        MONAD_VM_DEBUG_ASSERT(immediate_value == 0 || opcode() == OpCode::Push);
    }

    constexpr runtime::uint256_t const &
    Instruction::immediate_value() const noexcept
    {
        MONAD_VM_ASSERT(opcode() == OpCode::Push);
        return immediate_value_;
    }

    constexpr std::uint32_t Instruction::pc() const noexcept
    {
        return pc_;
    }

    constexpr std::uint32_t Instruction::static_gas_cost() const noexcept
    {
        return static_gas_cost_;
    }

    constexpr OpCode Instruction::opcode() const noexcept
    {
        return opcode_;
    }

    constexpr std::uint8_t Instruction::stack_args() const noexcept
    {
        return stack_args_;
    }

    constexpr std::uint8_t Instruction::index() const noexcept
    {
        MONAD_VM_ASSERT(
            opcode() == OpCode::Push || opcode() == OpCode::Swap ||
            opcode() == OpCode::Dup || opcode() == OpCode::Log);
        return index_;
    }

    constexpr bool Instruction::increases_stack() const noexcept
    {
        return stack_increase_ > 0;
    }

    constexpr std::uint8_t Instruction::stack_increase() const noexcept
    {
        return stack_increase_;
    }

    constexpr bool Instruction::dynamic_gas() const noexcept
    {
        return dynamic_gas_;
    }

    constexpr auto Instruction::as_tuple() const noexcept
    {
        return std::tie(
            immediate_value_,
            pc_,
            static_gas_cost_,
            opcode_,
            stack_args_,
            index_,
            stack_increase_,
            dynamic_gas_);
    }

    constexpr bool
    operator==(Instruction const &a, Instruction const &b) noexcept
    {
        return a.as_tuple() == b.as_tuple();
    }

    constexpr std::string_view opcode_name(OpCode op)
    {
        using enum monad::vm::compiler::OpCode;

        switch (op) {
        case Add:
            return "ADD";
        case Mul:
            return "MUL";
        case Sub:
            return "SUB";
        case Div:
            return "DIV";
        case SDiv:
            return "SDIV";
        case Mod:
            return "MOD";
        case SMod:
            return "SMOD";
        case AddMod:
            return "ADDMOD";
        case MulMod:
            return "MULMOD";
        case Exp:
            return "EXP";
        case SignExtend:
            return "SIGNEXTEND";
        case Lt:
            return "LT";
        case Gt:
            return "GT";
        case SLt:
            return "SLT";
        case SGt:
            return "SGT";
        case Eq:
            return "EQ";
        case IsZero:
            return "ISZERO";
        case And:
            return "AND";
        case Or:
            return "OR";
        case XOr:
            return "XOR";
        case Not:
            return "NOT";
        case Byte:
            return "BYTE";
        case Shl:
            return "SHL";
        case Shr:
            return "SHR";
        case Sar:
            return "SAR";
        case Clz:
            return "CLZ";
        case Sha3:
            return "KECCAK256";
        case Address:
            return "ADDRESS";
        case Balance:
            return "BALANCE";
        case Origin:
            return "ORIGIN";
        case Caller:
            return "CALLER";
        case CallValue:
            return "CALLVALUE";
        case CallDataLoad:
            return "CALLDATALOAD";
        case CallDataSize:
            return "CALLDATASIZE";
        case CallDataCopy:
            return "CALLDATACOPY";
        case CodeSize:
            return "CODESIZE";
        case CodeCopy:
            return "CODECOPY";
        case GasPrice:
            return "GASPRICE";
        case ExtCodeSize:
            return "EXTCODESIZE";
        case ExtCodeCopy:
            return "EXTCODECOPY";
        case ReturnDataSize:
            return "RETURNDATASIZE";
        case ReturnDataCopy:
            return "RETURNDATACOPY";
        case ExtCodeHash:
            return "EXTCODEHASH";
        case BlockHash:
            return "BLOCKHASH";
        case Coinbase:
            return "COINBASE";
        case Timestamp:
            return "TIMESTAMP";
        case Number:
            return "NUMBER";
        case Difficulty:
            return "PREVRANDAO";
        case GasLimit:
            return "GASLIMIT";
        case ChainId:
            return "CHAINID";
        case SelfBalance:
            return "SELFBALANCE";
        case BaseFee:
            return "BASEFEE";
        case BlobHash:
            return "BLOBHASH";
        case BlobBaseFee:
            return "BLOBBASEFEE";
        case Pop:
            return "POP";
        case MLoad:
            return "MLOAD";
        case MStore:
            return "MSTORE";
        case MStore8:
            return "MSTORE8";
        case SLoad:
            return "SLOAD";
        case SStore:
            return "SSTORE";
        case Pc:
            return "PC";
        case MSize:
            return "MSIZE";
        case Gas:
            return "GAS";
        case TLoad:
            return "TLOAD";
        case TStore:
            return "TSTORE";
        case MCopy:
            return "MCOPY";
        case Push:
            return "PUSH";
        case Dup:
            return "DUP";
        case Swap:
            return "SWAP";
        case Log:
            return "LOG";
        case CheckReserveBalance:
            return "CHECKRSERVEBALANCE";
        case Create:
            return "CREATE";
        case Call:
            return "CALL";
        case CallCode:
            return "CALLCODE";
        case DelegateCall:
            return "DELEGATECALL";
        case Create2:
            return "CREATE2";
        case StaticCall:
            return "STATICCALL";
        }

        std::unreachable();
    }
}

/*
 * Formatter Implementations
 */

template <>
struct std::formatter<monad::vm::compiler::OpCode>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::OpCode const &op, std::format_context &ctx) const
    {
        return std::format_to(ctx.out(), "{}", opcode_name(op));
    }
};

template <>
struct std::formatter<monad::vm::compiler::Instruction>
{
    constexpr auto parse(std::format_parse_context &ctx)
    {
        return ctx.begin();
    }

    auto format(
        monad::vm::compiler::Instruction const &inst,
        std::format_context &ctx) const
    {
        using enum monad::vm::compiler::OpCode;

        if (inst.opcode() == Push && inst.index() > 0) {
            return std::format_to(
                ctx.out(),
                "{}{} {}",
                inst.opcode(),
                inst.index(),
                inst.immediate_value());
        }

        if (inst.opcode() == Push || inst.opcode() == Dup ||
            inst.opcode() == Swap || inst.opcode() == Log) {
            return std::format_to(
                ctx.out(), "{}{}", inst.opcode(), inst.index());
        }

        return std::format_to(ctx.out(), "{}", inst.opcode());
    }
};
