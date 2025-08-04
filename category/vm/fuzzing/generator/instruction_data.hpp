#pragma once

#include <category/vm/evm/opcodes.hpp>

#include <array>

namespace monad::vm::fuzzing
{
    using enum monad::vm::compiler::EvmOpCode;

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

    constexpr auto uncommon_non_terminators = std::array{
        BALANCE,  BLOBHASH,    BLOCKHASH,   CALLDATACOPY, CALLDATALOAD,
        CODECOPY, EXTCODECOPY, EXTCODEHASH, EXTCODESIZE,  LOG0,
        LOG1,     LOG2,        LOG3,        LOG4,         MCOPY,
        MLOAD,    MSTORE,      MSTORE8,     SELFBALANCE,  SHA3,
        SLOAD,    SSTORE,      TLOAD,       TSTORE,
    };

    // Note DIFFICULTY == PREVRANDAO
    constexpr auto common_non_terminators = std::array{
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
        SWAP16,
    };

    constexpr auto terminators = std::array{
        STOP,
        REVERT,
        RETURN,
        JUMPDEST,
        JUMPI,
        JUMP,
        SELFDESTRUCT,
    };

    constexpr auto exit_terminators = std::array{
        STOP,
        REVERT,
        RETURN,
        SELFDESTRUCT,
    };

    constexpr bool is_exit_terminator(std::uint8_t opcode) noexcept
    {
        return std::find(
                   exit_terminators.begin(), exit_terminators.end(), opcode) !=
               exit_terminators.end();
    }

    static_assert(is_exit_terminator(STOP));

    constexpr auto jump_terminators = std::array{
        JUMP,
        JUMPI,
        JUMPDEST,
    };

    std::vector<std::uint8_t> const &
    memory_operands(std::uint8_t const opcode) noexcept;

    bool uses_memory(std::uint8_t const opcode) noexcept;
}
