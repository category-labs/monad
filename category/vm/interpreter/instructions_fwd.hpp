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

#include <category/vm/evm/traits.hpp>
#include <category/vm/interpreter/types.hpp>
#include <category/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#include <cstdint>

namespace monad::vm::interpreter
{
    // Arithmetic
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void add(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mul(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sub(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void udiv(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void exp(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(MONAD_VM_HANDLER_TYPES);

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void lt(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gt(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void slt(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sgt(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void eq(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(MONAD_VM_HANDLER_TYPES);

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void or_(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void xor_(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void not_(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void byte(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void shl(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void shr(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sar(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void clz(MONAD_VM_HANDLER_TYPES);

    // Data
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sha3(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void caller(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void timestamp(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gaslimit(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(MONAD_VM_HANDLER_TYPES);

    // Memory & Storage
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(MONAD_VM_HANDLER_TYPES);

    // Execution Intercode
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void pc(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gas(MONAD_VM_HANDLER_TYPES);

    // Stack
    template <size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void pop(MONAD_VM_HANDLER_TYPES);

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void dup(MONAD_VM_HANDLER_TYPES);

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(MONAD_VM_HANDLER_TYPES);

    // Logging
    template <size_t N, Traits traits>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void log(MONAD_VM_HANDLER_TYPES);

    // Call & Create
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(MONAD_VM_HANDLER_TYPES);

    // VM Control
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void return_(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(MONAD_VM_HANDLER_TYPES);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(MONAD_VM_HANDLER_TYPES);

    MONAD_VM_INLINE_INSTRUCTION_CALL void stop(MONAD_VM_HANDLER_TYPES);

    MONAD_VM_INLINE_INSTRUCTION_CALL void invalid(MONAD_VM_HANDLER_TYPES);
}
