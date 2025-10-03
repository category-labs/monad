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
#include <category/vm/runtime/types.hpp>
#include <test/vm/untyped_ir_interpreter/types.hpp>

#include <evmc/evmc.h>

#include <cstdint>

namespace monad::vm::interpreter
{
    // Arithmetic
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    add(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void udiv(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &, IntercodeUntypedIR const &,
       runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
       std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gt(runtime::Context &, IntercodeUntypedIR const &,
       runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
       std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    slt(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sgt(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    eq(runtime::Context &, IntercodeUntypedIR const &,
       runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
       std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    or_(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void xor_(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void not_(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void byte(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shl(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shr(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sar(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Data
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sha3(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void caller(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void timestamp(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gaslimit(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Memory & Storage
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Execution IntercodeUntypedIR
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &, IntercodeUntypedIR const &,
       runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
       std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Stack
    template <std::size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <std::size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <std::size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Logging
    template <std::size_t N, Traits traits>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void
    log(runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // Call & Create
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    // VM Control
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void return_(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    MONAD_VM_INSTRUCTION_CALL inline void stop(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);

    MONAD_VM_INSTRUCTION_CALL inline void invalid(
        runtime::Context &, IntercodeUntypedIR const &,
        runtime::uint256_t const *, runtime::uint256_t *, std::int64_t, bool,
        std::uint8_t const *);
}
