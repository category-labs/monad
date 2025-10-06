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

    template <Traits traits, InstrEvalInline eval, compiler::EvmOpCode OP>
    MONAD_VM_INSTRUCTION_CALL void wrap(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr);

    template <InstrEvalInline eval>
    MONAD_VM_INSTRUCTION_CALL inline void terminator_inline(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr);

    template <Traits traits, InstrEvalInline eval>
    MONAD_VM_INSTRUCTION_CALL void terminator(
        runtime::Context &ctx, Intercode const &analysis,
        runtime::uint256_t const *stack_bottom, runtime::uint256_t *stack_top,
        std::int64_t gas_remaining, std::uint8_t const *instr_ptr);

    // Arithmetic
    void
    add(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    mul(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    sub(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void udiv(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void sdiv(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void umod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void smod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void addmod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void mulmod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void
    exp(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void signextend(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Boolean
    void
    lt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    gt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    slt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    sgt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    eq(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void iszero(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Bitwise
    void and_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    or_(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void xor_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void not_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void byte(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    shl(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    shr(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    sar(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Data
    void sha3(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void address(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void balance(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void origin(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void caller(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void callvalue(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void calldataload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void calldatasize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void calldatacopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void codesize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void codecopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void gasprice(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void extcodesize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void extcodecopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void returndatasize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void returndatacopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void extcodehash(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void blockhash(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void coinbase(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void timestamp(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void number(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void prevrandao(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void gaslimit(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void chainid(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void selfbalance(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void basefee(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void blobhash(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void blobbasefee(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Memory & Storage
    void mload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void mstore(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void mstore8(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void mcopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void sstore(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void sload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void tstore(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void tload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Execution Intercode
    void
    pc(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void msize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    gas(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Stack
    template <std::size_t N>
        requires(N <= 32)
    void push(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void
    pop(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <std::size_t N>
        requires(N >= 1)
    void
    dup(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <std::size_t N>
        requires(N >= 1)
    void swap(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    void jumpdest(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Logging
    template <std::size_t N>
        requires(N <= 4)
    void
    log(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // Call & Create
    template <Traits traits>
    void create(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void call(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void callcode(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void delegatecall(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void create2(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void staticcall(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    // VM Control
    template <Traits traits>
    void return_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void revert(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    template <Traits traits>
    void selfdestruct(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void stop(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);

    void invalid(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t &, std::uint8_t const *&);
}
