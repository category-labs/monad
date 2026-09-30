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
    MONAD_VM_INSTRUCTION_CALL void
    add(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void udiv(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Boolean
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
       uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gt(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
       uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    slt(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sgt(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    eq(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
       uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Bitwise
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    or_(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void xor_(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void not_(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void byte(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shl(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    shr(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    sar(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    clz(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Data
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sha3(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void caller(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void timestamp(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void gaslimit(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Memory & Storage
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Execution Intercode
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
       uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Stack
    template <size_t N, Traits traits>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <size_t N, Traits traits>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Logging
    template <size_t N, Traits traits>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void
    log(runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // Call & Create
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    // VM Control
    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void return_(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    template <Traits traits>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    MONAD_VM_INLINE_INSTRUCTION_CALL void stop(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);

    MONAD_VM_INLINE_INSTRUCTION_CALL void invalid(
        runtime::Context &, MONAD_VM_ANALYSIS_TYPE, uint256_t const *,
        uint256_t *, int64_t, uint8_t const *MONAD_VM_TBL_TYPE);
}
