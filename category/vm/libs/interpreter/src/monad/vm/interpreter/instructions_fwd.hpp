#include <monad/vm/interpreter/types.hpp>
#include <monad/vm/runtime/types.hpp>

#include <evmc/evmc.h>

#include <cstdint>

namespace monad::vm::interpreter
{
    // Arithmetic
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    add(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    mul(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    sub(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void udiv(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void sdiv(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void umod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void smod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void addmod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void mulmod(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    exp(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void signextend(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Boolean
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    lt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    gt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    slt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    sgt(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    eq(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void iszero(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Bitwise
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void and_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    or_(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void xor_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void not_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void byte(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    shl(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    shr(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    sar(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Data
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void sha3(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void address(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void balance(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void origin(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void caller(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void callvalue(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void calldataload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void calldatasize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void calldatacopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void codesize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void codecopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void gasprice(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void extcodesize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void extcodecopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void returndatasize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void returndatacopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void extcodehash(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void blockhash(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void coinbase(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void timestamp(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void number(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void prevrandao(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void gaslimit(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void chainid(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void selfbalance(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void basefee(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void blobhash(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void blobbasefee(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Memory & Storage
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void mload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void mstore(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void mstore8(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void mcopy(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void sstore(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void sload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void tstore(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void tload(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Execution Intercode
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    pc(runtime::Context &, Intercode const &, runtime::uint256_t const *,
       runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void msize(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    gas(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Stack
    template <std::size_t N, evmc_revision Rev>
        requires(N <= 32)
    MONAD_VM_INSTRUCTION_CALL void push(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void
    pop(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <std::size_t N, evmc_revision Rev>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void
    dup(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <std::size_t N, evmc_revision Rev>
        requires(N >= 1)
    MONAD_VM_INSTRUCTION_CALL void swap(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void jump(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void jumpi(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void jumpdest(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Logging
    template <std::size_t N, evmc_revision Rev>
        requires(N <= 4)
    MONAD_VM_INSTRUCTION_CALL void
    log(runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // Call & Create
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void create(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void call(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void callcode(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void delegatecall(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void create2(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void staticcall(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    // VM Control
    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void return_(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void revert(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    template <evmc_revision Rev>
    MONAD_VM_INSTRUCTION_CALL void selfdestruct(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    MONAD_VM_INSTRUCTION_CALL inline void stop(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);

    MONAD_VM_INSTRUCTION_CALL inline void invalid(
        runtime::Context &, Intercode const &, runtime::uint256_t const *,
        runtime::uint256_t *, std::int64_t, std::uint8_t const *);
}
