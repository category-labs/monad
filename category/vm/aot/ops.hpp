// Copyright (C) 2025-26 Category Labs, Inc.
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

// The operations that the codes compiled ahead of time call (aot/codes.cpp,
// written by aotgen.py): each is the work of the interpreter's handler for
// the opcode, without its dispatch, its stack pointer and its gas test. A
// compiled code charges the static gas of a basic block on entry, as the x86
// compiler does; the runtime functions that read the gas left take the static
// gas of the block's later opcodes as remaining_block_base_gas.

#pragma once

#include <category/core/runtime/uint256.hpp>
#include <category/vm/evm/opcodes.hpp>
#include <category/vm/evm/traits.hpp>
#include <category/vm/runtime/call.hpp>
#include <category/vm/runtime/data.hpp>
#include <category/vm/runtime/keccak.hpp>
#include <category/vm/runtime/log.hpp>
#include <category/vm/runtime/math.hpp>
#include <category/vm/runtime/math/intrinsics.hpp>
#include <category/vm/runtime/memory.hpp>
#include <category/vm/runtime/storage.hpp>
#include <category/vm/runtime/transmute.hpp>
#include <category/vm/runtime/types.hpp>

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <initializer_list>

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // The static gas of a run of opcodes.
    template <Traits traits>
    consteval int64_t gas_of(std::initializer_list<uint8_t> const ops)
    {
        int64_t g = 0;
        for (auto const op : ops) {
            g += compiler::opcode_table<traits>[op].min_gas;
        }
        return g;
    }

    // Whether a run of opcodes needs `need` words on entry and grows the
    // stack by `grow` at most, as the generator found.
    template <Traits traits>
    consteval bool stack_bounds_are(
        std::initializer_list<uint8_t> const ops, int const need,
        int const grow)
    {
        int n = 0;
        int g = 0;
        int h = 0;
        for (auto const op : ops) {
            auto const &ci = compiler::opcode_table<traits>[op];
            n = std::max(n, static_cast<int>(ci.min_stack) - h);
            h += static_cast<int>(ci.stack_increase) -
                 static_cast<int>(ci.min_stack);
            g = std::max(g, h);
        }
        return n == need && g == grow;
    }

    template <Traits traits>
    consteval bool is_known(uint8_t const op)
    {
        return !compiler::is_unknown_opcode_info<traits>(op);
    }

    [[gnu::always_inline]] inline uint256_t from_bool(bool const b) noexcept
    {
        return uint256_t{static_cast<uint64_t>(b)};
    }

    [[gnu::always_inline]] inline bool nonzero(uint256_t const &x) noexcept
    {
        return (x[0] | x[1] | x[2] | x[3]) != 0;
    }

    // A jump's destination as a code offset, or ~0 past 2^32.
    [[gnu::always_inline]] inline uint64_t
    jump_offset(uint256_t const &x) noexcept
    {
        return MONAD_LIKELY((x[1] | x[2] | x[3] | (x[0] >> 32)) == 0)
                   ? x[0]
                   : ~uint64_t{0};
    }

    // Memory

    // The memory grown for a 32-byte access at a run-time offset that
    // reaches past it: within its capacity as the interpreter's mstore_grow
    // does it, else through expand_memory, which exits past 2^28. Returns
    // the gas left.
    template <Traits traits>
    [[gnu::noinline]] int64_t
    grow32_at(Context *const ctx, int64_t gas, uint64_t const off)
    {
        static_assert(!traits::mip_3_active());
        if (MONAD_LIKELY((off >> runtime::Memory::offset_bits) == 0)) {
            auto const offset = runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(off));
            auto const word_count =
                Context::memory_size_to_word_count(offset + runtime::bin<32>);
            auto const new_size =
                Context::word_count_to_memory_size(word_count);
            if (MONAD_LIKELY(ctx->memory.capacity >= *new_size)) {
                auto const new_cost =
                    Context::memory_cost_from_word_count<traits>(word_count);
                gas -= new_cost - ctx->memory.cost;
                if (MONAD_UNLIKELY(gas < 0)) {
                    ctx->exit(StatusCode::OutOfGas);
                }
                ctx->memory.size = *new_size;
                ctx->memory_access32_end = *new_size - 31;
                ctx->memory.cost = new_cost;
                return gas;
            }
        }
        ctx->gas_remaining = gas;
        auto const offset = ctx->get_memory_offset(uint256_t{off});
        ctx->expand_memory<traits>(offset + runtime::bin<32>);
        return ctx->gas_remaining;
    }

    // MLOAD and MSTORE at a run-time offset: high words zero and a low word
    // under memory_access32_end, as in their handlers.
    template <Traits traits>
    [[gnu::always_inline]] inline uint256_t
    mload(Context *const ctx, int64_t &gas, uint256_t const &offset)
    {
        if (MONAD_UNLIKELY((offset[1] | offset[2] | offset[3]) != 0)) {
            ctx->exit(StatusCode::OutOfGas);
        }
        if (MONAD_UNLIKELY(offset[0] >= ctx->memory_access32_end)) {
            gas = grow32_at<traits>(ctx, gas, offset[0]);
        }
        uint256_t r;
        runtime::mload_at<traits>(
            ctx,
            &r,
            runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(offset[0])));
        return r;
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void mstore(
        Context *const ctx, int64_t &gas, uint256_t const &offset,
        uint256_t const &value)
    {
        if (MONAD_UNLIKELY((offset[1] | offset[2] | offset[3]) != 0)) {
            ctx->exit(StatusCode::OutOfGas);
        }
        if (MONAD_UNLIKELY(offset[0] >= ctx->memory_access32_end)) {
            gas = grow32_at<traits>(ctx, gas, offset[0]);
        }
        runtime::mstore_at<traits>(
            ctx,
            runtime::Memory::Offset::unsafe_from(
                static_cast<runtime::Memory::Offset::rep>(offset[0])),
            &value);
    }

    // The memory grown to NEW_SIZE bytes, whose cost is NEW_COST, for a
    // 32-byte access at the constant offset OFF that reaches past it: the
    // interpreter's mstore_grow, its sizes folded. Returns the gas left.
    template <Traits traits, uint32_t OFF, uint32_t NEW_SIZE, int64_t NEW_COST>
    [[gnu::noinline]] int64_t grow32(Context *const ctx, int64_t gas)
    {
        static_assert(!traits::mip_3_active());
        static_assert(NEW_SIZE % 32 == 0 && NEW_SIZE >= OFF + 32);
        static_assert(
            NEW_COST == Context::memory_cost_from_word_count<traits>(
                            runtime::Bin<25>::unsafe_from(NEW_SIZE / 32)));
        if (MONAD_LIKELY(ctx->memory.capacity >= NEW_SIZE)) {
            gas -= NEW_COST - ctx->memory.cost;
            if (MONAD_UNLIKELY(gas < 0)) {
                ctx->exit(StatusCode::OutOfGas);
            }
            ctx->memory.size = NEW_SIZE;
            ctx->memory_access32_end = NEW_SIZE - 31;
            ctx->memory.cost = NEW_COST;
            return gas;
        }
        ctx->gas_remaining = gas;
        ctx->expand_memory<traits>(
            runtime::Memory::Offset::unsafe_from(OFF) + runtime::bin<32>);
        return ctx->gas_remaining;
    }

    template <Traits traits, uint32_t OFF, uint32_t NEW_SIZE, int64_t NEW_COST>
    [[gnu::always_inline]] inline uint256_t
    mload_c(Context *const ctx, int64_t &gas)
    {
        if (MONAD_UNLIKELY(ctx->memory_access32_end <= OFF)) {
            gas = grow32<traits, OFF, NEW_SIZE, NEW_COST>(ctx, gas);
        }
        uint256_t r;
        runtime::mload_at<traits>(
            ctx, &r, runtime::Memory::Offset::unsafe_from(OFF));
        return r;
    }

    template <Traits traits, uint32_t OFF, uint32_t NEW_SIZE, int64_t NEW_COST>
    [[gnu::always_inline]] inline void
    mstore_c(Context *const ctx, int64_t &gas, uint256_t const &value)
    {
        if (MONAD_UNLIKELY(ctx->memory_access32_end <= OFF)) {
            gas = grow32<traits, OFF, NEW_SIZE, NEW_COST>(ctx, gas);
        }
        runtime::mstore_at<traits>(
            ctx, runtime::Memory::Offset::unsafe_from(OFF), &value);
    }

    template <Traits traits>
    [[gnu::noinline]] void mstore8(
        Context *const ctx, int64_t const gas, uint256_t const &offset,
        uint256_t const &value)
    {
        ctx->gas_remaining = gas;
        runtime::mstore8<traits>(ctx, &offset, &value);
    }

    // SHA3

    template <Traits traits>
    [[gnu::noinline]] uint256_t sha3_any(
        Context *const ctx, int64_t const gas, uint256_t const &offset,
        uint256_t const &size)
    {
        ctx->gas_remaining = gas;
        uint256_t r;
        runtime::sha3<traits>(ctx, &r, &offset, &size);
        return r;
    }

    // N bytes, N 32 or 64, whose word gas the block charged: from the memo
    // when it holds them, as the SHA3 handler does.
    template <Traits traits, size_t N>
    [[gnu::always_inline]] inline uint256_t
    sha3_n(Context *const ctx, int64_t &gas, uint256_t const &offset)
    {
        static_assert(N == 32 || N == 64);
        uint64_t const o = offset[0];
        uint64_t const end = ctx->memory_access32_end;
        if (MONAD_LIKELY(
                ((o & 7) | offset[1] | offset[2] | offset[3]) == 0 &&
                o < end && o + (N - 32) < end)) {
            auto const *const in =
                reinterpret_cast<uint64_t const *>(ctx->memory.data + o);
            auto const &e = runtime::sha3_memo_entry<N>(in);
            if (MONAD_LIKELY(runtime::sha3_memo_holds(e, in))) {
                return e.out;
            }
            uint256_t r;
            runtime::sha3_memo_fill<N>(in, &r);
            return r;
        }
        uint256_t const r = sha3_any<traits>(
            ctx, gas + static_cast<int64_t>(N / 32 * 6), offset, uint256_t{N});
        gas = ctx->gas_remaining;
        return r;
    }

    // Arithmetic the handlers call out for

    [[gnu::always_inline]] inline uint256_t
    mul(uint256_t const &a, uint256_t const &b) noexcept
    {
        uint256_t r;
        runtime::mul(&r, &a, &b);
        return r;
    }

    [[gnu::always_inline]] inline uint256_t
    udiv(uint256_t const &a, uint256_t const &b) noexcept
    {
        uint256_t r;
        runtime::udiv(&r, &a, &b);
        return r;
    }

    [[gnu::always_inline]] inline uint256_t
    umod(uint256_t const &a, uint256_t const &b) noexcept
    {
        uint256_t r;
        runtime::umod(&r, &a, &b);
        return r;
    }

    // x << K and x >> K for a constant K under 256: the words' moves fold.
    template <unsigned K>
    [[gnu::always_inline]] inline uint256_t
    shl_c(uint256_t const &x) noexcept
    {
        static_assert(K > 0 && K < 256);
        constexpr unsigned w = K / 64;
        constexpr unsigned b = K % 64;
        uint256_t r{0};
        for (unsigned i = 3; i + 1 > w; --i) {
            uint64_t v = x[i - w] << b;
            if constexpr (b != 0) {
                if (i > w) {
                    v |= x[i - w - 1] >> (64 - b);
                }
            }
            r[i] = v;
        }
        return r;
    }

    template <unsigned K>
    [[gnu::always_inline]] inline uint256_t
    shr_c(uint256_t const &x) noexcept
    {
        static_assert(K > 0 && K < 256);
        constexpr unsigned w = K / 64;
        constexpr unsigned b = K % 64;
        uint256_t r{0};
        for (unsigned i = 0; i + w < 4; ++i) {
            uint64_t v = x[i + w] >> b;
            if constexpr (b != 0) {
                if (i + w + 1 < 4) {
                    v |= x[i + w + 1] << (64 - b);
                }
            }
            r[i] = v;
        }
        return r;
    }

    // base ** E for a constant exponent, whose byte gas the block charged:
    // square and multiply, unrolled.
    template <uint64_t E>
    [[gnu::always_inline]] inline uint256_t
    exp_c(uint256_t const &base) noexcept
    {
        if constexpr (E == 0) {
            return uint256_t{1};
        }
        else if constexpr (E == 1) {
            return base;
        }
        else {
            uint256_t const half = exp_c<E / 2>(base);
            uint256_t const sq = mul(half, half);
            if constexpr (E % 2 == 1) {
                return mul(sq, base);
            }
            else {
                return sq;
            }
        }
    }

    template <Traits traits>
    [[gnu::noinline]] uint256_t exp(
        Context *const ctx, int64_t const gas, uint256_t const &base,
        uint256_t const &exponent)
    {
        ctx->gas_remaining = gas;
        uint256_t r;
        runtime::exp<traits>(ctx, &r, &base, &exponent);
        return r;
    }

    // Environment

    [[gnu::always_inline]] inline uint256_t
    calldataload(Context *const ctx, uint256_t const &i) noexcept
    {
        uint256_t r;
        runtime::calldataload(ctx, &r, &i);
        return r;
    }

    template <Traits traits>
    [[gnu::noinline]] uint256_t
    balance(Context *const ctx, int64_t const gas, uint256_t const &address)
    {
        ctx->gas_remaining = gas;
        uint256_t r;
        runtime::balance<traits>(ctx, &r, &address);
        return r;
    }

    // Storage

    template <Traits traits>
    [[gnu::always_inline]] inline uint256_t
    sload(Context *const ctx, int64_t &gas, uint256_t const &key)
    {
        ctx->gas_remaining = gas;
        uint256_t r;
        runtime::sload<traits>(ctx, &r, &key);
        gas = ctx->gas_remaining;
        return r;
    }

    template <Traits traits>
    [[gnu::always_inline]] inline void sstore(
        Context *const ctx, int64_t &gas, uint256_t const &key,
        uint256_t const &value, int64_t const remaining_block_base_gas)
    {
        ctx->gas_remaining = gas;
        runtime::sstore<traits>(ctx, &key, &value, remaining_block_base_gas);
        gas = ctx->gas_remaining;
    }

    // Logs and calls

    template <Traits traits>
    [[gnu::noinline]] void log2(
        Context *const ctx, int64_t const gas, uint256_t const &offset,
        uint256_t const &size, uint256_t const &t1, uint256_t const &t2)
    {
        ctx->gas_remaining = gas;
        runtime::log2<traits>(ctx, &offset, &size, &t1, &t2);
    }

    template <Traits traits>
    [[gnu::noinline]] void log3(
        Context *const ctx, int64_t const gas, uint256_t const &offset,
        uint256_t const &size, uint256_t const &t1, uint256_t const &t2,
        uint256_t const &t3)
    {
        ctx->gas_remaining = gas;
        runtime::log3<traits>(ctx, &offset, &size, &t1, &t2, &t3);
    }

    template <Traits traits>
    [[gnu::noinline]] uint256_t call(
        Context *const ctx, int64_t const gas, uint256_t const &g,
        uint256_t const &address, uint256_t const &value,
        uint256_t const &args_offset, uint256_t const &args_size,
        uint256_t const &ret_offset, uint256_t const &ret_size,
        int64_t const remaining_block_base_gas)
    {
        ctx->gas_remaining = gas;
        uint256_t r;
        runtime::call<traits>(
            ctx,
            &r,
            &g,
            &address,
            &value,
            &args_offset,
            &args_size,
            &ret_offset,
            &ret_size,
            remaining_block_base_gas);
        return r;
    }

    // Exits: the frame's result where the interpreter's RETURN, REVERT and
    // STOP leave it, then a return to the trampoline.

    [[gnu::always_inline]] inline void finish(
        Context *const ctx, int64_t const gas, StatusCode const code,
        uint256_t const &offset, uint256_t const &size) noexcept
    {
        std::memcpy(ctx->result.offset, &offset, 32);
        std::memcpy(ctx->result.size, &size, 32);
        ctx->gas_remaining = gas;
        ctx->result.status = code;
    }

    [[gnu::always_inline]] inline void
    stop(Context *const ctx, int64_t const gas) noexcept
    {
        ctx->gas_remaining = gas;
        ctx->result.status = StatusCode::Success;
    }
}
