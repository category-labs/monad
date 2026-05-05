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

#include <category/core/config.hpp>

#include <category/core/runtime/uint256.hpp>

#include <cstdint>

MONAD_NAMESPACE_BEGIN

using ::monad::vm::runtime::div_result;
using ::monad::vm::runtime::result_with_carry;
using ::monad::vm::runtime::uint256_t;

[[gnu::noinline]]
result_with_carry<uint64_t>
addc_disas(uint64_t const a, uint64_t const b, bool const c)
{
    return ::monad::vm::runtime::addc(a, b, c);
}

[[gnu::noinline]]
result_with_carry<uint64_t>
subb_disas(uint64_t const a, uint64_t const b, bool const c)
{
    return ::monad::vm::runtime::subb(a, b, c);
}

[[gnu::noinline]]
uint64_t shld_disas(uint64_t const hi, uint64_t const lo, uint8_t const s)
{
    return ::monad::vm::runtime::shld(hi, lo, s);
}

[[gnu::noinline]]
uint64_t shrd_disas(uint64_t const hi, uint64_t const lo, uint8_t const s)
{
    return ::monad::vm::runtime::shrd(hi, lo, s);
}

[[gnu::noinline]]
div_result<uint64_t>
div_disas(uint64_t const u_hi, uint64_t const u_lo, uint64_t const v)
{
    return ::monad::vm::runtime::div(u_hi, u_lo, v);
}

[[gnu::noinline]]
void mulx_disas(
    uint64_t const x, uint64_t const y, uint64_t &r_hi, uint64_t &r_lo)
{
    ::monad::vm::runtime::mulx(x, y, r_hi, r_lo);
}

[[gnu::noinline]]
uint256_t uint256_add_disas(uint256_t const &a, uint256_t const &b)
{
    return a + b;
}

[[gnu::noinline]]
uint256_t uint256_sub_disas(uint256_t const &a, uint256_t const &b)
{
    return a - b;
}

[[gnu::noinline]]
uint256_t uint256_mul_disas(uint256_t const &a, uint256_t const &b)
{
    return a * b;
}

[[gnu::noinline]]
uint256_t uint256_shl_disas(uint256_t const &a, uint64_t const s)
{
    return a << s;
}

[[gnu::noinline]]
uint256_t uint256_shr_disas(uint256_t const &a, uint256_t const &s)
{
    return a >> s;
}

[[gnu::noinline]]
uint256_t uint256_div_disas(uint256_t const &a, uint256_t const &b)
{
    return a / b;
}

// Pins the current SWAP opcode codegen pattern used in the interpreter's
// instruction table. The subsequent refactor PR replaces the body with
// `runtime::swap(a, b)`; the emitted instructions must be byte-identical.
[[gnu::noinline]]
void uint256_swap_disas(uint256_t &a, uint256_t &b)
{
    auto const top = a.to_avx();
    a = b;
    b = uint256_t{top};
}

MONAD_NAMESPACE_END
