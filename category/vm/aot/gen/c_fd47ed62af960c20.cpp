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

// Written by aotgen.py from the code whose keccak is fd47ed62af960c20eb4a947a0554b963f630eeaf623bab374f914cb8e23d972b: not to be edited.

#include <category/vm/aot/ops.hpp>
#include <category/vm/interpreter/execute.hpp>
#include <category/vm/interpreter/intercode.hpp>

#define MONAD_AOT_TAIL __attribute__((musttail))

namespace monad::vm::aot
{
    using runtime::Context;
    using runtime::StatusCode;

    // 7263 bytes, keccak fd47ed62af960c20eb4a947a0554b963f630eeaf623bab374f914cb8e23d972b
    namespace c_fd47ed62af960c20
    {
        template <Traits traits>
        using Block = void (*)(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_22(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_37(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_40(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_5f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_79(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_84(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_90(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_af(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_db(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_fb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_102(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_120(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_23f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_242(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_24a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_277(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2c8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_316(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_346(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_352(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_35e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_36a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_376(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_382(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_389(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_392(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_396(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_39f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6ce(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_6fa(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_712(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_757(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_76c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_7a2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_7b9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_80a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_812(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_81c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_826(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_845(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_86c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_870(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_878(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_881(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_889(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_88f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_897(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_89e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_8c2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_90b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_936(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_975(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a20(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_a86(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_aeb(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b2a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b31(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_b94(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_bca(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c05(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c76(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c84(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_d15(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d4c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d62(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d73(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_dd5(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e2a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e3d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e84(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e95(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1008(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_100f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1023(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1070(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10c3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10d0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10fc(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_110b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_111d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_112a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1180(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_118d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11e0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1242(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_124f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_13ed(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1401(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_147f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_14d7(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1539(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1590(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_15e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_15ef(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_15f8(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_165c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_166f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1677(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1698(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16a4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1754(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_17ab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17d2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17e2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17e9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17f1(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_185b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_18da(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1906(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_190c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1938(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1939(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_195c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_195d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1980(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline]] void b_1981(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19bf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_19c0(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_19fe(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_19ff(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a1b(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a79(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a7d(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1abf(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1ac3(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ad9(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b0c(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b11(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b1a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b1f(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b24(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b2a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b30(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b6e(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b7a(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b81(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b90(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b99(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1ba2(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bab(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bb4(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bbd(Context *, uint256_t const *, uint256_t *, int64_t);
        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bc2(Context *, uint256_t const *, uint256_t *, int64_t);

        template <Traits traits>
        void bad(Context *const ctx, uint256_t const *, uint256_t *, int64_t)
        {
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        inline constexpr Block<traits> jump_table[7263] = {
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_11<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_3a<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_6c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_af<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_c1<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_ce<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_23f<traits>,
            &bad<traits>, &bad<traits>, &b_242<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_24e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_2c8<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_316<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_389<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_396<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_3b1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_6ce<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_712<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_76c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_7b9<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_80a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_81c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_845<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_86c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_870<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_881<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_88f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_89e<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_8c2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_90b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_936<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_975<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_b2a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_b31<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_bca<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_c05<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_c76<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_c84<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_d4c<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_d62<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_d73<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_e2a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_e3d<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_e84<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_e95<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1008<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_100f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1070<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_10c3<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_10d0<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_10fc<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_110b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_111d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_112a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1180<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_118d<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_11e0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_11ef<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1242<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_124f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1401<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_147f<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_14d7<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1539<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1590<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_15e2<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_15ef<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_165c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_166f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1677<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1698<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_16a4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1754<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_17d2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_17e2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_17e9<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_17f1<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_17fe<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, nullptr, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_185b<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_18da<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, nullptr,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_190c<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1939<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_195d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1981<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_19c0<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_19ff<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1a1b<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1a7d<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1ac3<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1b0c<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &b_1b11<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1b1a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &b_1b1f<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1b24<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1b2a<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1b30<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1b6e<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1b7a<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1b81<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1b90<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1b99<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1ba2<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1bab<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &b_1bb4<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &b_1bbd<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &b_1bc2<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, nullptr, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>, &bad<traits>,
            &bad<traits>, &bad<traits>, &bad<traits>,
        };

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x15, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x52, 0x60, 0x36, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::mstore_c<traits, 64u, 96u, 9>(ctx, gas, uint256_t{0x80ull});
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = aot::from_bool(t1 < uint256_t{0x4ull});
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j8 = aot::nonzero(t3);
            if (j8) { MONAD_AOT_TAIL return b_11<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x35, 0x60, 0x1c, 0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x0ull});
            uint256_t const t2 = aot::shr_c<224>(t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0x25394645ull} == t2);
            bool const j9 = aot::nonzero(t3);
            top[1] = t2;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc9); }
            MONAD_AOT_TAIL return b_22<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_22(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x80, 0x63, 0x14, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x80, 0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x439fab91ull} == s0);
            bool const j4 = aot::nonzero(t1);
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc9); }
            MONAD_AOT_TAIL return b_2d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x63, 0x14, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x63, 0x14, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::from_bool(uint256_t{0x7e4f7a8aull} == s0);
            bool const j3 = aot::nonzero(t1);
            top += -1;
            if (j3) { MONAD_AOT_TAIL return b_3a<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_37<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_37(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x80, 0xfd}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x80, 0xfd}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            aot::finish(ctx, gas, StatusCode::Revert, uint256_t{0x0ull}, uint256_t{0x0ull});
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x34, 0x61, 0x57}, 0, 2));
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x34, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = ::monad::load_be<uint256_t>(ctx->env.value);
            bool const j3 = aot::nonzero(t1);
            if (j3) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_40<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_40(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x40ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_4c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_4c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x67, 0x60, 0x35, 0x81, 0x81, 0x11, 0x61, 0x57}, 0, 4));
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x67, 0x60, 0x35, 0x81, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j7 = aot::nonzero(t2);
            top[1] = uint256_t{0xffffffffffffffffull};
            top[2] = t1;
            top += 2;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_5f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_5f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x6cull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x60, 0x35, 0x91, 0x81, 0x83, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x60, 0x35, 0x91, 0x81, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x24ull});
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = aot::from_bool(s2 < t1);
            bool const j9 = aot::nonzero(t2);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-2] = m0;
            top[-1] = t1;
            top[0] = m2;
            top[1] = m1;
            top += 1;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_79<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_79(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x36, 0x60, 0x84, 0x01, 0x12, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x36, 0x60, 0x84, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + uint256_t{0x23ull};
            uint256_t const t3 = aot::from_bool(slt(t2, t1));
            uint256_t const t4 = aot::from_bool(!aot::nonzero(t3));
            bool const j7 = aot::nonzero(t4);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_84<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_84(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x60, 0x01, 0x35, 0x91, 0x82, 0x11, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x60, 0x01, 0x35, 0x91, 0x82, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = uint256_t{0x4ull} + s2;
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j8 = aot::nonzero(t3);
            top[-1] = t2;
            if (j8) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_90<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_90(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x36, 0x60, 0x83, 0x60, 0x1b, 0x85, 0x01, 0x01, 0x11, 0x61, 0x57}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x36, 0x60, 0x83, 0x60, 0x1b, 0x85, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::shl_c<5>(s1);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + t2;
            uint256_t const t4 = t3 + uint256_t{0x24ull};
            uint256_t const t5 = aot::from_bool(t1 < t4);
            bool const j10 = aot::nonzero(t5);
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_9f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_9f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x93, 0x60, 0x61, 0x94, 0x01, 0x91, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x93, 0x60, 0x61, 0x94, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x24ull};
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-3] = uint256_t{0xc1ull};
            top[-2] = uint256_t{0xafull};
            top[0] = t1;
            top[1] = m3;
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_1ac3<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_af(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x15, 0x15, 0x81, 0x52, 0x90, 0x81, 0x90, 0x60, 0x82, 0x01, 0x90, 0x56}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x15, 0x15, 0x81, 0x52, 0x90, 0x81, 0x90, 0x60, 0x82, 0x01, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = aot::from_bool(!aot::nonzero(s0));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            aot::mstore<traits>(ctx, gas, t1, t3);
            uint256_t const t4 = t1 + uint256_t{0x20ull};
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-1] = t1;
            top[0] = t1;
            top[1] = t4;
            top += 1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x03, 0x90, 0xf3}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x03, 0x90, 0xf3}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 - s1;
            uint256_t const &s2 = top[-2];
            aot::finish(ctx, gas, StatusCode::Success, s2, t1);
            return;
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x81, 0x60, 0x84, 0x01, 0x12, 0x15, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x81, 0x60, 0x84, 0x01, 0x12, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1full};
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(slt(t1, s1));
            uint256_t const t3 = aot::from_bool(!aot::nonzero(t2));
            bool const j9 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = m0;
            top[0] = m2;
            if (j9) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_db<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_db(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x35, 0x91, 0x67, 0x83, 0x11, 0x61, 0x57}, 3, 3));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x35, 0x91, 0x67, 0x83, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::calldataload(ctx, s2);
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[1] = m1;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x83, 0x81, 0x86, 0x01, 0x95, 0x01, 0x01, 0x11, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x83, 0x81, 0x86, 0x01, 0x95, 0x01, 0x01, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s3 + s2;
            uint256_t const t3 = t2 + uint256_t{0x20ull};
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::from_bool(s0 < t3);
            bool const j10 = aot::nonzero(t4);
            top[-3] = t1;
            top += -1;
            if (j10) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_fb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_fb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_102(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x36, 0x60, 0x19, 0x01, 0x12, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const t2 = uint256_t{0xfffffffffffffffcull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull} + t1;
            uint256_t const t3 = aot::from_bool(slt(t2, uint256_t{0x20ull}));
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_10e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_10e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}, 0, 3));
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x35, 0x67, 0x81, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::calldataload(ctx, uint256_t{0x4ull});
            uint256_t const t2 = aot::from_bool(uint256_t{0xffffffffffffffffull} < t1);
            bool const j6 = aot::nonzero(t2);
            top[1] = t1;
            top += 1;
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xc5); }
            MONAD_AOT_TAIL return b_120<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_120(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x90, 0x36, 0x90, 0x60, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = uint256_t{static_cast<uint64_t>(ctx->env.input_data_size)};
            uint256_t const &s0 = top[0];
            uint256_t const t2 = uint256_t{0x4ull} + s0;
            top[0] = uint256_t{0x12dull};
            top[1] = t1;
            top[2] = t2;
            top += 2;
            MONAD_AOT_TAIL return b_ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_23f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x91}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x0ull};
            top[1] = m1;
            top += 1;
            MONAD_AOT_TAIL return b_242<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_242(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x83, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s2 < s1);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_24e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_24a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_24a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_24e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x81, 0x35, 0x11, 0x61, 0x57}, 1, 2));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x81, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const t2 = aot::from_bool(uint256_t{0x43e1f593f0000000ull, 0x2833e84879b97091ull, 0xb85045b68181585dull, 0x30644e72e131a029ull} < t1);
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x284); }
            MONAD_AOT_TAIL return b_277<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_277(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x91, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x91, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + uint256_t{0x1ull};
            top[-2] = t2;
            top[0] = t1;
            MONAD_AOT_TAIL return b_242<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_2c8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x03, 0x61, 0x57}, 1, 1));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x360ull} - s0;
            bool const j4 = aot::nonzero(t1);
            top += -1;
            if (j4) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x2d2); }
            MONAD_AOT_TAIL return b_2d1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_2d1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_316(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x01, 0x90, 0x7f, 0x80, 0x92, 0x35, 0x11, 0x61, 0x57}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x01, 0x90, 0x7f, 0x80, 0x92, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x180ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const t3 = aot::from_bool(uint256_t{0x43e1f593f0000000ull, 0x2833e84879b97091ull, 0xb85045b68181585dull, 0x30644e72e131a029ull} < t2);
            bool const j11 = aot::nonzero(t3);
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x43e1f593f0000000ull, 0x2833e84879b97091ull, 0xb85045b68181585dull, 0x30644e72e131a029ull};
            top[1] = m0;
            top += 1;
            if (j11) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_346<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_346(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1a0ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_352<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_352(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1c0ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_35e<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_35e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x1e0ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_36a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_36a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x200ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_376<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_376(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}, 2, 3));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x81, 0x61, 0x82, 0x01, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x260ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::from_bool(s1 < t2);
            bool const j7 = aot::nonzero(t3);
            if (j7) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_382<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_382(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x01, 0x90, 0x5f, 0x91}, 2, 1));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x01, 0x90, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x300ull} + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = uint256_t{0x0ull};
            top[0] = m1;
            top[1] = t1;
            top += 1;
            MONAD_AOT_TAIL return b_389<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_389(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x83, 0x10, 0x61, 0x57}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s2 < uint256_t{0x1ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_396<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_392<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_392(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x56}, 4, 0));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_396(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x81, 0x81, 0x35, 0x11, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x81, 0x81, 0x35, 0x11, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::calldataload(ctx, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::from_bool(s1 < t1);
            bool const j6 = aot::nonzero(t2);
            if (j6) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x3ac); }
            MONAD_AOT_TAIL return b_39f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_39f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x60, 0x91, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x60, 0x91, 0x01, 0x92, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + uint256_t{0x1ull};
            top[-2] = t2;
            top[0] = t1;
            MONAD_AOT_TAIL return b_389<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_3b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x90, 0x93, 0x92, 0x93, 0x61, 0x60, 0x51, 0x95, 0x60, 0x61, 0x88, 0x01, 0x95, 0x86, 0x94, 0x64, 0x86, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x61, 0x90, 0x60, 0x1b, 0x80, 0x94, 0x82, 0x8c, 0x01, 0x37, 0x83, 0x8a, 0x01, 0x01, 0x37, 0x01, 0x61, 0x86, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 4, 10));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x90, 0x93, 0x92, 0x93, 0x61, 0x60, 0x51, 0x95, 0x60, 0x61, 0x88, 0x01, 0x95, 0x86, 0x94, 0x64, 0x86, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x7f, 0x61, 0x8b, 0x01, 0x52, 0x61, 0x90, 0x60, 0x1b, 0x80, 0x94, 0x82, 0x8c, 0x01, 0x37, 0x83, 0x8a, 0x01, 0x01, 0x37, 0x01, 0x61, 0x86, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x67616d6d61ull});
            uint256_t const t3 = t1 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0x4cebef9be53ba77cull, 0x517d946564ab2422ull, 0xcdfcbab5df52610full, 0x584cfa0ab76e9f3ull});
            uint256_t const t4 = t1 + uint256_t{0x280ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x33e467df6c35e803ull, 0xc73ec9135e117f3aull, 0x4f52cb632a0fa64eull, 0x2b28cd768b28dc05ull});
            uint256_t const t5 = t1 + uint256_t{0x2a0ull};
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0xcf450677f29088f9ull, 0x1978749803061357ull, 0x9c3eca7c02aef089ull, 0x1c040c6eb53c43b7ull});
            uint256_t const t6 = t1 + uint256_t{0x2c0ull};
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0x96d5f3395c68e091ull, 0xabe6e1928baf1117ull, 0x4192afbacdf18161ull, 0x109cf6df22bc04e6ull});
            uint256_t const t7 = t1 + uint256_t{0x2e0ull};
            aot::mstore<traits>(ctx, gas, t7, uint256_t{0xfbc5a539efcf1381ull, 0x8e1fa771f4778595ull, 0x2cd4662a8cdde5d5ull, 0xeb7f86da11f7f0full});
            uint256_t const t8 = t1 + uint256_t{0x300ull};
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x5af040d25e76f99bull, 0x6ba906a76f2e51d3ull, 0x766feec7ee734b1bull, 0x29fc0dd0c7417d23ull});
            uint256_t const t9 = t1 + uint256_t{0x320ull};
            aot::mstore<traits>(ctx, gas, t9, uint256_t{0x7a9820468b369f61ull, 0xd1ba9a7aaaa77e9dull, 0x11644465a48353d2ull, 0x121c455821fa725dull});
            uint256_t const t10 = t1 + uint256_t{0x340ull};
            aot::mstore<traits>(ctx, gas, t10, uint256_t{0xbd82c0800c02d62bull, 0x5ee34ef256eed2baull, 0x20ab42c8fea72f97ull, 0x26fde3a359b76de1ull});
            uint256_t const t11 = t1 + uint256_t{0x360ull};
            aot::mstore<traits>(ctx, gas, t11, uint256_t{0xacaa6b6aa76dc9bcull, 0x907fcc1d4b466b17ull, 0x50b1afef6745b0afull, 0x17507f61603e878ull});
            uint256_t const t12 = t1 + uint256_t{0x380ull};
            aot::mstore<traits>(ctx, gas, t12, uint256_t{0x298d94160f9388f0ull, 0x183b157f4878a474ull, 0x1e1817990c4d5f4eull, 0x2b59b723a2b9d9e7ull});
            uint256_t const t13 = t1 + uint256_t{0x3a0ull};
            aot::mstore<traits>(ctx, gas, t13, uint256_t{0x7d15c53676faf662ull, 0xbcbe29b3fc6963a9ull, 0xf434653399935c68ull, 0xbf238da01b4d1aaull});
            uint256_t const t14 = t1 + uint256_t{0x3c0ull};
            aot::mstore<traits>(ctx, gas, t14, uint256_t{0x7d84812538a45bf4ull, 0x2660cdec96b7deeeull, 0xfd01ecb102a6ab2eull, 0x2360a9f01aa56f17ull});
            uint256_t const t15 = t1 + uint256_t{0x3e0ull};
            aot::mstore<traits>(ctx, gas, t15, uint256_t{0xebb9df279a537cf6ull, 0xd11eff5578c7ec31ull, 0xdf8379230a888cfaull, 0x8ccf24a4e892644ull});
            uint256_t const t16 = t1 + uint256_t{0x400ull};
            aot::mstore<traits>(ctx, gas, t16, uint256_t{0x7aca8c4169100478ull, 0xce0b31f0bf0a29abull, 0xb8202945fb217cb0ull, 0x28cc676be16a275dull});
            uint256_t const t17 = t1 + uint256_t{0x420ull};
            aot::mstore<traits>(ctx, gas, t17, uint256_t{0x627e23ad313001d5ull, 0x3fbebbda6ce2f255ull, 0xc764f931db2586f8ull, 0x1140272638681e95ull});
            uint256_t const t18 = t1 + uint256_t{0x440ull};
            aot::mstore<traits>(ctx, gas, t18, uint256_t{0xae8e57e28ea1e0c3ull, 0x6090590a8dff8966ull, 0xf23240a5641a17c0ull, 0xab6139495f0d9c1ull});
            uint256_t const t19 = t1 + uint256_t{0x460ull};
            aot::mstore<traits>(ctx, gas, t19, uint256_t{0xee38223a23d7c0feull, 0xfe154c2af083e550ull, 0x4ce8036b8bf56c68ull, 0x1dec8e22c06a93dull});
            uint256_t const t20 = t1 + uint256_t{0x480ull};
            aot::mstore<traits>(ctx, gas, t20, uint256_t{0x7c7bfe28828573bull, 0x94f82d670a09fd55ull, 0xe6c8953c911db9e5ull, 0x229df4eb55698f3bull});
            uint256_t const &s1 = top[-1];
            uint256_t const t21 = aot::shl_c<5>(s1);
            uint256_t const t22 = t1 + uint256_t{0x4a0ull};
            uint256_t const &s2 = top[-2];
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t22, &s2, &t21);
            gas = ctx->gas_remaining;
            uint256_t const t23 = t1 + t21;
            uint256_t const t24 = t23 + uint256_t{0x4a0ull};
            uint256_t const &s0 = top[0];
            uint256_t const k125_2 = uint256_t{0xc0ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t24, &s0, &k125_2);
            gas = ctx->gas_remaining;
            uint256_t const t25 = t21 + uint256_t{0x305ull};
            uint256_t const t26 = t1 + uint256_t{0x25bull};
            uint256_t const t27 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k132_1 = uint256_t{0x2ull};
            uint256_t const k132_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r132;
            runtime::staticcall<traits>(ctx, &r132, &t27, &k132_1, &t26, &t25, &t2, &k132_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t28 = aot::from_bool(!aot::nonzero(r132));
            bool const j135 = aot::nonzero(t28);
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            top[-3] = t1;
            top[-2] = m3;
            top[-1] = t2;
            top += -1;
            if (j135) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_6b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6b1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x91, 0x60, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x84, 0x06, 0x91, 0x01, 0x52, 0x56}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x91, 0x60, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x84, 0x06, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k9_0 = uint256_t{0x0ull};
            uint256_t const k9_1 = uint256_t{0x1c0aull};
            uint256_t const k9_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k9_0, &k9_1, &k9_2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            uint256_t const t4 = aot::umod(t1, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = s2 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_6ce(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x51, 0x91, 0x61, 0x83, 0x01, 0x90, 0x63, 0x82, 0x52, 0x61, 0x84, 0x01, 0x52, 0x60, 0x81, 0x60, 0x61, 0x86, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 2, 7));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x51, 0x91, 0x61, 0x83, 0x01, 0x90, 0x63, 0x82, 0x52, 0x61, 0x84, 0x01, 0x52, 0x60, 0x81, 0x60, 0x61, 0x86, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x62657461ull});
            uint256_t const t3 = t1 + uint256_t{0x260ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = t1 + uint256_t{0x25cull};
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k24_1 = uint256_t{0x2ull};
            uint256_t const k24_3 = uint256_t{0x24ull};
            uint256_t const k24_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r24;
            runtime::staticcall<traits>(ctx, &r24, &t5, &k24_1, &t4, &k24_3, &t2, &k24_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(r24));
            bool const j27 = aot::nonzero(t6);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-1] = t1;
            top[0] = m1;
            top[1] = t2;
            top += 1;
            if (j27) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_6fa<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_6fa(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x91, 0x60, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x84, 0x06, 0x91, 0x01, 0x52, 0x56}, 3, 6));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x91, 0x60, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x84, 0x06, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k9_0 = uint256_t{0x0ull};
            uint256_t const k9_1 = uint256_t{0x1c0aull};
            uint256_t const k9_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k9_0, &k9_1, &k9_2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            uint256_t const t4 = aot::umod(t1, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = s2 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_712(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x60, 0x61, 0x81, 0x51, 0x94, 0x61, 0x86, 0x01, 0x93, 0x64, 0x85, 0x52, 0x61, 0x87, 0x01, 0x52, 0x82, 0x61, 0x82, 0x01, 0x61, 0x88, 0x01, 0x37, 0x01, 0x61, 0x85, 0x01, 0x37, 0x60, 0x81, 0x60, 0x61, 0x86, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 3, 7));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x60, 0x61, 0x81, 0x51, 0x94, 0x61, 0x86, 0x01, 0x93, 0x64, 0x85, 0x52, 0x61, 0x87, 0x01, 0x52, 0x82, 0x61, 0x82, 0x01, 0x61, 0x88, 0x01, 0x37, 0x01, 0x61, 0x85, 0x01, 0x37, 0x60, 0x81, 0x60, 0x61, 0x86, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x616c706861ull});
            uint256_t const t3 = t1 + uint256_t{0x260ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t3, s1);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = s0 + uint256_t{0x320ull};
            uint256_t const t5 = t1 + uint256_t{0x280ull};
            uint256_t const k26_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t5, &t4, &k26_2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = s0 + uint256_t{0x220ull};
            uint256_t const t7 = t1 + uint256_t{0x2c0ull};
            uint256_t const k31_2 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t7, &t6, &k31_2);
            gas = ctx->gas_remaining;
            uint256_t const t8 = t1 + uint256_t{0x25bull};
            uint256_t const t9 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k40_1 = uint256_t{0x2ull};
            uint256_t const k40_3 = uint256_t{0xa5ull};
            uint256_t const k40_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r40;
            runtime::staticcall<traits>(ctx, &r40, &t9, &k40_1, &t8, &k40_3, &t2, &k40_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t10 = aot::from_bool(!aot::nonzero(r40));
            bool const j43 = aot::nonzero(t10);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = t2;
            if (j43) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_757<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_757(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x51, 0x91, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x83, 0x06, 0x90, 0x52, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x51, 0x91, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x83, 0x06, 0x90, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k8_0 = uint256_t{0x0ull};
            uint256_t const k8_1 = uint256_t{0x1c0aull};
            uint256_t const k8_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k8_0, &k8_1, &k8_2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            uint256_t const t4 = aot::umod(t1, t3);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t4);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_76c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x80, 0x60, 0x51, 0x93, 0x61, 0x85, 0x01, 0x93, 0x63, 0x85, 0x52, 0x61, 0x86, 0x01, 0x52, 0x01, 0x61, 0x84, 0x01, 0x37, 0x60, 0x81, 0x60, 0x61, 0x85, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x80, 0x60, 0x51, 0x93, 0x61, 0x85, 0x01, 0x93, 0x63, 0x85, 0x52, 0x61, 0x86, 0x01, 0x52, 0x01, 0x61, 0x84, 0x01, 0x37, 0x60, 0x81, 0x60, 0x61, 0x85, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x7a657461ull});
            uint256_t const t3 = t1 + uint256_t{0x260ull};
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, t3, s1);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = s0 + uint256_t{0xc0ull};
            uint256_t const t5 = t1 + uint256_t{0x280ull};
            uint256_t const k22_2 = uint256_t{0xc0ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t5, &t4, &k22_2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = t1 + uint256_t{0x25cull};
            uint256_t const t7 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k31_1 = uint256_t{0x2ull};
            uint256_t const k31_3 = uint256_t{0xe4ull};
            uint256_t const k31_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r31;
            runtime::staticcall<traits>(ctx, &r31, &t7, &k31_1, &t6, &k31_3, &t2, &k31_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t8 = aot::from_bool(!aot::nonzero(r31));
            bool const j34 = aot::nonzero(t8);
            top[-1] = t1;
            top[0] = t2;
            if (j34) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_7a2<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_7a2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x91, 0x51, 0x06, 0x91, 0x01, 0x52, 0x56}, 3, 5));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x91, 0x51, 0x06, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k6_0 = uint256_t{0x0ull};
            uint256_t const k6_1 = uint256_t{0x1c0aull};
            uint256_t const k6_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k6_0, &k6_1, &k6_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t4 = aot::umod(t3, t2);
            uint256_t const &s1 = top[-1];
            uint256_t const t5 = s1 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top += -3;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_7b9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x93, 0x92, 0x91, 0x7f, 0x60, 0x51, 0x93, 0x61, 0x60, 0x86, 0x01, 0x51, 0x95, 0x01, 0x51, 0x95, 0x81, 0x96, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x93, 0x84, 0x91, 0x09, 0x93, 0x60, 0x83, 0x97, 0x5f, 0x91}, 4, 10));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x93, 0x92, 0x91, 0x7f, 0x60, 0x51, 0x93, 0x61, 0x60, 0x86, 0x01, 0x51, 0x95, 0x01, 0x51, 0x95, 0x81, 0x96, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x93, 0x84, 0x91, 0x09, 0x93, 0x60, 0x83, 0x97, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x60ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = t1 + uint256_t{0x1c0ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k26_0 = uint256_t{0x0ull};
            uint256_t const k26_1 = uint256_t{0x1c0aull};
            uint256_t const k26_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k26_0, &k26_1, &k26_2);
            gas = ctx->gas_remaining;
            uint256_t const t7 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t6);
            uint256_t const k34_1 = uint256_t{0x6729acf1ff053609ull, 0x6787b9b45fc54c54ull, 0x1f8030da595e7d1cull, 0x30644e5aaf0a66b9ull};
            uint256_t r34;
            runtime::mulmod(&r34, &t5, &k34_1, &t7);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = uint256_t{0x0ull};
            top[-1] = m2;
            top[1] = r34;
            top[2] = t7;
            top[3] = m2;
            top[4] = m3;
            top[5] = m1;
            top[6] = uint256_t{0x0ull};
            top[7] = t3;
            top[8] = uint256_t{0x1ull};
            top += 8;
            MONAD_AOT_TAIL return b_80a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_80a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x83, 0x10, 0x61, 0x57}, 4, 2));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::from_bool(s2 < s3);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_936<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_812<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_812(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x60, 0x87, 0x52, 0x5f, 0x95, 0x5f}, 10, 0));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x60, 0x87, 0x52, 0x5f, 0x95, 0x5f}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, s9, uint256_t{0x1ull});
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-8] = uint256_t{0x0ull};
            top[-2] = m8;
            top[-1] = uint256_t{0x0ull};
            top += -1;
            MONAD_AOT_TAIL return b_81c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_81c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x87, 0x83, 0x82, 0x10, 0x15, 0x61, 0x57}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x87, 0x83, 0x82, 0x10, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::from_bool(s0 < s2);
            uint256_t const t2 = aot::from_bool(!aot::nonzero(t1));
            bool const j7 = aot::nonzero(t2);
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = m7;
            top += 1;
            if (j7) { MONAD_AOT_TAIL return b_845<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_826<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_826(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x90, 0x81, 0x87, 0x60, 0x93, 0x8c, 0x01, 0x51, 0x82, 0x89, 0x01, 0x51, 0x90, 0x09, 0x90, 0x60, 0x80, 0x91, 0x01, 0x9a, 0x8c, 0x01, 0x01, 0x52, 0x01, 0x61, 0x56}, 10, 5));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x90, 0x81, 0x87, 0x60, 0x93, 0x8c, 0x01, 0x51, 0x82, 0x89, 0x01, 0x51, 0x90, 0x09, 0x90, 0x60, 0x80, 0x91, 0x01, 0x9a, 0x8c, 0x01, 0x01, 0x52, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s9 + s0;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s5 = top[-5];
            uint256_t const t3 = s5 + s0;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const &s6 = top[-6];
            uint256_t r13;
            runtime::mulmod(&r13, &t2, &t4, &s6);
            uint256_t const t5 = s0 + uint256_t{0x20ull};
            uint256_t const &s8 = top[-8];
            uint256_t const t6 = s9 + s8;
            uint256_t const t7 = t6 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t7, r13);
            uint256_t const &s1 = top[-1];
            uint256_t const t8 = s1 + uint256_t{0x1ull};
            top[-8] = t5;
            top[-1] = t8;
            top += -1;
            MONAD_AOT_TAIL return b_81c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_845(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x96, 0x93, 0x99, 0x98, 0x91, 0x94, 0x92, 0x97, 0x50, 0x50, 0x60, 0x19, 0x95, 0x86, 0x81, 0x84, 0x01, 0x01, 0x91, 0x01, 0x95, 0x60, 0x96, 0x61, 0x60, 0x82, 0x01, 0x82, 0x51, 0x61, 0x56}, 11, 4));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x96, 0x93, 0x99, 0x98, 0x91, 0x94, 0x92, 0x97, 0x50, 0x50, 0x60, 0x19, 0x95, 0x86, 0x81, 0x84, 0x01, 0x01, 0x91, 0x01, 0x95, 0x60, 0x96, 0x61, 0x60, 0x82, 0x01, 0x82, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s5 + s0;
            uint256_t const t2 = t1 + uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            uint256_t const &s9 = top[-9];
            uint256_t const t3 = s9 + s0;
            uint256_t const t4 = t3 + uint256_t{0x20ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const m5 = s5;
            top[-10] = m4;
            top[-9] = m10;
            top[-8] = m3;
            top[-7] = uint256_t{0x20ull};
            top[-5] = m2;
            top[-4] = m7;
            top[-3] = m5;
            top[-2] = t2;
            top[-1] = uint256_t{0xffffffffffffffe0ull, 0xffffffffffffffffull, 0xffffffffffffffffull, 0xffffffffffffffffull};
            top[0] = t3;
            top[1] = uint256_t{0x86cull};
            top[2] = t4;
            top[3] = t5;
            top += 3;
            MONAD_AOT_TAIL return b_1a1b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_86c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x5f, 0x91}, 4, 1));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = m0;
            top[-1] = uint256_t{0x0ull};
            top[0] = m3;
            top[1] = m1;
            top += 1;
            MONAD_AOT_TAIL return b_870<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_870(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8a, 0x83, 0x10, 0x61, 0x57}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8a, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s10 = top[-10];
            uint256_t const t1 = aot::from_bool(s2 < s10);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_90b<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_878<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_878(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x60, 0x5f, 0x91}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x60, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = uint256_t{0x0ull};
            top[-4] = uint256_t{0x1ull};
            top[-3] = m5;
            top += -3;
            MONAD_AOT_TAIL return b_881<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_881(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x87, 0x83, 0x10, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x87, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::from_bool(s2 < s7);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_8c2<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_889<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_889(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x5f, 0x91}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x5f, 0x91}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = uint256_t{0x0ull};
            top[-3] = m5;
            top += -3;
            MONAD_AOT_TAIL return b_88f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_88f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x83, 0x10, 0x61, 0x57}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x83, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::from_bool(s2 < s4);
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_89e<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_897<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_897(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x50, 0x50, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint64_t const jt = aot::jump_offset(s6);
            top += -7;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_89e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x96, 0x84, 0x80, 0x83, 0x60, 0x93, 0x81, 0x87, 0x35, 0x8d, 0x51, 0x09, 0x90, 0x08, 0x99, 0x01, 0x93, 0x01, 0x93, 0x01, 0x91, 0x94, 0x93, 0x92, 0x90, 0x61, 0x56}, 8, 7));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x92, 0x93, 0x94, 0x96, 0x84, 0x80, 0x83, 0x60, 0x93, 0x81, 0x87, 0x35, 0x8d, 0x51, 0x09, 0x90, 0x08, 0x99, 0x01, 0x93, 0x01, 0x93, 0x01, 0x91, 0x94, 0x93, 0x92, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            uint256_t const &s5 = top[-5];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s5);
            uint256_t const &s0 = top[0];
            uint256_t r17;
            runtime::mulmod(&r17, &t2, &t1, &s0);
            uint256_t const &s7 = top[-7];
            uint256_t r19;
            runtime::addmod(&r19, &s7, &r17, &s0);
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s5 + s3;
            uint256_t const t4 = s1 + s3;
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = s2 + uint256_t{0x1ull};
            top[-7] = r19;
            top[-5] = t3;
            top[-2] = t5;
            top[-1] = t4;
            MONAD_AOT_TAIL return b_88f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_8c2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x7f, 0x88, 0x83, 0x83, 0x86, 0x81, 0x9d, 0x9e, 0x9b, 0x8a, 0x9d, 0x9e, 0x9b, 0x9d, 0x60, 0x98, 0x51, 0x09, 0x09, 0x81, 0x52, 0x01, 0x93, 0x09, 0x92, 0x01, 0x91, 0x90, 0x97, 0x96, 0x95, 0x93, 0x94, 0x97, 0x61, 0x56}, 9, 9));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x7f, 0x88, 0x83, 0x83, 0x86, 0x81, 0x9d, 0x9e, 0x9b, 0x8a, 0x9d, 0x9e, 0x9b, 0x9d, 0x60, 0x98, 0x51, 0x09, 0x09, 0x81, 0x52, 0x01, 0x93, 0x09, 0x92, 0x01, 0x91, 0x90, 0x97, 0x96, 0x95, 0x93, 0x94, 0x97, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s3 = top[-3];
            uint256_t const &s5 = top[-5];
            uint256_t r19;
            runtime::mulmod(&r19, &t1, &s3, &s5);
            uint256_t const &s1 = top[-1];
            uint256_t r20;
            runtime::mulmod(&r20, &r19, &s1, &s5);
            aot::mstore<traits>(ctx, gas, s0, r20);
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = s0 + s6;
            uint256_t const k25_1 = uint256_t{0xeccd4f3eb878331aull, 0x7b26b7488dc6d26eull, 0xa19b0361d9130cd4ull, 0x2a734ebb326341efull};
            uint256_t r25;
            runtime::mulmod(&r25, &s1, &k25_1, &s5);
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + uint256_t{0x1ull};
            top[-2] = t3;
            top[-1] = r25;
            top[0] = t2;
            MONAD_AOT_TAIL return b_881<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_90b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x89, 0x81, 0x60, 0x93, 0x9e, 0x9b, 0x9a, 0x9c, 0x9d, 0x9e, 0x01, 0x96, 0x84, 0x51, 0x90, 0x82, 0x89, 0x51, 0x82, 0x09, 0x86, 0x52, 0x09, 0x92, 0x01, 0x92, 0x01, 0x91, 0x90, 0x93, 0x9a, 0x99, 0x98, 0x96, 0x97, 0x9a, 0x61, 0x56}, 12, 7));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x89, 0x81, 0x60, 0x93, 0x9e, 0x9b, 0x9a, 0x9c, 0x9d, 0x9e, 0x01, 0x96, 0x84, 0x51, 0x90, 0x82, 0x89, 0x51, 0x82, 0x09, 0x86, 0x52, 0x09, 0x92, 0x01, 0x92, 0x01, 0x91, 0x90, 0x93, 0x9a, 0x99, 0x98, 0x96, 0x97, 0x9a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s0 + s3;
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const &s8 = top[-8];
            uint256_t r21;
            runtime::mulmod(&r21, &s4, &t3, &s8);
            aot::mstore<traits>(ctx, gas, s1, r21);
            uint256_t r24;
            runtime::mulmod(&r24, &s4, &t2, &s8);
            uint256_t const t4 = s1 + s3;
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = s2 + uint256_t{0x1ull};
            top[-4] = r24;
            top[-2] = t5;
            top[-1] = t4;
            top[0] = t1;
            MONAD_AOT_TAIL return b_870<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_936(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x87, 0x7f, 0x83, 0x82, 0x60, 0x95, 0x97, 0x9e, 0x96, 0x97, 0x81, 0x03, 0x88, 0x08, 0x86, 0x52, 0x09, 0x92, 0x01, 0x99, 0x01, 0x91, 0x90, 0x61, 0x56}, 10, 7));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x87, 0x7f, 0x83, 0x82, 0x60, 0x95, 0x97, 0x9e, 0x96, 0x97, 0x81, 0x03, 0x88, 0x08, 0x86, 0x52, 0x09, 0x92, 0x01, 0x99, 0x01, 0x91, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s6 - s0;
            uint256_t const &s1 = top[-1];
            uint256_t r15;
            runtime::addmod(&r15, &s1, &t1, &s6);
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, s9, r15);
            uint256_t const k18_1 = uint256_t{0xeccd4f3eb878331aull, 0x7b26b7488dc6d26eull, 0xa19b0361d9130cd4ull, 0x2a734ebb326341efull};
            uint256_t r18;
            runtime::mulmod(&r18, &s0, &k18_1, &s6);
            uint256_t const t2 = s9 + uint256_t{0x20ull};
            uint256_t const &s2 = top[-2];
            uint256_t const t3 = s2 + uint256_t{0x1ull};
            top[-9] = t2;
            top[-2] = t3;
            top[0] = r18;
            MONAD_AOT_TAIL return b_80a<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_975(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x51, 0x92, 0x61, 0x60, 0x85, 0x01, 0x51, 0x94, 0x01, 0x51, 0x90, 0x5f, 0x81, 0x52, 0x60, 0x81, 0x01, 0x93, 0x5f, 0x85, 0x52, 0x61, 0x60, 0x83, 0x01, 0x91, 0x61, 0x81, 0x01, 0x35, 0x83, 0x52, 0x01, 0x35, 0x60, 0x83, 0x01, 0x52, 0x5f, 0x60, 0x83, 0x01, 0x53, 0x60, 0x60, 0x83, 0x01, 0x53, 0x5f, 0x60, 0x83, 0x01, 0x53, 0x60, 0x80, 0x60, 0x84, 0x01, 0x53, 0x60, 0x60, 0x84, 0x01, 0x53, 0x80, 0x60, 0x84, 0x01, 0x53, 0x60, 0x91, 0x82, 0x60, 0x85, 0x01, 0x53, 0x82, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x84, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 3, 11));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1013)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x51, 0x92, 0x61, 0x60, 0x85, 0x01, 0x51, 0x94, 0x01, 0x51, 0x90, 0x5f, 0x81, 0x52, 0x60, 0x81, 0x01, 0x93, 0x5f, 0x85, 0x52, 0x61, 0x60, 0x83, 0x01, 0x91, 0x61, 0x81, 0x01, 0x35, 0x83, 0x52, 0x01, 0x35, 0x60, 0x83, 0x01, 0x52, 0x5f, 0x60, 0x83, 0x01, 0x53, 0x60, 0x60, 0x83, 0x01, 0x53, 0x5f, 0x60, 0x83, 0x01, 0x53, 0x60, 0x80, 0x60, 0x84, 0x01, 0x53, 0x60, 0x60, 0x84, 0x01, 0x53, 0x80, 0x60, 0x84, 0x01, 0x53, 0x60, 0x91, 0x82, 0x60, 0x85, 0x01, 0x53, 0x82, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x60, 0x85, 0x01, 0x53, 0x60, 0x84, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x60ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = t1 + uint256_t{0x1c0ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, uint256_t{0x0ull});
            uint256_t const t6 = s2 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0x0ull});
            uint256_t const t7 = s2 + uint256_t{0x40ull};
            uint256_t const &s0 = top[0];
            uint256_t const t8 = s0 + uint256_t{0x320ull};
            uint256_t const t9 = aot::calldataload(ctx, t8);
            aot::mstore<traits>(ctx, gas, t7, t9);
            uint256_t const t10 = s0 + uint256_t{0x340ull};
            uint256_t const t11 = aot::calldataload(ctx, t10);
            uint256_t const t12 = s2 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t12, t11);
            uint256_t const t13 = s2 + uint256_t{0x80ull};
            aot::mstore8<traits>(ctx, gas, t13, uint256_t{0x0ull});
            gas = ctx->gas_remaining;
            uint256_t const t14 = s2 + uint256_t{0x81ull};
            aot::mstore8<traits>(ctx, gas, t14, uint256_t{0x30ull});
            gas = ctx->gas_remaining;
            uint256_t const t15 = s2 + uint256_t{0x82ull};
            aot::mstore8<traits>(ctx, gas, t15, uint256_t{0x0ull});
            gas = ctx->gas_remaining;
            uint256_t const t16 = s2 + uint256_t{0x83ull};
            aot::mstore8<traits>(ctx, gas, t16, uint256_t{0x42ull});
            gas = ctx->gas_remaining;
            uint256_t const t17 = s2 + uint256_t{0x84ull};
            aot::mstore8<traits>(ctx, gas, t17, uint256_t{0x53ull});
            gas = ctx->gas_remaining;
            uint256_t const t18 = s2 + uint256_t{0x85ull};
            aot::mstore8<traits>(ctx, gas, t18, uint256_t{0x42ull});
            gas = ctx->gas_remaining;
            uint256_t const t19 = s2 + uint256_t{0x86ull};
            aot::mstore8<traits>(ctx, gas, t19, uint256_t{0x32ull});
            gas = ctx->gas_remaining;
            uint256_t const t20 = s2 + uint256_t{0x87ull};
            aot::mstore8<traits>(ctx, gas, t20, uint256_t{0x32ull});
            gas = ctx->gas_remaining;
            uint256_t const t21 = s2 + uint256_t{0x88ull};
            aot::mstore8<traits>(ctx, gas, t21, uint256_t{0x2dull});
            gas = ctx->gas_remaining;
            uint256_t const t22 = s2 + uint256_t{0x89ull};
            aot::mstore8<traits>(ctx, gas, t22, uint256_t{0x50ull});
            gas = ctx->gas_remaining;
            uint256_t const t23 = s2 + uint256_t{0x8aull};
            aot::mstore8<traits>(ctx, gas, t23, uint256_t{0x6cull});
            gas = ctx->gas_remaining;
            uint256_t const t24 = s2 + uint256_t{0x8bull};
            aot::mstore8<traits>(ctx, gas, t24, uint256_t{0x6full});
            gas = ctx->gas_remaining;
            uint256_t const t25 = s2 + uint256_t{0x8cull};
            aot::mstore8<traits>(ctx, gas, t25, uint256_t{0x6eull});
            gas = ctx->gas_remaining;
            uint256_t const t26 = s2 + uint256_t{0x8dull};
            aot::mstore8<traits>(ctx, gas, t26, uint256_t{0x6bull});
            gas = ctx->gas_remaining;
            uint256_t const t27 = s2 + uint256_t{0x8eull};
            aot::mstore8<traits>(ctx, gas, t27, uint256_t{0xbull});
            gas = ctx->gas_remaining;
            uint256_t const t28 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k125_1 = uint256_t{0x2ull};
            uint256_t const k125_3 = uint256_t{0x8full};
            uint256_t const k125_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r125;
            runtime::staticcall<traits>(ctx, &r125, &t28, &k125_1, &s2, &k125_3, &s2, &k125_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t29 = aot::from_bool(!aot::nonzero(r125));
            bool const j128 = aot::nonzero(t29);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m2 = s2;
            top[-2] = t3;
            top[-1] = t6;
            top[0] = m1;
            top[1] = t5;
            top[2] = m2;
            top[3] = uint256_t{0x32ull};
            top[4] = uint256_t{0x42ull};
            top[5] = t7;
            top += 5;
            if (j128) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_a20<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a20(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x83, 0x51, 0x90, 0x60, 0x88, 0x53, 0x82, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x82, 0x60, 0x86, 0x01, 0x53, 0x83, 0x60, 0x86, 0x01, 0x53, 0x83, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x85, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x83, 0x51, 0x90, 0x60, 0x88, 0x53, 0x82, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x82, 0x60, 0x86, 0x01, 0x53, 0x83, 0x60, 0x86, 0x01, 0x53, 0x83, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x60, 0x86, 0x01, 0x53, 0x60, 0x85, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const &s6 = top[-6];
            aot::mstore8<traits>(ctx, gas, s6, uint256_t{0x1ull});
            gas = ctx->gas_remaining;
            uint256_t const t2 = s3 + uint256_t{0x21ull};
            uint256_t const &s1 = top[-1];
            aot::mstore8<traits>(ctx, gas, t2, s1);
            gas = ctx->gas_remaining;
            uint256_t const t3 = s3 + uint256_t{0x22ull};
            aot::mstore8<traits>(ctx, gas, t3, uint256_t{0x53ull});
            gas = ctx->gas_remaining;
            uint256_t const t4 = s3 + uint256_t{0x23ull};
            aot::mstore8<traits>(ctx, gas, t4, s1);
            gas = ctx->gas_remaining;
            uint256_t const t5 = s3 + uint256_t{0x24ull};
            uint256_t const &s2 = top[-2];
            aot::mstore8<traits>(ctx, gas, t5, s2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = s3 + uint256_t{0x25ull};
            aot::mstore8<traits>(ctx, gas, t6, s2);
            gas = ctx->gas_remaining;
            uint256_t const t7 = s3 + uint256_t{0x26ull};
            aot::mstore8<traits>(ctx, gas, t7, uint256_t{0x2dull});
            gas = ctx->gas_remaining;
            uint256_t const t8 = s3 + uint256_t{0x27ull};
            aot::mstore8<traits>(ctx, gas, t8, uint256_t{0x50ull});
            gas = ctx->gas_remaining;
            uint256_t const t9 = s3 + uint256_t{0x28ull};
            aot::mstore8<traits>(ctx, gas, t9, uint256_t{0x6cull});
            gas = ctx->gas_remaining;
            uint256_t const t10 = s3 + uint256_t{0x29ull};
            aot::mstore8<traits>(ctx, gas, t10, uint256_t{0x6full});
            gas = ctx->gas_remaining;
            uint256_t const t11 = s3 + uint256_t{0x2aull};
            aot::mstore8<traits>(ctx, gas, t11, uint256_t{0x6eull});
            gas = ctx->gas_remaining;
            uint256_t const t12 = s3 + uint256_t{0x2bull};
            aot::mstore8<traits>(ctx, gas, t12, uint256_t{0x6bull});
            gas = ctx->gas_remaining;
            uint256_t const t13 = s3 + uint256_t{0x2cull};
            aot::mstore8<traits>(ctx, gas, t13, uint256_t{0xbull});
            gas = ctx->gas_remaining;
            uint256_t const t14 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k72_1 = uint256_t{0x2ull};
            uint256_t const k72_3 = uint256_t{0x2dull};
            uint256_t const k72_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r72;
            runtime::staticcall<traits>(ctx, &r72, &t14, &k72_1, &s3, &k72_3, &s3, &k72_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t15 = aot::from_bool(!aot::nonzero(r72));
            bool const j75 = aot::nonzero(t15);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top += 1;
            if (j75) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_a86<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_a86(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x60, 0x91, 0x85, 0x51, 0x18, 0x88, 0x52, 0x53, 0x80, 0x60, 0x84, 0x01, 0x53, 0x60, 0x81, 0x84, 0x01, 0x53, 0x60, 0x83, 0x01, 0x53, 0x80, 0x60, 0x83, 0x01, 0x53, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x84, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 8, 2));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x60, 0x91, 0x85, 0x51, 0x18, 0x88, 0x52, 0x53, 0x80, 0x60, 0x84, 0x01, 0x53, 0x60, 0x81, 0x84, 0x01, 0x53, 0x60, 0x83, 0x01, 0x53, 0x80, 0x60, 0x83, 0x01, 0x53, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x60, 0x82, 0x01, 0x53, 0x60, 0x84, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s4);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = t1 ^ s1;
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, t2);
            uint256_t const &s0 = top[0];
            aot::mstore8<traits>(ctx, gas, s0, uint256_t{0x2ull});
            gas = ctx->gas_remaining;
            uint256_t const t3 = s4 + uint256_t{0x41ull};
            uint256_t const &s2 = top[-2];
            aot::mstore8<traits>(ctx, gas, t3, s2);
            gas = ctx->gas_remaining;
            uint256_t const t4 = s4 + s2;
            aot::mstore8<traits>(ctx, gas, t4, uint256_t{0x53ull});
            gas = ctx->gas_remaining;
            uint256_t const t5 = s4 + uint256_t{0x43ull};
            aot::mstore8<traits>(ctx, gas, t5, s2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = s4 + uint256_t{0x44ull};
            uint256_t const &s3 = top[-3];
            aot::mstore8<traits>(ctx, gas, t6, s3);
            gas = ctx->gas_remaining;
            uint256_t const t7 = s4 + uint256_t{0x45ull};
            aot::mstore8<traits>(ctx, gas, t7, s3);
            gas = ctx->gas_remaining;
            uint256_t const t8 = s4 + uint256_t{0x46ull};
            aot::mstore8<traits>(ctx, gas, t8, uint256_t{0x2dull});
            gas = ctx->gas_remaining;
            uint256_t const t9 = s4 + uint256_t{0x47ull};
            aot::mstore8<traits>(ctx, gas, t9, uint256_t{0x50ull});
            gas = ctx->gas_remaining;
            uint256_t const t10 = s4 + uint256_t{0x48ull};
            aot::mstore8<traits>(ctx, gas, t10, uint256_t{0x6cull});
            gas = ctx->gas_remaining;
            uint256_t const t11 = s4 + uint256_t{0x49ull};
            aot::mstore8<traits>(ctx, gas, t11, uint256_t{0x6full});
            gas = ctx->gas_remaining;
            uint256_t const t12 = s4 + uint256_t{0x4aull};
            aot::mstore8<traits>(ctx, gas, t12, uint256_t{0x6eull});
            gas = ctx->gas_remaining;
            uint256_t const t13 = s4 + uint256_t{0x4bull};
            aot::mstore8<traits>(ctx, gas, t13, uint256_t{0x6bull});
            gas = ctx->gas_remaining;
            uint256_t const t14 = s4 + uint256_t{0x4cull};
            aot::mstore8<traits>(ctx, gas, t14, uint256_t{0xbull});
            gas = ctx->gas_remaining;
            uint256_t const t15 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k72_1 = uint256_t{0x2ull};
            uint256_t const k72_3 = uint256_t{0x2dull};
            uint256_t const k72_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r72;
            runtime::staticcall<traits>(ctx, &r72, &t15, &k72_1, &s7, &k72_3, &s7, &k72_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t16 = aot::from_bool(!aot::nonzero(r72));
            bool const j75 = aot::nonzero(t16);
            top += -4;
            if (j75) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_aeb<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_aeb(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x62, 0x94, 0x61, 0x92, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x96, 0x87, 0x80, 0x97, 0x81, 0x70, 0x87, 0x51, 0x09, 0x90, 0x51, 0x60, 0x1c, 0x90, 0x08, 0x95, 0x01, 0x91, 0x61, 0x56}, 5, 8));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x62, 0x94, 0x61, 0x92, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x96, 0x87, 0x80, 0x97, 0x81, 0x70, 0x87, 0x51, 0x09, 0x90, 0x51, 0x60, 0x1c, 0x90, 0x08, 0x95, 0x01, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k10_0 = uint256_t{0x0ull};
            uint256_t const k10_1 = uint256_t{0x1c0aull};
            uint256_t const k10_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k10_0, &k10_1, &k10_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const k23_1 = uint256_t{0x0ull, 0x0ull, 0x1ull, 0x0ull};
            uint256_t r23;
            runtime::mulmod(&r23, &t3, &k23_1, &t2);
            uint256_t const &s3 = top[-3];
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s3);
            uint256_t const t5 = aot::shr_c<128>(t4);
            uint256_t r29;
            runtime::addmod(&r29, &r23, &t5, &t2);
            uint256_t const &s2 = top[-2];
            uint256_t const t6 = s2 + uint256_t{0x99b6ddull};
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-4] = t2;
            top[-3] = t2;
            top[-2] = r29;
            top[-1] = uint256_t{0xb2aull};
            top[1] = t6;
            top[2] = m1;
            top[3] = m4;
            top += 3;
            MONAD_AOT_TAIL return b_b31<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b2a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x09, 0x5f, 0x08, 0x90, 0x56}, 5, 0));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x09, 0x5f, 0x08, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::mulmod(&r2, &s1, &s0, &s2);
            uint256_t const k4_0 = uint256_t{0x0ull};
            uint256_t const &s3 = top[-3];
            uint256_t r4;
            runtime::addmod(&r4, &k4_0, &r2, &s3);
            uint256_t const &s4 = top[-4];
            uint64_t const jt = aot::jump_offset(s4);
            top[-4] = r4;
            top += -4;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_b31(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x91, 0x92, 0x60, 0x93, 0x84, 0x82, 0x52, 0x84, 0x80, 0x83, 0x01, 0x52, 0x84, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x93, 0x84, 0x60, 0x83, 0x01, 0x52, 0x80, 0x82, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x91, 0x92, 0x60, 0x93, 0x84, 0x82, 0x52, 0x84, 0x80, 0x83, 0x01, 0x52, 0x84, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x60, 0x82, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x93, 0x84, 0x60, 0x83, 0x01, 0x52, 0x80, 0x82, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, uint256_t{0x20ull});
            uint256_t const t1 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x20ull});
            uint256_t const t2 = s3 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x20ull});
            uint256_t const t3 = s3 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0xeccd4f3eb878331aull, 0x7b26b7488dc6d26eull, 0xa19b0361d9130cd4ull, 0x2a734ebb326341efull});
            uint256_t const t4 = s3 + uint256_t{0x80ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t4, s2);
            uint256_t const t5 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k34_0 = uint256_t{0x0ull};
            uint256_t const k34_1 = uint256_t{0x1c0aull};
            uint256_t const k34_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k34_0, &k34_1, &k34_2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t5);
            uint256_t const t7 = s3 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k51_1 = uint256_t{0x5ull};
            uint256_t const k51_3 = uint256_t{0xc0ull};
            uint256_t const k51_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r51;
            runtime::staticcall<traits>(ctx, &r51, &t8, &k51_1, &s3, &k51_3, &s3, &k51_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r51));
            bool const j54 = aot::nonzero(t9);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m3 = s3;
            top[-3] = t6;
            top[-2] = m1;
            top[-1] = m0;
            top[0] = m3;
            top[1] = uint256_t{0x20ull};
            top += 1;
            if (j54) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbd1); }
            MONAD_AOT_TAIL return b_b94<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_b94(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x90, 0x83, 0x7f, 0x61, 0x84, 0x83, 0x80, 0x96, 0x51, 0x95, 0x86, 0x82, 0x03, 0x90, 0x08, 0x61, 0x56}, 5, 7));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x90, 0x83, 0x7f, 0x61, 0x84, 0x83, 0x80, 0x96, 0x51, 0x95, 0x86, 0x82, 0x03, 0x90, 0x08, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s4 = top[-4];
            uint256_t const t2 = s4 - t1;
            uint256_t const &s2 = top[-2];
            uint256_t r15;
            runtime::addmod(&r15, &s2, &t2, &s4);
            uint256_t const m4 = s4;
            uint256_t const m1 = s1;
            top[-2] = m4;
            top[-1] = t1;
            top[0] = m4;
            top[1] = uint256_t{0x6729acf1ff053609ull, 0x6787b9b45fc54c54ull, 0x1f8030da595e7d1cull, 0x30644e5aaf0a66b9ull};
            top[2] = uint256_t{0xbcaull};
            top[3] = m1;
            top[4] = r15;
            top += 4;
            MONAD_AOT_TAIL return b_1a1b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_bca(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x09, 0x09, 0x09, 0x90, 0x56}, 8, 0));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x09, 0x09, 0x09, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r2;
            runtime::mulmod(&r2, &s3, &s1, &s2);
            uint256_t const &s0 = top[0];
            uint256_t const &s4 = top[-4];
            uint256_t r3;
            runtime::mulmod(&r3, &r2, &s0, &s4);
            uint256_t const &s5 = top[-5];
            uint256_t const &s6 = top[-6];
            uint256_t r4;
            runtime::mulmod(&r4, &r3, &s5, &s6);
            uint256_t const &s7 = top[-7];
            uint64_t const jt = aot::jump_offset(s7);
            top[-7] = r4;
            top += -7;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c05(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x60, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x80, 0x61, 0x84, 0x01, 0x51, 0x81, 0x7f, 0x61, 0x61, 0x88, 0x01, 0x83, 0x7f, 0x60, 0x8b, 0x01, 0x51, 0x08, 0x61, 0x56}, 0, 13));
            if (MONAD_UNLIKELY(top - bottom > 1011)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x60, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x80, 0x61, 0x84, 0x01, 0x51, 0x81, 0x7f, 0x61, 0x61, 0x88, 0x01, 0x83, 0x7f, 0x60, 0x8b, 0x01, 0x51, 0x08, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k10_0 = uint256_t{0x0ull};
            uint256_t const k10_1 = uint256_t{0x1c0aull};
            uint256_t const k10_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k10_0, &k10_1, &k10_2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            uint256_t const t4 = t1 + uint256_t{0x1c0ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = t1 + uint256_t{0x240ull};
            uint256_t const t7 = t1 + uint256_t{0x60ull};
            uint256_t const t8 = aot::mload<traits>(ctx, gas, t7);
            uint256_t const k32_1 = uint256_t{0x43e1f593f0000000ull, 0x2833e84879b97091ull, 0xb85045b68181585dull, 0x30644e72e131a029ull};
            uint256_t r32;
            runtime::addmod(&r32, &t8, &k32_1, &t3);
            top[1] = t1;
            top[2] = uint256_t{0x80ull};
            top[3] = t3;
            top[4] = t3;
            top[5] = t5;
            top[6] = t3;
            top[7] = uint256_t{0x6729acf1ff053609ull, 0x6787b9b45fc54c54ull, 0x1f8030da595e7d1cull, 0x30644e5aaf0a66b9ull};
            top[8] = uint256_t{0xc76ull};
            top[9] = t6;
            top[10] = r32;
            top += 10;
            MONAD_AOT_TAIL return b_1a1b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c76(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x09, 0x09, 0x81, 0x84, 0x51, 0x80, 0x92, 0x09, 0x09, 0x91, 0x01, 0x52, 0x56}, 9, 0));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x09, 0x09, 0x81, 0x84, 0x51, 0x80, 0x92, 0x09, 0x09, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::mulmod(&r1, &s0, &s1, &s2);
            uint256_t const &s3 = top[-3];
            uint256_t const &s4 = top[-4];
            uint256_t r2;
            runtime::mulmod(&r2, &r1, &s3, &s4);
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s7);
            uint256_t const &s5 = top[-5];
            uint256_t r8;
            runtime::mulmod(&r8, &r2, &t1, &s5);
            uint256_t r9;
            runtime::mulmod(&r9, &r8, &t1, &s5);
            uint256_t const &s6 = top[-6];
            uint256_t const t2 = s7 + s6;
            aot::mstore<traits>(ctx, gas, t2, r9);
            uint256_t const &s8 = top[-8];
            uint64_t const jt = aot::jump_offset(s8);
            top += -9;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_c84(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x91, 0x61, 0x81, 0x01, 0x51, 0x83, 0x82, 0x01, 0x52, 0x61, 0x81, 0x01, 0x51, 0x61, 0x82, 0x01, 0x52, 0x61, 0x92, 0x83, 0x83, 0x01, 0x35, 0x84, 0x83, 0x01, 0x52, 0x61, 0x80, 0x84, 0x01, 0x35, 0x81, 0x84, 0x01, 0x52, 0x61, 0x93, 0x61, 0x81, 0x01, 0x35, 0x85, 0x85, 0x01, 0x52, 0x82, 0x81, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x84, 0x81, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x81, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x94, 0x60, 0x84, 0x86, 0x01, 0x87, 0x86, 0x88, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 1, 12));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1012)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x91, 0x61, 0x81, 0x01, 0x51, 0x83, 0x82, 0x01, 0x52, 0x61, 0x81, 0x01, 0x51, 0x61, 0x82, 0x01, 0x52, 0x61, 0x92, 0x83, 0x83, 0x01, 0x35, 0x84, 0x83, 0x01, 0x52, 0x61, 0x80, 0x84, 0x01, 0x35, 0x81, 0x84, 0x01, 0x52, 0x61, 0x93, 0x61, 0x81, 0x01, 0x35, 0x85, 0x85, 0x01, 0x52, 0x82, 0x81, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x84, 0x81, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x81, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x94, 0x60, 0x84, 0x86, 0x01, 0x87, 0x86, 0x88, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x160ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = t1 + uint256_t{0x180ull};
            uint256_t const t6 = aot::mload<traits>(ctx, gas, t5);
            uint256_t const t7 = t1 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const &s0 = top[0];
            uint256_t const t8 = s0 + uint256_t{0x280ull};
            uint256_t const t9 = aot::calldataload(ctx, t8);
            uint256_t const t10 = t1 + uint256_t{0x280ull};
            aot::mstore<traits>(ctx, gas, t10, t9);
            uint256_t const t11 = s0 + uint256_t{0x2a0ull};
            uint256_t const t12 = aot::calldataload(ctx, t11);
            uint256_t const t13 = t1 + uint256_t{0x2a0ull};
            aot::mstore<traits>(ctx, gas, t13, t12);
            uint256_t const t14 = s0 + uint256_t{0x220ull};
            uint256_t const t15 = aot::calldataload(ctx, t14);
            uint256_t const t16 = t1 + uint256_t{0x2c0ull};
            aot::mstore<traits>(ctx, gas, t16, t15);
            uint256_t const t17 = s0 + uint256_t{0x240ull};
            uint256_t const t18 = aot::calldataload(ctx, t17);
            uint256_t const t19 = t1 + uint256_t{0x2e0ull};
            aot::mstore<traits>(ctx, gas, t19, t18);
            uint256_t const t20 = s0 + uint256_t{0x2c0ull};
            uint256_t const t21 = aot::calldataload(ctx, t20);
            uint256_t const t22 = t1 + uint256_t{0x300ull};
            aot::mstore<traits>(ctx, gas, t22, t21);
            uint256_t const t23 = s0 + uint256_t{0x2e0ull};
            uint256_t const t24 = aot::calldataload(ctx, t23);
            uint256_t const t25 = t1 + uint256_t{0x320ull};
            aot::mstore<traits>(ctx, gas, t25, t24);
            uint256_t const t26 = t1 + uint256_t{0x60ull};
            uint256_t const t27 = aot::mload<traits>(ctx, gas, t26);
            uint256_t const t28 = t1 + uint256_t{0x340ull};
            aot::mstore<traits>(ctx, gas, t28, t27);
            uint256_t const t29 = t1 + uint256_t{0x1e0ull};
            uint256_t const t30 = aot::mload<traits>(ctx, gas, t29);
            uint256_t const t31 = t1 + uint256_t{0x360ull};
            aot::mstore<traits>(ctx, gas, t31, t30);
            uint256_t const t32 = t1 + uint256_t{0x240ull};
            uint256_t const t33 = t1 + uint256_t{0x240ull};
            uint256_t const t34 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k103_1 = uint256_t{0x2ull};
            uint256_t const k103_3 = uint256_t{0x140ull};
            uint256_t const k103_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r103;
            runtime::staticcall<traits>(ctx, &r103, &t34, &k103_1, &t33, &k103_3, &t32, &k103_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t35 = aot::from_bool(!aot::nonzero(r103));
            bool const j106 = aot::nonzero(t35);
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x280ull};
            top[1] = uint256_t{0x140ull};
            top[2] = t1;
            top[3] = uint256_t{0x240ull};
            top[4] = uint256_t{0x2a0ull};
            top[5] = m0;
            top[6] = uint256_t{0x2c0ull};
            top += 6;
            if (j106) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x100a); }
            MONAD_AOT_TAIL return b_d15<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_d15(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x84, 0x86, 0x01, 0x51, 0x06, 0x95, 0x87, 0x83, 0x01, 0x35, 0x85, 0x87, 0x01, 0x52, 0x83, 0x83, 0x01, 0x35, 0x61, 0x87, 0x01, 0x52, 0x61, 0x88, 0x87, 0x01, 0x88, 0x84, 0x86, 0x01, 0x88, 0x8a, 0x01, 0x61, 0x56}, 7, 7));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x84, 0x86, 0x01, 0x51, 0x06, 0x95, 0x87, 0x83, 0x01, 0x35, 0x85, 0x87, 0x01, 0x52, 0x83, 0x83, 0x01, 0x35, 0x61, 0x87, 0x01, 0x52, 0x61, 0x88, 0x87, 0x01, 0x88, 0x84, 0x86, 0x01, 0x88, 0x8a, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k6_0 = uint256_t{0x0ull};
            uint256_t const k6_1 = uint256_t{0x1c0aull};
            uint256_t const k6_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k6_0, &k6_1, &k6_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s4 = top[-4];
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s4 + s3;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = aot::umod(t4, t2);
            uint256_t const &s1 = top[-1];
            uint256_t const &s6 = top[-6];
            uint256_t const t6 = s1 + s6;
            uint256_t const t7 = aot::calldataload(ctx, t6);
            uint256_t const t8 = s4 + s3;
            aot::mstore<traits>(ctx, gas, t8, t7);
            uint256_t const &s2 = top[-2];
            uint256_t const t9 = s1 + s2;
            uint256_t const t10 = aot::calldataload(ctx, t9);
            uint256_t const t11 = s4 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = s4 + s6;
            uint256_t const &s0 = top[0];
            uint256_t const t13 = s1 + s0;
            uint256_t const t14 = s4 + s3;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-5] = t5;
            top[1] = m5;
            top[2] = uint256_t{0xd4cull};
            top[3] = t12;
            top[4] = t5;
            top[5] = t13;
            top[6] = t14;
            top += 6;
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d4c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x88, 0x87, 0x01, 0x88, 0x61, 0x86, 0x01, 0x61, 0x8a, 0x01, 0x61, 0x56}, 8, 6));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x88, 0x87, 0x01, 0x88, 0x61, 0x86, 0x01, 0x61, 0x8a, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s7 = top[-7];
            uint256_t const t1 = s5 + s7;
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + uint256_t{0x220ull};
            uint256_t const t3 = s5 + uint256_t{0x160ull};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[1] = uint256_t{0xd62ull};
            top[2] = t1;
            top[3] = m6;
            top[4] = t2;
            top[5] = t3;
            top += 5;
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d62(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x85, 0x01, 0x61, 0x87, 0x61, 0x85, 0x01, 0x83, 0x61, 0x56}, 7, 5));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x85, 0x01, 0x61, 0x87, 0x61, 0x85, 0x01, 0x83, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s5 + s0;
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s2 + uint256_t{0x260ull};
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[0] = t1;
            top[1] = uint256_t{0xd73ull};
            top[2] = m6;
            top[3] = t2;
            top[4] = t1;
            top += 4;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_d73(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x86, 0x89, 0x01, 0x90, 0x81, 0x52, 0x7f, 0x85, 0x88, 0x01, 0x52, 0x90, 0x51, 0x82, 0x87, 0x01, 0x52, 0x60, 0x90, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 8, 5));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x86, 0x89, 0x01, 0x90, 0x81, 0x52, 0x7f, 0x85, 0x88, 0x01, 0x52, 0x90, 0x51, 0x82, 0x87, 0x01, 0x52, 0x60, 0x90, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s7 + s5;
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x9fa44c281ac9b03bull, 0x99638b304ed8310eull, 0x74d5059b63554fabull, 0x1fa4be93b5e7f7e6ull});
            uint256_t const &s3 = top[-3];
            uint256_t const t2 = s5 + s3;
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0xfb3737e6c389b721ull, 0x60f3241e79a5f48full, 0x9d3cb5a5e71fd311ull, 0x1a01ae7fac6228e3ull});
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const &s1 = top[-1];
            uint256_t const t4 = s5 + s1;
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k25_1 = uint256_t{0x7ull};
            uint256_t const k25_3 = uint256_t{0x60ull};
            uint256_t const k25_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r25;
            runtime::staticcall<traits>(ctx, &r25, &t5, &k25_1, &t1, &k25_3, &t1, &k25_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::from_bool(!aot::nonzero(r25));
            bool const j28 = aot::nonzero(t6);
            top += -1;
            if (j28) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_dd5<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_dd5(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x61, 0x96, 0x61, 0x93, 0x61, 0x61, 0x9a, 0x87, 0x8a, 0x01, 0x51, 0x97, 0x7f, 0x98, 0x89, 0x03, 0x90, 0x8b, 0x01, 0x52, 0x61, 0x86, 0x8b, 0x01, 0x82, 0x8c, 0x01, 0x8c, 0x61, 0x80, 0x82, 0x01, 0x91, 0x01, 0x61, 0x56}, 7, 12));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1012)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x61, 0x96, 0x61, 0x93, 0x61, 0x61, 0x9a, 0x87, 0x8a, 0x01, 0x51, 0x97, 0x7f, 0x98, 0x89, 0x03, 0x90, 0x8b, 0x01, 0x52, 0x61, 0x86, 0x8b, 0x01, 0x82, 0x8c, 0x01, 0x8c, 0x61, 0x80, 0x82, 0x01, 0x91, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s4 = top[-4];
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s4 + s2;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x3c208c16d87cfd47ull, 0x97816a916871ca8dull, 0xb85045b68181585dull, 0x30644e72e131a029ull} - t2;
            uint256_t const t4 = s4 + s2;
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s0 = top[0];
            uint256_t const t5 = s4 + s0;
            uint256_t const &s6 = top[-6];
            uint256_t const t6 = s4 + s6;
            uint256_t const t7 = s4 + uint256_t{0x160ull};
            uint256_t const t8 = s4 + uint256_t{0x160ull};
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m6 = s6;
            top[-6] = uint256_t{0x1008ull};
            top[-5] = uint256_t{0x300ull};
            top[-2] = uint256_t{0x3c208c16d87cfd47ull, 0x97816a916871ca8dull, 0xb85045b68181585dull, 0x30644e72e131a029ull};
            top[-1] = uint256_t{0xe95ull};
            top[1] = uint256_t{0xe84ull};
            top[2] = m5;
            top[3] = m1;
            top[4] = uint256_t{0xe3dull};
            top[5] = m6;
            top[6] = uint256_t{0xe2aull};
            top[7] = t5;
            top[8] = t6;
            top[9] = t7;
            top[10] = t8;
            top += 10;
            MONAD_AOT_TAIL return b_18da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e2a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x8a, 0x01, 0x51, 0x8a, 0x8c, 0x01, 0x91, 0x84, 0x01, 0x87, 0x8c, 0x01, 0x61, 0x56}, 11, 4));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x8a, 0x01, 0x51, 0x8a, 0x8c, 0x01, 0x91, 0x84, 0x01, 0x87, 0x8c, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s9 = top[-9];
            uint256_t const t1 = s9 + uint256_t{0x60ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s10 = top[-10];
            uint256_t const t3 = s10 + s9;
            uint256_t const &s2 = top[-2];
            uint256_t const &s0 = top[0];
            uint256_t const t4 = s2 + s0;
            uint256_t const &s5 = top[-5];
            uint256_t const t5 = s9 + s5;
            top[0] = t3;
            top[1] = t2;
            top[2] = t4;
            top[3] = t5;
            top += 3;
            MONAD_AOT_TAIL return b_195d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e3d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x83, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x8a, 0x8a, 0x01, 0x93, 0x81, 0x7f, 0x60, 0x8d, 0x01, 0x51, 0x09, 0x90, 0x09, 0x91, 0x01, 0x84, 0x89, 0x01, 0x61, 0x56}, 9, 7));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x83, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x8a, 0x8a, 0x01, 0x93, 0x81, 0x7f, 0x60, 0x8d, 0x01, 0x51, 0x09, 0x90, 0x09, 0x91, 0x01, 0x84, 0x89, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k8_0 = uint256_t{0x0ull};
            uint256_t const k8_1 = uint256_t{0x1c0aull};
            uint256_t const k8_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k8_0, &k8_1, &k8_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s7 = top[-7];
            uint256_t const &s8 = top[-8];
            uint256_t const t3 = s7 + s8;
            uint256_t const t4 = s7 + uint256_t{0x60ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const k23_1 = uint256_t{0xeccd4f3eb878331aull, 0x7b26b7488dc6d26eull, 0xa19b0361d9130cd4ull, 0x2a734ebb326341efull};
            uint256_t r23;
            runtime::mulmod(&r23, &t5, &k23_1, &t2);
            uint256_t const &s1 = top[-1];
            uint256_t r25;
            runtime::mulmod(&r25, &s1, &r23, &t2);
            uint256_t const &s0 = top[0];
            uint256_t const &s3 = top[-3];
            uint256_t const t6 = s0 + s3;
            uint256_t const t7 = s7 + s3;
            top[-1] = t3;
            top[0] = r25;
            top[1] = t6;
            top[2] = t7;
            top += 2;
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e84(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x84, 0x86, 0x01, 0x90, 0x85, 0x01, 0x61, 0x86, 0x01, 0x80, 0x61, 0x56}, 6, 4));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x84, 0x86, 0x01, 0x90, 0x85, 0x01, 0x61, 0x86, 0x01, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s5 + s4;
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s4 + s0;
            uint256_t const t3 = s4 + uint256_t{0x160ull};
            top[0] = t1;
            top[1] = t2;
            top[2] = t3;
            top[3] = t3;
            top += 3;
            MONAD_AOT_TAIL return b_18da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_e95(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x83, 0x01, 0x51, 0x90, 0x03, 0x90, 0x81, 0x61, 0x84, 0x01, 0x52, 0x61, 0x83, 0x01, 0x51, 0x84, 0x84, 0x01, 0x52, 0x61, 0x83, 0x01, 0x51, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x82, 0x01, 0x51, 0x61, 0x83, 0x01, 0x52, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x01, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x83, 0x01, 0x51, 0x90, 0x03, 0x90, 0x81, 0x61, 0x84, 0x01, 0x52, 0x61, 0x83, 0x01, 0x51, 0x84, 0x84, 0x01, 0x52, 0x61, 0x83, 0x01, 0x51, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x7f, 0x61, 0x84, 0x01, 0x52, 0x82, 0x01, 0x51, 0x61, 0x83, 0x01, 0x52, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x7f, 0x61, 0x82, 0x01, 0x52, 0x01, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x260ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 - t2;
            uint256_t const t4 = s2 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s2 + uint256_t{0x160ull};
            uint256_t const t6 = aot::mload<traits>(ctx, gas, t5);
            uint256_t const &s3 = top[-3];
            uint256_t const t7 = s2 + s3;
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const t8 = s2 + uint256_t{0x180ull};
            uint256_t const t9 = aot::mload<traits>(ctx, gas, t8);
            uint256_t const t10 = s2 + uint256_t{0x320ull};
            aot::mstore<traits>(ctx, gas, t10, t9);
            uint256_t const t11 = s2 + uint256_t{0x340ull};
            aot::mstore<traits>(ctx, gas, t11, uint256_t{0x97e485b7aef312c2ull, 0xf1aa493335a9e712ull, 0x7260bfb731fb5d25ull, 0x198e9393920d483aull});
            uint256_t const t12 = s2 + uint256_t{0x360ull};
            aot::mstore<traits>(ctx, gas, t12, uint256_t{0x46debd5cd992f6edull, 0x674322d4f75edaddull, 0x426a00665e5c4479ull, 0x1800deef121f1e76ull});
            uint256_t const t13 = s2 + uint256_t{0x380ull};
            aot::mstore<traits>(ctx, gas, t13, uint256_t{0x55acdadcd122975bull, 0xbc4b313370b38ef3ull, 0xec9e99ad690c3395ull, 0x90689d0585ff075ull});
            uint256_t const t14 = s2 + uint256_t{0x3a0ull};
            aot::mstore<traits>(ctx, gas, t14, uint256_t{0x4ce6cc0166fa7daaull, 0xe3d1e7690c43d37bull, 0x4aab71808dcb408full, 0x12c85ea5db8c6debull});
            uint256_t const &s1 = top[-1];
            uint256_t const t15 = s2 + s1;
            uint256_t const t16 = aot::mload<traits>(ctx, gas, t15);
            uint256_t const t17 = s2 + uint256_t{0x3c0ull};
            aot::mstore<traits>(ctx, gas, t17, t16);
            uint256_t const t18 = s2 + uint256_t{0x3e0ull};
            aot::mstore<traits>(ctx, gas, t18, t3);
            uint256_t const t19 = s2 + uint256_t{0x400ull};
            aot::mstore<traits>(ctx, gas, t19, uint256_t{0xdcc3708ddb954a48ull, 0xcdf9f3eb1224504full, 0x60c2430af35865e7ull, 0x22f1acbb03c45087ull});
            uint256_t const t20 = s2 + uint256_t{0x420ull};
            aot::mstore<traits>(ctx, gas, t20, uint256_t{0x103cc21c2308e1cbull, 0xaea515c6f3f6b941ull, 0xd73142ae1752429eull, 0x2a344fad01c2ed0eull});
            uint256_t const t21 = s2 + uint256_t{0x440ull};
            aot::mstore<traits>(ctx, gas, t21, uint256_t{0xb464e964845c3f8ull, 0x4c7142e5193473d8ull, 0x49aa3268f981010dull, 0x159f15b842ba9c84ull});
            uint256_t const t22 = s2 + uint256_t{0x460ull};
            aot::mstore<traits>(ctx, gas, t22, uint256_t{0x34cf8258cd428b3ull, 0xbad1532dc0293f0dull, 0x3ccbc2207587c2acull, 0xefd30ac7b6f8d0dull});
            uint256_t const t23 = s2 + s3;
            top[-3] = t23;
            top += -3;
            MONAD_AOT_TAIL return b_100f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1008(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_100f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x5f, 0x61, 0x60, 0x51, 0x93, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 1, 6));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x5f, 0x61, 0x60, 0x51, 0x93, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k9_1 = uint256_t{0x8ull};
            uint256_t const &s0 = top[0];
            uint256_t const k9_3 = uint256_t{0x180ull};
            uint256_t const k9_4 = uint256_t{0x0ull};
            uint256_t const k9_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r9;
            runtime::staticcall<traits>(ctx, &r9, &t2, &k9_1, &s0, &k9_3, &k9_4, &k9_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::from_bool(!aot::nonzero(r9));
            bool const j12 = aot::nonzero(t3);
            top[0] = t1;
            if (j12) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x102c); }
            MONAD_AOT_TAIL return b_1023<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1023(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x61, 0x5f, 0x51, 0x91, 0x01, 0x52, 0x56}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x61, 0x5f, 0x51, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const &s0 = top[0];
            uint256_t const t2 = s0 + uint256_t{0x200ull};
            aot::mstore<traits>(ctx, gas, t2, t1);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1070(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x01, 0x90, 0x61, 0x83, 0x01, 0x61, 0x84, 0x01, 0x61, 0x91, 0x82, 0x86, 0x01, 0x51, 0x80, 0x61, 0x88, 0x01, 0x94, 0x60, 0x89, 0x01, 0x51, 0x86, 0x52, 0x81, 0x61, 0x8a, 0x01, 0x51, 0x61, 0x90, 0x81, 0x8c, 0x01, 0x52, 0x61, 0x8b, 0x01, 0x51, 0x9a, 0x61, 0x01, 0x9a, 0x8b, 0x52, 0x61, 0x8a, 0x83, 0x8b, 0x8b, 0x61, 0x56}, 1, 16));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1008)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x90, 0x61, 0x82, 0x01, 0x90, 0x61, 0x83, 0x01, 0x61, 0x84, 0x01, 0x61, 0x91, 0x82, 0x86, 0x01, 0x51, 0x80, 0x61, 0x88, 0x01, 0x94, 0x60, 0x89, 0x01, 0x51, 0x86, 0x52, 0x81, 0x61, 0x8a, 0x01, 0x51, 0x61, 0x90, 0x81, 0x8c, 0x01, 0x52, 0x61, 0x8b, 0x01, 0x51, 0x9a, 0x61, 0x01, 0x9a, 0x8b, 0x52, 0x61, 0x8a, 0x83, 0x8b, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            uint256_t const t3 = t1 + uint256_t{0x260ull};
            uint256_t const t4 = t1 + uint256_t{0x280ull};
            uint256_t const t5 = t1 + uint256_t{0x1e0ull};
            uint256_t const t6 = aot::mload<traits>(ctx, gas, t5);
            uint256_t const t7 = t1 + uint256_t{0x160ull};
            uint256_t const t8 = t1 + uint256_t{0xe0ull};
            uint256_t const t9 = aot::mload<traits>(ctx, gas, t8);
            aot::mstore<traits>(ctx, gas, t7, t9);
            uint256_t const t10 = t1 + uint256_t{0x100ull};
            uint256_t const t11 = aot::mload<traits>(ctx, gas, t10);
            uint256_t const t12 = t1 + uint256_t{0x180ull};
            aot::mstore<traits>(ctx, gas, t12, t11);
            uint256_t const t13 = t1 + uint256_t{0x120ull};
            uint256_t const t14 = aot::mload<traits>(ctx, gas, t13);
            uint256_t const t15 = uint256_t{0x140ull} + t1;
            aot::mstore<traits>(ctx, gas, t15, t14);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t15;
            top[1] = t2;
            top[2] = m0;
            top[3] = t7;
            top[4] = t4;
            top[5] = t3;
            top[6] = t6;
            top[7] = t6;
            top[8] = uint256_t{0x1e0ull};
            top[9] = t6;
            top[10] = uint256_t{0x180ull};
            top[11] = uint256_t{0x10c3ull};
            top[12] = t2;
            top[13] = t6;
            top[14] = m0;
            top[15] = t7;
            top += 15;
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10c3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x88, 0x01, 0x90, 0x61, 0x91, 0x8b, 0x61, 0x56}, 11, 3));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x88, 0x01, 0x90, 0x61, 0x91, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s8 + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-1] = uint256_t{0x10d0ull};
            top[0] = m1;
            top[1] = t1;
            top[2] = m10;
            top += 2;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10d0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x92, 0x83, 0x91, 0x82, 0x82, 0x89, 0x8d, 0x8d, 0x8d, 0x85, 0x85, 0x81, 0x81, 0x80, 0x09, 0x61, 0x85, 0x82, 0x60, 0x87, 0x01, 0x8a, 0x61, 0x56}, 9, 17));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1007)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x92, 0x83, 0x91, 0x82, 0x82, 0x89, 0x8d, 0x8d, 0x8d, 0x85, 0x85, 0x81, 0x81, 0x80, 0x09, 0x61, 0x85, 0x82, 0x60, 0x87, 0x01, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k7_0 = uint256_t{0x0ull};
            uint256_t const k7_1 = uint256_t{0x1c0aull};
            uint256_t const k7_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k7_0, &k7_1, &k7_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint256_t r26;
            runtime::mulmod(&r26, &s2, &s2, &t2);
            uint256_t const &s6 = top[-6];
            uint256_t const t3 = s6 + uint256_t{0x40ull};
            uint256_t const m2 = s2;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            uint256_t const m6 = s6;
            top[-2] = t2;
            top[0] = t2;
            top[1] = m2;
            top[2] = m0;
            top[3] = t2;
            top[4] = m2;
            top[5] = m5;
            top[6] = m8;
            top[7] = m7;
            top[8] = m6;
            top[9] = t2;
            top[10] = m2;
            top[11] = r26;
            top[12] = uint256_t{0x10fcull};
            top[13] = m7;
            top[14] = r26;
            top[15] = t3;
            top[16] = m5;
            top += 16;
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_10fc(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x86, 0x01, 0x88, 0x61, 0x56}, 6, 5));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x86, 0x01, 0x88, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x1a0ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[1] = uint256_t{0x110bull};
            top[2] = m0;
            top[3] = t1;
            top[4] = m5;
            top += 4;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_110b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x09, 0x93, 0x84, 0x92, 0x83, 0x60, 0x84, 0x01, 0x61, 0x93, 0x61, 0x56}, 7, 3));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x09, 0x93, 0x84, 0x92, 0x83, 0x60, 0x84, 0x01, 0x61, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::mulmod(&r1, &s0, &s1, &s2);
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x80ull};
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            top[-6] = r1;
            top[-4] = r1;
            top[-2] = uint256_t{0x111dull};
            top[-1] = m4;
            top[0] = r1;
            top[1] = t1;
            top[2] = m6;
            top += 2;
            MONAD_AOT_TAIL return b_19c0<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_111d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x01, 0x61, 0x92, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x01, 0x61, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x1c0ull} + s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x112aull};
            top[0] = t1;
            top[1] = m2;
            top += 1;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_112a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x09, 0x80, 0x91, 0x7f, 0x8c, 0x52, 0x8b, 0x89, 0x83, 0x7f, 0x8b, 0x52, 0x61, 0x92, 0x8d, 0x61, 0x56}, 13, 5));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x09, 0x80, 0x91, 0x7f, 0x8c, 0x52, 0x8b, 0x89, 0x83, 0x7f, 0x8b, 0x52, 0x61, 0x92, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::mulmod(&r1, &s0, &s1, &s2);
            uint256_t const &s12 = top[-12];
            aot::mstore<traits>(ctx, gas, s12, uint256_t{0x4cebef9be53ba77cull, 0x517d946564ab2422ull, 0xcdfcbab5df52610full, 0x584cfa0ab76e9f3ull});
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, uint256_t{0x33e467df6c35e803ull, 0xc73ec9135e117f3aull, 0x4f52cb632a0fa64eull, 0x2b28cd768b28dc05ull});
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const m12 = s12;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-3] = r1;
            top[-2] = r1;
            top[-1] = m3;
            top[0] = uint256_t{0x1180ull};
            top[1] = m9;
            top[2] = r1;
            top[3] = m12;
            top[4] = m10;
            top += 4;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1180(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8a, 0x01, 0x90, 0x61, 0x91, 0x8d, 0x61, 0x56}, 13, 3));
            if (MONAD_UNLIKELY(top - bottom < 13)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8a, 0x01, 0x90, 0x61, 0x91, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s10 + s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            top[-1] = uint256_t{0x118dull};
            top[0] = m1;
            top[1] = t1;
            top[2] = m12;
            top += 2;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_118d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x09, 0x7f, 0x88, 0x52, 0x7f, 0x84, 0x52, 0x61, 0x85, 0x82, 0x8a, 0x89, 0x61, 0x56}, 10, 4));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x09, 0x7f, 0x88, 0x52, 0x7f, 0x84, 0x52, 0x61, 0x85, 0x82, 0x8a, 0x89, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::mulmod(&r1, &s0, &s1, &s2);
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, s9, uint256_t{0xcf450677f29088f9ull, 0x1978749803061357ull, 0x9c3eca7c02aef089ull, 0x1c040c6eb53c43b7ull});
            uint256_t const &s5 = top[-5];
            aot::mstore<traits>(ctx, gas, s5, uint256_t{0x96d5f3395c68e091ull, 0xabe6e1928baf1117ull, 0x4192afbacdf18161ull, 0x109cf6df22bc04e6ull});
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m9 = s9;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[-2] = r1;
            top[-1] = uint256_t{0x11e0ull};
            top[0] = m6;
            top[1] = r1;
            top[2] = m9;
            top[3] = m7;
            top += 3;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11e0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x89, 0x01, 0x8b, 0x61, 0x56}, 9, 5));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x89, 0x01, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s6 = top[-6];
            uint256_t const t1 = s6 + uint256_t{0x200ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[1] = uint256_t{0x11efull};
            top[2] = m0;
            top[3] = t1;
            top[4] = m8;
            top += 4;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_11ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x09, 0x94, 0x85, 0x91, 0x7f, 0x82, 0x52, 0x7f, 0x90, 0x52, 0x61, 0x93, 0x61, 0x56}, 8, 1));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x09, 0x94, 0x85, 0x91, 0x7f, 0x82, 0x52, 0x7f, 0x90, 0x52, 0x61, 0x93, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::mulmod(&r1, &s0, &s1, &s2);
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, uint256_t{0xee38223a23d7c0feull, 0xfe154c2af083e550ull, 0x4ce8036b8bf56c68ull, 0x1dec8e22c06a93dull});
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, uint256_t{0x7c7bfe28828573bull, 0x94f82d670a09fd55ull, 0xe6c8953c911db9e5ull, 0x229df4eb55698f3bull});
            uint256_t const m7 = s7;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-7] = r1;
            top[-5] = uint256_t{0x1242ull};
            top[-3] = r1;
            top[-2] = m7;
            top[-1] = m5;
            top += -1;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1242(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x01, 0x61, 0x92, 0x61, 0x56}, 3, 2));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x01, 0x61, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = uint256_t{0x300ull} + s0;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = uint256_t{0x1008ull};
            top[0] = t1;
            top[1] = m2;
            top += 1;
            MONAD_AOT_TAIL return b_19ff<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_124f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x61, 0x91, 0x61, 0x60, 0x51, 0x91, 0x64, 0x61, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x51, 0x61, 0x90, 0x81, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x60, 0x82, 0x61, 0x86, 0x01, 0x37, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x61, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x82, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x82, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x82, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x91, 0x82, 0x81, 0x01, 0x35, 0x61, 0x86, 0x01, 0x52, 0x61, 0x81, 0x01, 0x35, 0x61, 0x86, 0x01, 0x52, 0x85, 0x61, 0x82, 0x01, 0x61, 0x87, 0x01, 0x37, 0x01, 0x35, 0x61, 0x84, 0x01, 0x52, 0x82, 0x01, 0x93, 0x84, 0x92, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 1, 10));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x61, 0x91, 0x61, 0x60, 0x51, 0x91, 0x64, 0x61, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x51, 0x61, 0x90, 0x81, 0x85, 0x01, 0x52, 0x60, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x60, 0x82, 0x61, 0x86, 0x01, 0x37, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x7f, 0x61, 0x85, 0x01, 0x52, 0x61, 0x84, 0x01, 0x51, 0x61, 0x85, 0x01, 0x52, 0x61, 0x82, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x82, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x82, 0x01, 0x35, 0x61, 0x85, 0x01, 0x52, 0x61, 0x91, 0x82, 0x81, 0x01, 0x35, 0x61, 0x86, 0x01, 0x52, 0x61, 0x81, 0x01, 0x35, 0x61, 0x86, 0x01, 0x52, 0x85, 0x61, 0x82, 0x01, 0x61, 0x87, 0x01, 0x37, 0x01, 0x35, 0x61, 0x84, 0x01, 0x52, 0x82, 0x01, 0x93, 0x84, 0x92, 0x01, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x67616d6d61ull});
            uint256_t const t3 = t1 + uint256_t{0x60ull};
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const t5 = t1 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t5, t4);
            uint256_t const t6 = t1 + uint256_t{0xe0ull};
            uint256_t const t7 = aot::mload<traits>(ctx, gas, t6);
            uint256_t const t8 = t1 + uint256_t{0x280ull};
            aot::mstore<traits>(ctx, gas, t8, t7);
            uint256_t const t9 = t1 + uint256_t{0x100ull};
            uint256_t const t10 = aot::mload<traits>(ctx, gas, t9);
            uint256_t const t11 = t1 + uint256_t{0x2a0ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = t1 + uint256_t{0x2c0ull};
            uint256_t const &s0 = top[0];
            uint256_t const k44_2 = uint256_t{0xc0ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t12, &s0, &k44_2);
            gas = ctx->gas_remaining;
            uint256_t const t13 = t1 + uint256_t{0x380ull};
            aot::mstore<traits>(ctx, gas, t13, uint256_t{0x4cebef9be53ba77cull, 0x517d946564ab2422ull, 0xcdfcbab5df52610full, 0x584cfa0ab76e9f3ull});
            uint256_t const t14 = t1 + uint256_t{0x3a0ull};
            aot::mstore<traits>(ctx, gas, t14, uint256_t{0x33e467df6c35e803ull, 0xc73ec9135e117f3aull, 0x4f52cb632a0fa64eull, 0x2b28cd768b28dc05ull});
            uint256_t const t15 = t1 + uint256_t{0x3c0ull};
            aot::mstore<traits>(ctx, gas, t15, uint256_t{0xcf450677f29088f9ull, 0x1978749803061357ull, 0x9c3eca7c02aef089ull, 0x1c040c6eb53c43b7ull});
            uint256_t const t16 = t1 + uint256_t{0x3e0ull};
            aot::mstore<traits>(ctx, gas, t16, uint256_t{0x96d5f3395c68e091ull, 0xabe6e1928baf1117ull, 0x4192afbacdf18161ull, 0x109cf6df22bc04e6ull});
            uint256_t const t17 = t1 + uint256_t{0x400ull};
            aot::mstore<traits>(ctx, gas, t17, uint256_t{0xee38223a23d7c0feull, 0xfe154c2af083e550ull, 0x4ce8036b8bf56c68ull, 0x1dec8e22c06a93dull});
            uint256_t const t18 = t1 + uint256_t{0x420ull};
            aot::mstore<traits>(ctx, gas, t18, uint256_t{0x7c7bfe28828573bull, 0x94f82d670a09fd55ull, 0xe6c8953c911db9e5ull, 0x229df4eb55698f3bull});
            uint256_t const t19 = t1 + uint256_t{0x120ull};
            uint256_t const t20 = aot::mload<traits>(ctx, gas, t19);
            uint256_t const t21 = t1 + uint256_t{0x440ull};
            aot::mstore<traits>(ctx, gas, t21, t20);
            uint256_t const t22 = s0 + uint256_t{0x180ull};
            uint256_t const t23 = aot::calldataload(ctx, t22);
            uint256_t const t24 = t1 + uint256_t{0x460ull};
            aot::mstore<traits>(ctx, gas, t24, t23);
            uint256_t const t25 = s0 + uint256_t{0x1a0ull};
            uint256_t const t26 = aot::calldataload(ctx, t25);
            uint256_t const t27 = t1 + uint256_t{0x480ull};
            aot::mstore<traits>(ctx, gas, t27, t26);
            uint256_t const t28 = s0 + uint256_t{0x1c0ull};
            uint256_t const t29 = aot::calldataload(ctx, t28);
            uint256_t const t30 = t1 + uint256_t{0x4a0ull};
            aot::mstore<traits>(ctx, gas, t30, t29);
            uint256_t const t31 = s0 + uint256_t{0x1e0ull};
            uint256_t const t32 = aot::calldataload(ctx, t31);
            uint256_t const t33 = t1 + uint256_t{0x4c0ull};
            aot::mstore<traits>(ctx, gas, t33, t32);
            uint256_t const t34 = s0 + uint256_t{0x200ull};
            uint256_t const t35 = aot::calldataload(ctx, t34);
            uint256_t const t36 = t1 + uint256_t{0x4e0ull};
            aot::mstore<traits>(ctx, gas, t36, t35);
            uint256_t const t37 = s0 + uint256_t{0x300ull};
            uint256_t const t38 = t1 + uint256_t{0x500ull};
            uint256_t const k132_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::calldatacopy<traits>(ctx, &t38, &t37, &k132_2);
            gas = ctx->gas_remaining;
            uint256_t const t39 = s0 + uint256_t{0x260ull};
            uint256_t const t40 = aot::calldataload(ctx, t39);
            uint256_t const t41 = t1 + uint256_t{0x520ull};
            aot::mstore<traits>(ctx, gas, t41, t40);
            uint256_t const t42 = t1 + uint256_t{0x1e0ull};
            uint256_t const t43 = t1 + uint256_t{0x25bull};
            uint256_t const t44 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k147_1 = uint256_t{0x2ull};
            uint256_t const k147_3 = uint256_t{0x2e5ull};
            uint256_t const k147_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r147;
            runtime::staticcall<traits>(ctx, &r147, &t44, &k147_1, &t43, &k147_3, &t42, &k147_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t45 = aot::from_bool(!aot::nonzero(r147));
            bool const j150 = aot::nonzero(t45);
            top[0] = t42;
            if (j150) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x6c9); }
            MONAD_AOT_TAIL return b_13ed<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_13ed(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x81, 0x51, 0x06, 0x90, 0x52, 0x56}, 2, 5));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x81, 0x51, 0x06, 0x90, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k6_0 = uint256_t{0x0ull};
            uint256_t const k6_1 = uint256_t{0x1c0aull};
            uint256_t const k6_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k6_0, &k6_1, &k6_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t3 = aot::mload<traits>(ctx, gas, s0);
            uint256_t const t4 = aot::umod(t3, t2);
            aot::mstore<traits>(ctx, gas, s0, t4);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1401(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x92, 0x91, 0x92, 0x60, 0x90, 0x60, 0x51, 0x94, 0x61, 0x93, 0x84, 0x87, 0x01, 0x94, 0x7f, 0x86, 0x52, 0x61, 0x88, 0x01, 0x91, 0x7f, 0x83, 0x52, 0x61, 0x89, 0x01, 0x94, 0x61, 0x82, 0x01, 0x35, 0x96, 0x86, 0x60, 0x8c, 0x01, 0x98, 0x61, 0x82, 0x82, 0x8d, 0x8d, 0x61, 0x56}, 4, 15));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1009)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x92, 0x91, 0x92, 0x60, 0x90, 0x60, 0x51, 0x94, 0x61, 0x93, 0x84, 0x87, 0x01, 0x94, 0x7f, 0x86, 0x52, 0x61, 0x88, 0x01, 0x91, 0x7f, 0x83, 0x52, 0x61, 0x89, 0x01, 0x94, 0x61, 0x82, 0x01, 0x35, 0x96, 0x86, 0x60, 0x8c, 0x01, 0x98, 0x61, 0x82, 0x82, 0x8d, 0x8d, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x7a9820468b369f61ull, 0xd1ba9a7aaaa77e9dull, 0x11644465a48353d2ull, 0x121c455821fa725dull});
            uint256_t const t3 = t1 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t3, uint256_t{0xbd82c0800c02d62bull, 0x5ee34ef256eed2baull, 0x20ab42c8fea72f97ull, 0x26fde3a359b76de1ull});
            uint256_t const t4 = t1 + uint256_t{0x280ull};
            uint256_t const &s0 = top[0];
            uint256_t const t5 = s0 + uint256_t{0x180ull};
            uint256_t const t6 = aot::calldataload(ctx, t5);
            uint256_t const t7 = t1 + uint256_t{0xe0ull};
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m0 = s0;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = t1;
            top[-2] = m3;
            top[-1] = t2;
            top[0] = t7;
            top[1] = t4;
            top[2] = m2;
            top[3] = t3;
            top[4] = uint256_t{0x240ull};
            top[5] = m0;
            top[6] = m1;
            top[7] = uint256_t{0x40ull};
            top[8] = t4;
            top[9] = t6;
            top[10] = uint256_t{0x147full};
            top[11] = t4;
            top[12] = t6;
            top[13] = t2;
            top[14] = t7;
            top += 14;
            MONAD_AOT_TAIL return b_1939<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_147f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x8b, 0x52, 0x7f, 0x87, 0x52, 0x61, 0x85, 0x01, 0x35, 0x61, 0x83, 0x82, 0x8e, 0x8e, 0x61, 0x56}, 11, 7));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x8b, 0x52, 0x7f, 0x87, 0x52, 0x61, 0x85, 0x01, 0x35, 0x61, 0x83, 0x82, 0x8e, 0x8e, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            aot::mstore<traits>(ctx, gas, s10, uint256_t{0xacaa6b6aa76dc9bcull, 0x907fcc1d4b466b17ull, 0x50b1afef6745b0afull, 0x17507f61603e878ull});
            uint256_t const &s6 = top[-6];
            aot::mstore<traits>(ctx, gas, s6, uint256_t{0x298d94160f9388f0ull, 0x183b157f4878a474ull, 0x1e1817990c4d5f4eull, 0x2b59b723a2b9d9e7ull});
            uint256_t const &s4 = top[-4];
            uint256_t const t1 = s4 + uint256_t{0x1a0ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const m10 = s10;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            top[1] = t2;
            top[2] = uint256_t{0x14d7ull};
            top[3] = m1;
            top[4] = t2;
            top[5] = m10;
            top[6] = m9;
            top += 6;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_14d7(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x8c, 0x52, 0x7f, 0x88, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x91, 0x09, 0x90, 0x61, 0x91, 0x8b, 0x8b, 0x61, 0x56}, 12, 5));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x8c, 0x52, 0x7f, 0x88, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x91, 0x09, 0x90, 0x61, 0x91, 0x8b, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, s11, uint256_t{0x7d15c53676faf662ull, 0xbcbe29b3fc6963a9ull, 0xf434653399935c68ull, 0xbf238da01b4d1aaull});
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, uint256_t{0x7d84812538a45bf4ull, 0x2660cdec96b7deeeull, 0xfd01ecb102a6ab2eull, 0x2360a9f01aa56f17ull});
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k13_0 = uint256_t{0x0ull};
            uint256_t const k13_1 = uint256_t{0x1c0aull};
            uint256_t const k13_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k13_0, &k13_1, &k13_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const &s0 = top[0];
            uint256_t r19;
            runtime::mulmod(&r19, &s1, &s0, &t2);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m11 = s11;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-2] = uint256_t{0x1539ull};
            top[-1] = m2;
            top[0] = r19;
            top[1] = m11;
            top[2] = m10;
            top += 2;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1539(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x89, 0x52, 0x7f, 0x85, 0x52, 0x61, 0x87, 0x61, 0x85, 0x01, 0x35, 0x8b, 0x8b, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x89, 0x52, 0x7f, 0x85, 0x52, 0x61, 0x87, 0x61, 0x85, 0x01, 0x35, 0x8b, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, uint256_t{0xebb9df279a537cf6ull, 0xd11eff5578c7ec31ull, 0xdf8379230a888cfaull, 0x8ccf24a4e892644ull});
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s4, uint256_t{0x7aca8c4169100478ull, 0xce0b31f0bf0a29abull, 0xb8202945fb217cb0ull, 0x28cc676be16a275dull});
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x1c0ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x1590ull};
            top[2] = m6;
            top[3] = t2;
            top[4] = m8;
            top[5] = m7;
            top += 5;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1590(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x7f, 0x89, 0x52, 0x7f, 0x85, 0x52, 0x61, 0x87, 0x8a, 0x8a, 0x80, 0x61, 0x56}, 9, 6));
            if (MONAD_UNLIKELY(top - bottom < 9)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x7f, 0x89, 0x52, 0x7f, 0x85, 0x52, 0x61, 0x87, 0x8a, 0x8a, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s8 = top[-8];
            aot::mstore<traits>(ctx, gas, s8, uint256_t{0x627e23ad313001d5ull, 0x3fbebbda6ce2f255ull, 0xc764f931db2586f8ull, 0x1140272638681e95ull});
            uint256_t const &s4 = top[-4];
            aot::mstore<traits>(ctx, gas, s4, uint256_t{0xae8e57e28ea1e0c3ull, 0x6090590a8dff8966ull, 0xf23240a5641a17c0ull, 0xab6139495f0d9c1ull});
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const m8 = s8;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x15e2ull};
            top[2] = m6;
            top[3] = m8;
            top[4] = m7;
            top[5] = m7;
            top += 5;
            MONAD_AOT_TAIL return b_18da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_15e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x83, 0x01, 0x90, 0x5f, 0x61, 0x85, 0x01}, 3, 4));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x83, 0x01, 0x90, 0x5f, 0x61, 0x85, 0x01}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = s2 + uint256_t{0x320ull};
            uint256_t const t2 = s2 + uint256_t{0x300ull};
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t1;
            top[1] = m0;
            top[2] = uint256_t{0x0ull};
            top[3] = t2;
            top += 3;
            MONAD_AOT_TAIL return b_15ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_15ef(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x82, 0x10, 0x61, 0x57}, 2, 2));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x82, 0x10, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::from_bool(s1 < uint256_t{0x1ull});
            bool const j5 = aot::nonzero(t1);
            if (j5) { MONAD_AOT_TAIL return b_1677<traits>(ctx, bottom, top, gas); }
            MONAD_AOT_TAIL return b_15f8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_15f8(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x50, 0x50, 0x50, 0x92, 0x85, 0x92, 0x61, 0x99, 0x9a, 0x95, 0x92, 0x61, 0x60, 0x98, 0x61, 0x97, 0x7f, 0x8d, 0x52, 0x7f, 0x86, 0x52, 0x8c, 0x8c, 0x61, 0x56}, 14, 4));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x50, 0x50, 0x50, 0x92, 0x85, 0x92, 0x61, 0x99, 0x9a, 0x95, 0x92, 0x61, 0x60, 0x98, 0x61, 0x97, 0x7f, 0x8d, 0x52, 0x7f, 0x86, 0x52, 0x8c, 0x8c, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, s11, uint256_t{0xfbc5a539efcf1381ull, 0x8e1fa771f4778595ull, 0x2cd4662a8cdde5d5ull, 0xeb7f86da11f7f0full});
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, uint256_t{0x5af040d25e76f99bull, 0x6ba906a76f2e51d3ull, 0x766feec7ee734b1bull, 0x29fc0dd0c7417d23ull});
            uint256_t const &s12 = top[-12];
            uint256_t const m12 = s12;
            uint256_t const &s13 = top[-13];
            uint256_t const m13 = s13;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            uint256_t const m7 = s7;
            uint256_t const &s6 = top[-6];
            uint256_t const m6 = s6;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const m11 = s11;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[-13] = m12;
            top[-12] = uint256_t{0x1008ull};
            top[-9] = uint256_t{0xa0ull};
            top[-8] = m13;
            top[-7] = uint256_t{0x166full};
            top[-6] = m9;
            top[-5] = m8;
            top[-4] = m7;
            top[-3] = m6;
            top[-2] = m5;
            top[-1] = uint256_t{0x165cull};
            top[0] = m9;
            top[1] = m4;
            top[2] = m11;
            top[3] = m10;
            top += 3;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_165c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x01, 0x35, 0x8a, 0x52, 0x01, 0x35, 0x90, 0x52, 0x86, 0x86, 0x61, 0x56}, 10, 2));
            if (MONAD_UNLIKELY(top - bottom < 10)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x01, 0x35, 0x8a, 0x52, 0x01, 0x35, 0x90, 0x52, 0x86, 0x86, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const t1 = s0 + uint256_t{0x220ull};
            uint256_t const t2 = aot::calldataload(ctx, t1);
            uint256_t const &s9 = top[-9];
            aot::mstore<traits>(ctx, gas, s9, t2);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = s0 + s1;
            uint256_t const t4 = aot::calldataload(ctx, t3);
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, s2, t4);
            uint256_t const m9 = s9;
            uint256_t const &s8 = top[-8];
            uint256_t const m8 = s8;
            top[-2] = m9;
            top[-1] = m8;
            top += -1;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_166f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x90, 0x80, 0x61, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x90, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-2] = t1;
            top[-1] = m2;
            top[0] = m2;
            MONAD_AOT_TAIL return b_18da<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1677(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x82, 0x88, 0x60, 0x92, 0x61, 0x8f, 0x8f, 0x8f, 0x91, 0x8a, 0x35, 0x81, 0x52, 0x60, 0x95, 0x86, 0x8c, 0x01, 0x35, 0x90, 0x52, 0x84, 0x35, 0x91, 0x61, 0x56}, 12, 10));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1014)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x82, 0x88, 0x60, 0x92, 0x61, 0x8f, 0x8f, 0x8f, 0x91, 0x8a, 0x35, 0x81, 0x52, 0x60, 0x95, 0x86, 0x8c, 0x01, 0x35, 0x90, 0x52, 0x84, 0x35, 0x91, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = aot::calldataload(ctx, s3);
            uint256_t const &s11 = top[-11];
            aot::mstore<traits>(ctx, gas, s11, t1);
            uint256_t const t2 = s3 + uint256_t{0x20ull};
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const &s7 = top[-7];
            aot::mstore<traits>(ctx, gas, s7, t3);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::calldataload(ctx, s0);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const m0 = s0;
            uint256_t const &s9 = top[-9];
            uint256_t const m9 = s9;
            uint256_t const m11 = s11;
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[0] = uint256_t{0x1ull};
            top[1] = m2;
            top[2] = uint256_t{0x20ull};
            top[3] = m0;
            top[4] = uint256_t{0x1698ull};
            top[5] = m9;
            top[6] = t4;
            top[7] = m11;
            top[8] = m10;
            top += 8;
            MONAD_AOT_TAIL return b_1981<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1698(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x94, 0x01, 0x91, 0x01, 0x90, 0x92, 0x61, 0x56}, 7, 0));
            if (MONAD_UNLIKELY(top - bottom < 7)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x94, 0x01, 0x91, 0x01, 0x90, 0x92, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const &s6 = top[-6];
            uint256_t const &s2 = top[-2];
            uint256_t const t2 = s6 + s2;
            uint256_t const &s4 = top[-4];
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s4 + s3;
            top[-6] = t2;
            top[-4] = t3;
            top[-3] = t1;
            top += -3;
            MONAD_AOT_TAIL return b_15ef<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_16a4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x90, 0x60, 0x51, 0x90, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x81, 0x60, 0x85, 0x01, 0x51, 0x94, 0x81, 0x80, 0x87, 0x81, 0x60, 0x85, 0x01, 0x51, 0x94, 0x81, 0x60, 0x82, 0x01, 0x51, 0x81, 0x8c, 0x81, 0x8a, 0x81, 0x87, 0x51, 0x9e, 0x8f, 0x98, 0x01, 0x51, 0x99, 0x81, 0x80, 0x84, 0x81, 0x8a, 0x81, 0x60, 0x81, 0x61, 0x8d, 0x01, 0x35, 0x93, 0x89, 0x09, 0x09, 0x08, 0x08, 0x97, 0x61, 0x82, 0x86, 0x81, 0x61, 0x8b, 0x01, 0x35, 0x81, 0x60, 0x81, 0x88, 0x8b, 0x09, 0x09, 0x08, 0x08, 0x97, 0x01, 0x35, 0x92, 0x09, 0x08, 0x08, 0x09, 0x09, 0x82, 0x03, 0x09, 0x08, 0x96, 0x81, 0x80, 0x80, 0x85, 0x81, 0x61, 0x8c, 0x01, 0x35, 0x81, 0x61, 0x8e, 0x01, 0x35, 0x88, 0x09, 0x08, 0x08, 0x94, 0x81, 0x61, 0x8b, 0x01, 0x35, 0x81, 0x61, 0x8d, 0x01, 0x35, 0x87, 0x09, 0x08, 0x08, 0x91, 0x61, 0x89, 0x01, 0x35, 0x09, 0x09, 0x09, 0x09, 0x90, 0x61, 0x56}, 1, 31));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 993)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x90, 0x60, 0x51, 0x90, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x81, 0x60, 0x85, 0x01, 0x51, 0x94, 0x81, 0x80, 0x87, 0x81, 0x60, 0x85, 0x01, 0x51, 0x94, 0x81, 0x60, 0x82, 0x01, 0x51, 0x81, 0x8c, 0x81, 0x8a, 0x81, 0x87, 0x51, 0x9e, 0x8f, 0x98, 0x01, 0x51, 0x99, 0x81, 0x80, 0x84, 0x81, 0x8a, 0x81, 0x60, 0x81, 0x61, 0x8d, 0x01, 0x35, 0x93, 0x89, 0x09, 0x09, 0x08, 0x08, 0x97, 0x61, 0x82, 0x86, 0x81, 0x61, 0x8b, 0x01, 0x35, 0x81, 0x60, 0x81, 0x88, 0x8b, 0x09, 0x09, 0x08, 0x08, 0x97, 0x01, 0x35, 0x92, 0x09, 0x08, 0x08, 0x09, 0x09, 0x82, 0x03, 0x09, 0x08, 0x96, 0x81, 0x80, 0x80, 0x85, 0x81, 0x61, 0x8c, 0x01, 0x35, 0x81, 0x61, 0x8e, 0x01, 0x35, 0x88, 0x09, 0x08, 0x08, 0x94, 0x81, 0x61, 0x8b, 0x01, 0x35, 0x81, 0x61, 0x8d, 0x01, 0x35, 0x87, 0x09, 0x08, 0x08, 0x91, 0x61, 0x89, 0x01, 0x35, 0x09, 0x09, 0x09, 0x09, 0x90, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k12_0 = uint256_t{0x0ull};
            uint256_t const k12_1 = uint256_t{0x1c0aull};
            uint256_t const k12_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k12_0, &k12_1, &k12_2);
            gas = ctx->gas_remaining;
            uint256_t const t3 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t2);
            uint256_t const t4 = t1 + uint256_t{0x20ull};
            uint256_t const t5 = aot::mload<traits>(ctx, gas, t4);
            uint256_t const t6 = t1 + uint256_t{0x40ull};
            uint256_t const t7 = aot::mload<traits>(ctx, gas, t6);
            uint256_t const t8 = t1 + uint256_t{0x60ull};
            uint256_t const t9 = aot::mload<traits>(ctx, gas, t8);
            uint256_t const t10 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t11 = t1 + uint256_t{0x80ull};
            uint256_t const t12 = aot::mload<traits>(ctx, gas, t11);
            uint256_t const &s0 = top[0];
            uint256_t const t13 = s0 + uint256_t{0x1c0ull};
            uint256_t const t14 = aot::calldataload(ctx, t13);
            uint256_t r65;
            runtime::mulmod(&r65, &t5, &t9, &t3);
            uint256_t const k66_1 = uint256_t{0x19ull};
            uint256_t r66;
            runtime::mulmod(&r66, &r65, &k66_1, &t3);
            uint256_t r67;
            runtime::addmod(&r67, &r66, &t14, &t3);
            uint256_t r68;
            runtime::addmod(&r68, &r67, &t7, &t3);
            uint256_t const t15 = s0 + uint256_t{0x1a0ull};
            uint256_t const t16 = aot::calldataload(ctx, t15);
            uint256_t r83;
            runtime::mulmod(&r83, &t5, &t9, &t3);
            uint256_t const k84_1 = uint256_t{0x5ull};
            uint256_t r84;
            runtime::mulmod(&r84, &r83, &k84_1, &t3);
            uint256_t r85;
            runtime::addmod(&r85, &r84, &t16, &t3);
            uint256_t r86;
            runtime::addmod(&r86, &r85, &t7, &t3);
            uint256_t const t17 = s0 + uint256_t{0x180ull};
            uint256_t const t18 = aot::calldataload(ctx, t17);
            uint256_t r91;
            runtime::mulmod(&r91, &t5, &t9, &t3);
            uint256_t r92;
            runtime::addmod(&r92, &r91, &t18, &t3);
            uint256_t r93;
            runtime::addmod(&r93, &r92, &t7, &t3);
            uint256_t r94;
            runtime::mulmod(&r94, &r93, &r86, &t3);
            uint256_t r95;
            runtime::mulmod(&r95, &r94, &r68, &t3);
            uint256_t const t19 = t3 - r95;
            uint256_t r98;
            runtime::mulmod(&r98, &t19, &t10, &t3);
            uint256_t r99;
            runtime::addmod(&r99, &r98, &t12, &t3);
            uint256_t const t20 = s0 + uint256_t{0x1a0ull};
            uint256_t const t21 = aot::calldataload(ctx, t20);
            uint256_t const t22 = s0 + uint256_t{0x200ull};
            uint256_t const t23 = aot::calldataload(ctx, t22);
            uint256_t r116;
            runtime::mulmod(&r116, &t5, &t23, &t3);
            uint256_t r117;
            runtime::addmod(&r117, &r116, &t21, &t3);
            uint256_t r118;
            runtime::addmod(&r118, &r117, &t7, &t3);
            uint256_t const t24 = s0 + uint256_t{0x180ull};
            uint256_t const t25 = aot::calldataload(ctx, t24);
            uint256_t const t26 = s0 + uint256_t{0x1e0ull};
            uint256_t const t27 = aot::calldataload(ctx, t26);
            uint256_t r131;
            runtime::mulmod(&r131, &t5, &t27, &t3);
            uint256_t r132;
            runtime::addmod(&r132, &r131, &t25, &t3);
            uint256_t r133;
            runtime::addmod(&r133, &r132, &t7, &t3);
            uint256_t const t28 = s0 + uint256_t{0x260ull};
            uint256_t const t29 = aot::calldataload(ctx, t28);
            uint256_t r139;
            runtime::mulmod(&r139, &t29, &t5, &t3);
            uint256_t r140;
            runtime::mulmod(&r140, &r139, &r133, &t3);
            uint256_t r141;
            runtime::mulmod(&r141, &r140, &r118, &t3);
            uint256_t r142;
            runtime::mulmod(&r142, &r141, &t10, &t3);
            uint256_t const m0 = s0;
            top[0] = uint256_t{0x1008ull};
            top[1] = r99;
            top[2] = r142;
            top[3] = m0;
            top += 3;
            MONAD_AOT_TAIL return b_1401<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1754(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x51, 0x61, 0x81, 0x01, 0x91, 0x60, 0x82, 0x01, 0x51, 0x60, 0x84, 0x52, 0x60, 0x61, 0x84, 0x01, 0x52, 0x60, 0x61, 0x84, 0x01, 0x52, 0x61, 0x83, 0x01, 0x52, 0x63, 0x61, 0x83, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x61, 0x83, 0x01, 0x52, 0x60, 0x83, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 1, 8));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1016)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x51, 0x61, 0x81, 0x01, 0x91, 0x60, 0x82, 0x01, 0x51, 0x60, 0x84, 0x52, 0x60, 0x61, 0x84, 0x01, 0x52, 0x60, 0x61, 0x84, 0x01, 0x52, 0x61, 0x83, 0x01, 0x52, 0x63, 0x61, 0x83, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x61, 0x83, 0x01, 0x52, 0x60, 0x83, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            uint256_t const t3 = t1 + uint256_t{0x60ull};
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x20ull});
            uint256_t const t5 = t1 + uint256_t{0x260ull};
            aot::mstore<traits>(ctx, gas, t5, uint256_t{0x20ull});
            uint256_t const t6 = t1 + uint256_t{0x280ull};
            aot::mstore<traits>(ctx, gas, t6, uint256_t{0x20ull});
            uint256_t const t7 = t1 + uint256_t{0x2a0ull};
            aot::mstore<traits>(ctx, gas, t7, t4);
            uint256_t const t8 = t1 + uint256_t{0x2c0ull};
            aot::mstore<traits>(ctx, gas, t8, uint256_t{0x2000002ull});
            uint256_t const t9 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k39_0 = uint256_t{0x0ull};
            uint256_t const k39_1 = uint256_t{0x1c0aull};
            uint256_t const k39_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k39_0, &k39_1, &k39_2);
            gas = ctx->gas_remaining;
            uint256_t const t10 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t9);
            uint256_t const t11 = t1 + uint256_t{0x2e0ull};
            aot::mstore<traits>(ctx, gas, t11, t10);
            uint256_t const t12 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k54_1 = uint256_t{0x5ull};
            uint256_t const k54_3 = uint256_t{0xc0ull};
            uint256_t const k54_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r54;
            runtime::staticcall<traits>(ctx, &r54, &t12, &k54_1, &t2, &k54_3, &t2, &k54_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(r54));
            bool const j57 = aot::nonzero(t13);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t2;
            top[1] = t1;
            top[2] = m0;
            top += 2;
            if (j57) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1827); }
            MONAD_AOT_TAIL return b_17ab<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_17ab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x82, 0x61, 0x91, 0x61, 0x82, 0x60, 0x80, 0x97, 0x51, 0x93, 0x61, 0x83, 0x60, 0x8a, 0x01, 0x96, 0x61, 0x82, 0x82, 0x61, 0x87, 0x01, 0x8b, 0x61, 0x56}, 3, 15));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1009)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x82, 0x61, 0x91, 0x61, 0x82, 0x60, 0x80, 0x97, 0x51, 0x93, 0x61, 0x83, 0x60, 0x8a, 0x01, 0x96, 0x61, 0x82, 0x82, 0x61, 0x87, 0x01, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s2 = top[-2];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const &s1 = top[-1];
            uint256_t const t2 = s1 + uint256_t{0xa0ull};
            uint256_t const &s0 = top[0];
            uint256_t const t3 = s0 + uint256_t{0x140ull};
            uint256_t const m2 = s2;
            uint256_t const m0 = s0;
            top[-2] = uint256_t{0xc0ull};
            top[0] = uint256_t{0x17feull};
            top[1] = m2;
            top[2] = t2;
            top[3] = uint256_t{0x17f1ull};
            top[4] = m2;
            top[5] = uint256_t{0xc0ull};
            top[6] = m0;
            top[7] = uint256_t{0x17e9ull};
            top[8] = m2;
            top[9] = t1;
            top[10] = uint256_t{0x17d2ull};
            top[11] = m2;
            top[12] = t1;
            top[13] = t3;
            top[14] = t2;
            top += 14;
            MONAD_AOT_TAIL return b_195d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17d2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x82, 0x61, 0x86, 0x01, 0x8a, 0x80, 0x61, 0x56}, 8, 6));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x82, 0x61, 0x86, 0x01, 0x8a, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x100ull};
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = uint256_t{0x17e2ull};
            top[2] = m1;
            top[3] = t1;
            top[4] = m7;
            top[5] = m7;
            top += 5;
            MONAD_AOT_TAIL return b_190c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17e2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x87, 0x80, 0x61, 0x56}, 8, 3));
            if (MONAD_UNLIKELY(top - bottom < 8)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x87, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s7 = top[-7];
            uint256_t const m7 = s7;
            top[1] = m7;
            top[2] = m7;
            top += 2;
            MONAD_AOT_TAIL return b_1939<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17e9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x83, 0x80, 0x61, 0x56}, 5, 2));
            if (MONAD_UNLIKELY(top - bottom < 5)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x83, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            top[-1] = t1;
            top[0] = m4;
            top[1] = m4;
            top += 1;
            MONAD_AOT_TAIL return b_190c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17f1(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x84, 0x01, 0x51, 0x90, 0x80, 0x61, 0x56}, 4, 3));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x84, 0x01, 0x51, 0x90, 0x80, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s3 = top[-3];
            uint256_t const t1 = s3 + uint256_t{0x1c0ull};
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[0] = t2;
            top[1] = m0;
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_1939<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_17fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x80, 0x51, 0x7f, 0x03, 0x90, 0x52, 0x56}, 3, 1));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x80, 0x51, 0x7f, 0x03, 0x90, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const t3 = uint256_t{0x3c208c16d87cfd47ull, 0x97816a916871ca8dull, 0xb85045b68181585dull, 0x30644e72e131a029ull} - t2;
            aot::mstore<traits>(ctx, gas, t1, t3);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top += -3;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_185b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x60, 0x83, 0x01, 0x51, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x80, 0x92, 0x81, 0x80, 0x93, 0x61, 0x82, 0x60, 0x8a, 0x01, 0x51, 0x92, 0x81, 0x61, 0x94, 0x81, 0x8d, 0x51, 0x93, 0x81, 0x8a, 0x81, 0x80, 0x86, 0x61, 0x84, 0x01, 0x35, 0x08, 0x95, 0x81, 0x80, 0x8d, 0x85, 0x01, 0x35, 0x81, 0x84, 0x81, 0x8a, 0x61, 0x8a, 0x01, 0x35, 0x09, 0x08, 0x08, 0x95, 0x61, 0x61, 0x86, 0x01, 0x35, 0x95, 0x01, 0x35, 0x09, 0x08, 0x08, 0x09, 0x09, 0x09, 0x91, 0x89, 0x01, 0x51, 0x93, 0x01, 0x35, 0x90, 0x09, 0x08, 0x60, 0x85, 0x01, 0x51, 0x82, 0x03, 0x90, 0x08, 0x90, 0x03, 0x91, 0x01, 0x52, 0x56}, 2, 27));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 997)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x60, 0x51, 0x91, 0x60, 0x83, 0x01, 0x51, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x80, 0x92, 0x81, 0x80, 0x93, 0x61, 0x82, 0x60, 0x8a, 0x01, 0x51, 0x92, 0x81, 0x61, 0x94, 0x81, 0x8d, 0x51, 0x93, 0x81, 0x8a, 0x81, 0x80, 0x86, 0x61, 0x84, 0x01, 0x35, 0x08, 0x95, 0x81, 0x80, 0x8d, 0x85, 0x01, 0x35, 0x81, 0x84, 0x81, 0x8a, 0x61, 0x8a, 0x01, 0x35, 0x09, 0x08, 0x08, 0x95, 0x61, 0x61, 0x86, 0x01, 0x35, 0x95, 0x01, 0x35, 0x09, 0x08, 0x08, 0x09, 0x09, 0x09, 0x91, 0x89, 0x01, 0x51, 0x93, 0x01, 0x35, 0x90, 0x09, 0x08, 0x60, 0x85, 0x01, 0x51, 0x82, 0x03, 0x90, 0x08, 0x90, 0x03, 0x91, 0x01, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k15_0 = uint256_t{0x0ull};
            uint256_t const k15_1 = uint256_t{0x1c0aull};
            uint256_t const k15_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k15_0, &k15_1, &k15_2);
            gas = ctx->gas_remaining;
            uint256_t const t5 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t4);
            uint256_t const t6 = t1 + uint256_t{0x40ull};
            uint256_t const t7 = aot::mload<traits>(ctx, gas, t6);
            uint256_t const t8 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s0 = top[0];
            uint256_t const t9 = s0 + uint256_t{0x1c0ull};
            uint256_t const t10 = aot::calldataload(ctx, t9);
            uint256_t r48;
            runtime::addmod(&r48, &t10, &t7, &t5);
            uint256_t const t11 = s0 + uint256_t{0x1a0ull};
            uint256_t const t12 = aot::calldataload(ctx, t11);
            uint256_t const t13 = s0 + uint256_t{0x200ull};
            uint256_t const t14 = aot::calldataload(ctx, t13);
            uint256_t r64;
            runtime::mulmod(&r64, &t14, &t3, &t5);
            uint256_t r65;
            runtime::addmod(&r65, &r64, &t7, &t5);
            uint256_t r66;
            runtime::addmod(&r66, &r65, &t12, &t5);
            uint256_t const t15 = s0 + uint256_t{0x180ull};
            uint256_t const t16 = aot::calldataload(ctx, t15);
            uint256_t const t17 = s0 + uint256_t{0x1e0ull};
            uint256_t const t18 = aot::calldataload(ctx, t17);
            uint256_t r76;
            runtime::mulmod(&r76, &t18, &t3, &t5);
            uint256_t r77;
            runtime::addmod(&r77, &r76, &t7, &t5);
            uint256_t r78;
            runtime::addmod(&r78, &r77, &t16, &t5);
            uint256_t r79;
            runtime::mulmod(&r79, &r78, &r66, &t5);
            uint256_t r80;
            runtime::mulmod(&r80, &r79, &r48, &t5);
            uint256_t r81;
            runtime::mulmod(&r81, &r80, &t8, &t5);
            uint256_t const t19 = t1 + uint256_t{0x1a0ull};
            uint256_t const t20 = aot::mload<traits>(ctx, gas, t19);
            uint256_t const t21 = s0 + uint256_t{0x260ull};
            uint256_t const t22 = aot::calldataload(ctx, t21);
            uint256_t r90;
            runtime::mulmod(&r90, &r81, &t22, &t5);
            uint256_t r91;
            runtime::addmod(&r91, &r90, &t20, &t5);
            uint256_t const t23 = t1 + uint256_t{0x80ull};
            uint256_t const t24 = aot::mload<traits>(ctx, gas, t23);
            uint256_t const t25 = t5 - t24;
            uint256_t r99;
            runtime::addmod(&r99, &r91, &t25, &t5);
            uint256_t const t26 = t5 - r99;
            uint256_t const t27 = t1 + uint256_t{0x120ull};
            aot::mstore<traits>(ctx, gas, t27, t26);
            uint256_t const &s1 = top[-1];
            uint64_t const jt = aot::jump_offset(s1);
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_18da(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x92, 0x60, 0x60, 0x94, 0x81, 0x60, 0x94, 0x80, 0x51, 0x85, 0x52, 0x01, 0x51, 0x82, 0x84, 0x01, 0x52, 0x80, 0x51, 0x86, 0x84, 0x01, 0x52, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x92, 0x60, 0x60, 0x94, 0x81, 0x60, 0x94, 0x80, 0x51, 0x85, 0x52, 0x01, 0x51, 0x82, 0x84, 0x01, 0x52, 0x80, 0x51, 0x86, 0x84, 0x01, 0x52, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = aot::mload<traits>(ctx, gas, s2);
            uint256_t const t6 = s3 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = s2 + uint256_t{0x20ull};
            uint256_t const t8 = aot::mload<traits>(ctx, gas, t7);
            uint256_t const t9 = s3 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k33_1 = uint256_t{0x6ull};
            uint256_t const k33_3 = uint256_t{0x80ull};
            uint256_t const &s0 = top[0];
            uint256_t const k33_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r33;
            runtime::staticcall<traits>(ctx, &r33, &t10, &k33_1, &s3, &k33_3, &s0, &k33_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(r33));
            bool const j36 = aot::nonzero(t11);
            top += -4;
            if (j36) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1907); }
            MONAD_AOT_TAIL return b_1906<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1906(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_190c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x92, 0x60, 0x60, 0x94, 0x81, 0x60, 0x94, 0x80, 0x51, 0x85, 0x52, 0x01, 0x51, 0x82, 0x84, 0x01, 0x52, 0x80, 0x35, 0x86, 0x84, 0x01, 0x52, 0x01, 0x35, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 4, 6));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x92, 0x60, 0x60, 0x94, 0x81, 0x60, 0x94, 0x80, 0x51, 0x85, 0x52, 0x01, 0x51, 0x82, 0x84, 0x01, 0x52, 0x80, 0x35, 0x86, 0x84, 0x01, 0x52, 0x01, 0x35, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const t5 = aot::calldataload(ctx, s2);
            uint256_t const t6 = s3 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t6, t5);
            uint256_t const t7 = s2 + uint256_t{0x20ull};
            uint256_t const t8 = aot::calldataload(ctx, t7);
            uint256_t const t9 = s3 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t9, t8);
            uint256_t const t10 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k33_1 = uint256_t{0x6ull};
            uint256_t const k33_3 = uint256_t{0x80ull};
            uint256_t const &s0 = top[0];
            uint256_t const k33_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r33;
            runtime::staticcall<traits>(ctx, &r33, &t10, &k33_1, &s3, &k33_3, &s0, &k33_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t11 = aot::from_bool(!aot::nonzero(r33));
            bool const j36 = aot::nonzero(t11);
            top += -4;
            if (j36) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1907); }
            MONAD_AOT_TAIL return b_1938<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1938(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1939(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x92, 0x60, 0x93, 0x60, 0x60, 0x93, 0x80, 0x51, 0x84, 0x52, 0x01, 0x51, 0x60, 0x83, 0x01, 0x52, 0x84, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x92, 0x60, 0x93, 0x60, 0x60, 0x93, 0x80, 0x51, 0x84, 0x52, 0x01, 0x51, 0x60, 0x83, 0x01, 0x52, 0x84, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s3 + uint256_t{0x40ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t5, s2);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k24_1 = uint256_t{0x7ull};
            uint256_t const k24_3 = uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            uint256_t const k24_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r24;
            runtime::staticcall<traits>(ctx, &r24, &t6, &k24_1, &s3, &k24_3, &s0, &k24_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(r24));
            bool const j27 = aot::nonzero(t7);
            top += -4;
            if (j27) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1907); }
            MONAD_AOT_TAIL return b_195c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_195c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_195d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x92, 0x60, 0x93, 0x60, 0x60, 0x93, 0x80, 0x35, 0x84, 0x52, 0x01, 0x35, 0x60, 0x83, 0x01, 0x52, 0x84, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x92, 0x60, 0x93, 0x60, 0x60, 0x93, 0x80, 0x35, 0x84, 0x52, 0x01, 0x35, 0x60, 0x83, 0x01, 0x52, 0x84, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s3 + uint256_t{0x40ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t5, s2);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k24_1 = uint256_t{0x7ull};
            uint256_t const k24_3 = uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            uint256_t const k24_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r24;
            runtime::staticcall<traits>(ctx, &r24, &t6, &k24_1, &s3, &k24_3, &s0, &k24_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t7 = aot::from_bool(!aot::nonzero(r24));
            bool const j27 = aot::nonzero(t7);
            top += -4;
            if (j27) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1907); }
            MONAD_AOT_TAIL return b_1980<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1980(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline]] void b_1981(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x92, 0x93, 0x60, 0x60, 0x92, 0x80, 0x51, 0x83, 0x52, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x83, 0x81, 0x01, 0x94, 0x85, 0x52, 0x83, 0x81, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x92, 0x93, 0x60, 0x60, 0x92, 0x80, 0x51, 0x83, 0x52, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x83, 0x81, 0x01, 0x94, 0x85, 0x52, 0x83, 0x81, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::mload<traits>(ctx, gas, t2);
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s3 + uint256_t{0x40ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t5, s2);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k30_1 = uint256_t{0x7ull};
            uint256_t const k30_3 = uint256_t{0x60ull};
            uint256_t const k30_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r30;
            runtime::staticcall<traits>(ctx, &r30, &t6, &k30_1, &s3, &k30_3, &s3, &k30_5, (aot::gas_of<traits>({0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const &s0 = top[0];
            uint256_t const t7 = aot::mload<traits>(ctx, gas, s0);
            aot::mstore<traits>(ctx, gas, t5, t7);
            uint256_t const t8 = s0 + uint256_t{0x20ull};
            uint256_t const t9 = aot::mload<traits>(ctx, gas, t8);
            uint256_t const t10 = s3 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t10, t9);
            uint256_t const t11 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x16, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k46_1 = uint256_t{0x6ull};
            uint256_t const k46_3 = uint256_t{0x80ull};
            uint256_t const k46_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r46;
            runtime::staticcall<traits>(ctx, &r46, &t11, &k46_1, &s3, &k46_3, &s0, &k46_5, (aot::gas_of<traits>({0x16, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t12 = r46 & r30;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j50 = aot::nonzero(t13);
            top += -4;
            if (j50) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1907); }
            MONAD_AOT_TAIL return b_19bf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19bf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_19c0(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x90, 0x60, 0x92, 0x93, 0x60, 0x60, 0x92, 0x80, 0x35, 0x83, 0x52, 0x01, 0x35, 0x60, 0x82, 0x01, 0x52, 0x83, 0x81, 0x01, 0x94, 0x85, 0x52, 0x83, 0x81, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}, 4, 7));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1017)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x90, 0x60, 0x92, 0x93, 0x60, 0x60, 0x92, 0x80, 0x35, 0x83, 0x52, 0x01, 0x35, 0x60, 0x82, 0x01, 0x52, 0x83, 0x81, 0x01, 0x94, 0x85, 0x52, 0x83, 0x81, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::calldataload(ctx, s1);
            uint256_t const &s3 = top[-3];
            aot::mstore<traits>(ctx, gas, s3, t1);
            uint256_t const t2 = s1 + uint256_t{0x20ull};
            uint256_t const t3 = aot::calldataload(ctx, t2);
            uint256_t const t4 = s3 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t4, t3);
            uint256_t const t5 = s3 + uint256_t{0x40ull};
            uint256_t const &s2 = top[-2];
            aot::mstore<traits>(ctx, gas, t5, s2);
            uint256_t const t6 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k30_1 = uint256_t{0x7ull};
            uint256_t const k30_3 = uint256_t{0x60ull};
            uint256_t const k30_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r30;
            runtime::staticcall<traits>(ctx, &r30, &t6, &k30_1, &s3, &k30_3, &s3, &k30_5, (aot::gas_of<traits>({0x94, 0x83, 0x51, 0x90, 0x52, 0x60, 0x83, 0x01, 0x51, 0x60, 0x82, 0x01, 0x52, 0x60, 0x5a, 0xfa, 0x16, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const &s0 = top[0];
            uint256_t const t7 = aot::mload<traits>(ctx, gas, s0);
            aot::mstore<traits>(ctx, gas, t5, t7);
            uint256_t const t8 = s0 + uint256_t{0x20ull};
            uint256_t const t9 = aot::mload<traits>(ctx, gas, t8);
            uint256_t const t10 = s3 + uint256_t{0x60ull};
            aot::mstore<traits>(ctx, gas, t10, t9);
            uint256_t const t11 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x16, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k46_1 = uint256_t{0x6ull};
            uint256_t const k46_3 = uint256_t{0x80ull};
            uint256_t const k46_5 = uint256_t{0x40ull};
            ctx->gas_remaining = gas;
            uint256_t r46;
            runtime::staticcall<traits>(ctx, &r46, &t11, &k46_1, &s3, &k46_3, &s0, &k46_5, (aot::gas_of<traits>({0x16, 0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t12 = r46 & r30;
            uint256_t const t13 = aot::from_bool(!aot::nonzero(t12));
            bool const j50 = aot::nonzero(t13);
            top += -4;
            if (j50) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1907); }
            MONAD_AOT_TAIL return b_19fe<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_19fe(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x56}, 1, 0));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint64_t const jt = aot::jump_offset(s0);
            top += -1;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_19ff(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x90, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x91, 0x82, 0x91, 0x35, 0x09, 0x82, 0x51, 0x08, 0x90, 0x52, 0x56}, 4, 5));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1019)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x90, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x91, 0x82, 0x91, 0x35, 0x09, 0x82, 0x51, 0x08, 0x90, 0x52, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k9_0 = uint256_t{0x0ull};
            uint256_t const k9_1 = uint256_t{0x1c0aull};
            uint256_t const k9_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k9_0, &k9_1, &k9_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s1 = top[-1];
            uint256_t const t3 = aot::calldataload(ctx, s1);
            uint256_t const &s2 = top[-2];
            uint256_t r18;
            runtime::mulmod(&r18, &t3, &s2, &t2);
            uint256_t const &s0 = top[0];
            uint256_t const t4 = aot::mload<traits>(ctx, gas, s0);
            uint256_t r21;
            runtime::addmod(&r21, &t4, &r18, &t2);
            aot::mstore<traits>(ctx, gas, s0, r21);
            uint256_t const &s3 = top[-3];
            uint64_t const jt = aot::jump_offset(s3);
            top += -4;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a1b(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x81, 0x83, 0x52, 0x81, 0x80, 0x84, 0x01, 0x52, 0x81, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x83, 0x01, 0x52, 0x80, 0x82, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x81, 0x83, 0x52, 0x81, 0x80, 0x84, 0x01, 0x52, 0x81, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x7f, 0x60, 0x83, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x83, 0x01, 0x52, 0x80, 0x82, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x20ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x20ull});
            uint256_t const t2 = s1 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x20ull});
            uint256_t const t3 = s1 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x43e1f593efffffffull, 0x2833e84879b97091ull, 0xb85045b68181585dull, 0x30644e72e131a029ull});
            uint256_t const t5 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k31_0 = uint256_t{0x0ull};
            uint256_t const k31_1 = uint256_t{0x1c0aull};
            uint256_t const k31_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k31_0, &k31_1, &k31_2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t5);
            uint256_t const t7 = s1 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k46_1 = uint256_t{0x5ull};
            uint256_t const k46_3 = uint256_t{0xc0ull};
            uint256_t const k46_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r46;
            runtime::staticcall<traits>(ctx, &r46, &t8, &k46_1, &s1, &k46_3, &s1, &k46_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r46));
            bool const j49 = aot::nonzero(t9);
            top[0] = uint256_t{0x20ull};
            if (j49) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbd1); }
            MONAD_AOT_TAIL return b_1a79<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1a79(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x51, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x51, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1a7d(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x60, 0x90, 0x81, 0x83, 0x52, 0x81, 0x80, 0x84, 0x01, 0x52, 0x81, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x63, 0x60, 0x83, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x83, 0x01, 0x52, 0x80, 0x82, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}, 2, 6));
            if (MONAD_UNLIKELY(top - bottom < 2)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1018)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x60, 0x90, 0x81, 0x83, 0x52, 0x81, 0x80, 0x84, 0x01, 0x52, 0x81, 0x60, 0x84, 0x01, 0x52, 0x60, 0x83, 0x01, 0x52, 0x63, 0x60, 0x83, 0x01, 0x52, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x60, 0x83, 0x01, 0x52, 0x80, 0x82, 0x60, 0x81, 0x60, 0x5a, 0xfa, 0x15, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            aot::mstore<traits>(ctx, gas, s1, uint256_t{0x20ull});
            uint256_t const t1 = s1 + uint256_t{0x20ull};
            aot::mstore<traits>(ctx, gas, t1, uint256_t{0x20ull});
            uint256_t const t2 = s1 + uint256_t{0x40ull};
            aot::mstore<traits>(ctx, gas, t2, uint256_t{0x20ull});
            uint256_t const t3 = s1 + uint256_t{0x60ull};
            uint256_t const &s0 = top[0];
            aot::mstore<traits>(ctx, gas, t3, s0);
            uint256_t const t4 = s1 + uint256_t{0x80ull};
            aot::mstore<traits>(ctx, gas, t4, uint256_t{0x2000000ull});
            uint256_t const t5 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k31_0 = uint256_t{0x0ull};
            uint256_t const k31_1 = uint256_t{0x1c0aull};
            uint256_t const k31_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k31_0, &k31_1, &k31_2);
            gas = ctx->gas_remaining;
            uint256_t const t6 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t5);
            uint256_t const t7 = s1 + uint256_t{0xa0ull};
            aot::mstore<traits>(ctx, gas, t7, t6);
            uint256_t const t8 = uint256_t{static_cast<uint64_t>(gas + (aot::gas_of<traits>({0xfa, 0x15, 0x61, 0x57}) + 0))};
            uint256_t const k46_1 = uint256_t{0x5ull};
            uint256_t const k46_3 = uint256_t{0xc0ull};
            uint256_t const k46_5 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            uint256_t r46;
            runtime::staticcall<traits>(ctx, &r46, &t8, &k46_1, &s1, &k46_3, &s1, &k46_5, (aot::gas_of<traits>({0x15, 0x61, 0x57}) + 0));
            gas = ctx->gas_remaining;
            uint256_t const t9 = aot::from_bool(!aot::nonzero(r46));
            bool const j49 = aot::nonzero(t9);
            top[0] = uint256_t{0x20ull};
            if (j49) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0xbd1); }
            MONAD_AOT_TAIL return b_1abf<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1abf(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x50, 0x51, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x50, 0x51, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = aot::mload<traits>(ctx, gas, s1);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t1;
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1ac3(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x91, 0x92, 0x90, 0x60, 0x51, 0x93, 0x61, 0x85, 0x01, 0x91, 0x60, 0x84, 0x03, 0x61, 0x57}, 4, 4));
            if (MONAD_UNLIKELY(top - bottom < 4)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1020)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x91, 0x92, 0x90, 0x60, 0x51, 0x93, 0x61, 0x85, 0x01, 0x91, 0x60, 0x84, 0x03, 0x61, 0x57}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 64u, 96u, 9>(ctx, gas);
            uint256_t const t2 = t1 + uint256_t{0x240ull};
            uint256_t const &s3 = top[-3];
            uint256_t const t3 = s3 - uint256_t{0x1ull};
            bool const j15 = aot::nonzero(t3);
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            top[-3] = t1;
            top[-2] = m0;
            top[-1] = m3;
            top[0] = t2;
            top[1] = m2;
            top[2] = m1;
            top += 2;
            if (j15) { MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, 0x1bc7); }
            MONAD_AOT_TAIL return b_1ad9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::always_inline]] inline void b_1ad9(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x92, 0x61, 0x83, 0x61, 0x87, 0x95, 0x84, 0x86, 0x61, 0x61, 0x61, 0x61, 0x61, 0x9f, 0x9e, 0x9b, 0x86, 0x61, 0x9f, 0x9d, 0x61, 0x60, 0x9f, 0x61, 0x85, 0x85, 0x61, 0x56}, 6, 19));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1005)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x92, 0x61, 0x83, 0x61, 0x87, 0x95, 0x84, 0x86, 0x61, 0x61, 0x61, 0x61, 0x61, 0x9f, 0x9e, 0x9b, 0x86, 0x61, 0x9f, 0x9d, 0x61, 0x60, 0x9f, 0x61, 0x85, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            uint256_t const &s4 = top[-4];
            uint256_t const m4 = s4;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            uint256_t const &s1 = top[-1];
            uint256_t const m1 = s1;
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[-5] = uint256_t{0x200ull};
            top[-4] = m5;
            top[-3] = uint256_t{0x1bc2ull};
            top[-2] = m4;
            top[-1] = uint256_t{0x60ull};
            top[0] = m3;
            top[1] = uint256_t{0x1b81ull};
            top[2] = m2;
            top[3] = uint256_t{0x1b7aull};
            top[4] = m2;
            top[5] = m3;
            top[6] = m1;
            top[7] = uint256_t{0x1b30ull};
            top[8] = uint256_t{0x1b2aull};
            top[9] = uint256_t{0x1b24ull};
            top[10] = uint256_t{0x1b1full};
            top[11] = m1;
            top[12] = m3;
            top[13] = m4;
            top[14] = uint256_t{0x1b11ull};
            top[15] = m0;
            top[16] = uint256_t{0x1b0cull};
            top[17] = m1;
            top[18] = m3;
            top += 18;
            MONAD_AOT_TAIL return b_23f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b0c(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_2c8<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b11(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1b1aull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_316<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b1a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_3b1<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b1f(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_6ce<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b24(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8b, 0x61, 0x56}, 12, 2));
            if (MONAD_UNLIKELY(top - bottom < 12)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s11 = top[-11];
            uint256_t const m11 = s11;
            top[1] = m11;
            top += 1;
            MONAD_AOT_TAIL return b_712<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b2a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8a, 0x61, 0x56}, 11, 2));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8a, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s10 = top[-10];
            uint256_t const m10 = s10;
            top[1] = m10;
            top += 1;
            MONAD_AOT_TAIL return b_76c<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b30(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x8a, 0x7f, 0x61, 0x85, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x9b, 0x8c, 0x94, 0x01, 0x51, 0x61, 0x56}, 11, 9));
            if (MONAD_UNLIKELY(top - bottom < 11)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1015)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x8a, 0x7f, 0x61, 0x85, 0x5f, 0x80, 0x51, 0x60, 0x61, 0x83, 0x39, 0x81, 0x51, 0x91, 0x52, 0x9b, 0x8c, 0x94, 0x01, 0x51, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const t1 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            uint256_t const k11_0 = uint256_t{0x0ull};
            uint256_t const k11_1 = uint256_t{0x1c0aull};
            uint256_t const k11_2 = uint256_t{0x20ull};
            ctx->gas_remaining = gas;
            runtime::codecopy<traits>(ctx, &k11_0, &k11_1, &k11_2);
            gas = ctx->gas_remaining;
            uint256_t const t2 = aot::mload_c<traits, 0u, 32u, 3>(ctx, gas);
            aot::mstore_c<traits, 0u, 32u, 3>(ctx, gas, t1);
            uint256_t const &s10 = top[-10];
            uint256_t const &s7 = top[-7];
            uint256_t const t3 = s10 + s7;
            uint256_t const t4 = aot::mload<traits>(ctx, gas, t3);
            uint256_t const &s2 = top[-2];
            uint256_t const m2 = s2;
            top[-7] = t2;
            top[1] = t2;
            top[2] = uint256_t{0x43e1f593f0000000ull, 0x2833e84879b97091ull, 0xb85045b68181585dull, 0x30644e72e131a029ull};
            top[3] = uint256_t{0x1b6eull};
            top[4] = m2;
            top[5] = t4;
            top += 5;
            MONAD_AOT_TAIL return b_1a7d<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b6e(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x08, 0x61, 0x8c, 0x01, 0x52, 0x61, 0x56}, 14, 0));
            if (MONAD_UNLIKELY(top - bottom < 14)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x08, 0x61, 0x8c, 0x01, 0x52, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::addmod(&r1, &s0, &s1, &s2);
            uint256_t const &s13 = top[-13];
            uint256_t const t1 = s13 + uint256_t{0x1c0ull};
            aot::mstore<traits>(ctx, gas, t1, r1);
            top += -3;
            MONAD_AOT_TAIL return b_7b9<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b7a(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x92, 0x85, 0x61, 0x56}, 6, 2));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1022)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x92, 0x85, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            uint256_t const &s3 = top[-3];
            uint256_t const m3 = s3;
            uint256_t const &s5 = top[-5];
            uint256_t const m5 = s5;
            top[-3] = m0;
            top[0] = m3;
            top[1] = m5;
            top += 1;
            MONAD_AOT_TAIL return b_975<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b81(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x08, 0x61, 0x84, 0x01, 0x52, 0x61, 0x61, 0x56}, 6, 0));
            if (MONAD_UNLIKELY(top - bottom < 6)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x08, 0x61, 0x84, 0x01, 0x52, 0x61, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const &s2 = top[-2];
            uint256_t r1;
            runtime::addmod(&r1, &s0, &s1, &s2);
            uint256_t const &s5 = top[-5];
            uint256_t const t1 = s5 + uint256_t{0x1a0ull};
            aot::mstore<traits>(ctx, gas, t1, r1);
            top[-2] = uint256_t{0x1b90ull};
            top += -2;
            MONAD_AOT_TAIL return b_c05<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b90(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1b99ull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_185b<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1b99(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1ba2ull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_1754<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1ba2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1babull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_16a4<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bab(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1bb4ull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_124f<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bb4(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}, 1, 3));
            if (MONAD_UNLIKELY(top - bottom < 1)) { ctx->exit(StatusCode::Error); }
            if (MONAD_UNLIKELY(top - bottom > 1021)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x81, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const m0 = s0;
            top[1] = uint256_t{0x1bbdull};
            top[2] = m0;
            top += 2;
            MONAD_AOT_TAIL return b_1070<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bbd(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x61, 0x56}, 0, 1));
            if (MONAD_UNLIKELY(top - bottom > 1023)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x61, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            MONAD_AOT_TAIL return b_c84<traits>(ctx, bottom, top, gas);
        }

        template <Traits traits>
        [[gnu::noinline, gnu::optimize("Os")]] void b_1bc2(Context *const ctx, uint256_t const *const bottom, uint256_t *top, int64_t gas)
        {
            static_assert(aot::stack_bounds_are<traits>({0x5b, 0x01, 0x51, 0x90, 0x56}, 3, 0));
            if (MONAD_UNLIKELY(top - bottom < 3)) { ctx->exit(StatusCode::Error); }
            gas -= aot::gas_of<traits>({0x5b, 0x01, 0x51, 0x90, 0x56}) + 0;
            if (MONAD_UNLIKELY(gas < 0)) { ctx->exit(StatusCode::OutOfGas); }
            uint256_t const &s0 = top[0];
            uint256_t const &s1 = top[-1];
            uint256_t const t1 = s0 + s1;
            uint256_t const t2 = aot::mload<traits>(ctx, gas, t1);
            uint256_t const &s2 = top[-2];
            uint64_t const jt = aot::jump_offset(s2);
            top[-2] = t2;
            top += -2;
            if (MONAD_LIKELY(jt < 7263)) {
                Block<traits> const f = jump_table<traits>[jt];
                if (MONAD_LIKELY(f != nullptr)) {
                    MONAD_AOT_TAIL return f(ctx, bottom, top, gas);
                }
                MONAD_AOT_TAIL return interpreter::resume<traits>(*ctx, bottom, top, gas, jt);
            }
            ctx->exit(StatusCode::Error);
        }

        template <Traits traits>
        void run(
            void *, Context *const ctx, interpreter::Intercode const *,
            uint256_t *const stack_ptr, void *)
        {
            b_0<traits>(ctx, stack_ptr - 1, stack_ptr - 1, ctx->gas_remaining);
        }
    }

    template void c_fd47ed62af960c20::run<EvmTraits<MONAD_ETH_OSAKA>>(
        void *, Context *, interpreter::Intercode const *, uint256_t *, void *);
}
